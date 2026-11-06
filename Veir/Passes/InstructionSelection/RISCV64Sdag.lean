module

public import Veir.Pass
public import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Passes.InstructionSelection.Common

namespace Veir

/-!
  This file replicates instruction selection patterns from LLVM's SelectionDAG instruction selector,
  to lower LLVM IR to RISC-V assembly (64 bits).
-/

/-! # SelectionDAG Lowering Patterns  -/

/-! ## Division by a constant power of two

  RISC-V has no divide-by-constant strength reduction in hardware, so a `udiv`/`sdiv`
  by a constant power of two is turned into shifts here. This mirrors the
  target-independent `DAGCombiner::visitUDIVLike` / `DAGCombiner::visitSDIVLike`:
  RISC-V does not override this generic lowering with something target-specific
  unless the `short-forward-branch-ialu` tuning feature is set (in which case
  `RISCVTargetLowering::BuildSDIVPow2` instead emits a branchy `cmov` form), which we
  do not model, so the sequences below are what a plain `-mtriple=riscv64` emits.
  https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L5270-L5285
-/

/-- The `w`-bit unsigned magnitude of `v`, i.e. `v`'s bit pattern reduced mod `2^w`.
    Needed because a `udiv` divisor whose top bit is set is decoded as a negative
    `Int` (integer attributes carry no signedness), even though `udiv` treats the
    bit pattern as unsigned. -/
def unsignedMod (w : Nat) (v : Int) : Nat := (v % ((2 : Int) ^ w)).toNat

/-- If `m` is a nonzero power of two, return its base-2 logarithm. -/
def log2IfPow2 (m : Nat) : Option Nat :=
  if m == 0 || (m &&& (m - 1)) != 0 then none else some (Nat.log2 m)

/-- If `|v|` is a nonzero power of two, return its base-2 logarithm together with
    whether `v` is negative. Used for `sdiv`, whose divisor is signed, so `v` (as
    decoded) already carries the correct sign. Mirrors `isDivisorPowerOfTwo`.
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L5270-L5285 -/
def matchSignedPow2Divisor (w : Nat) (v : Int) : Option (Nat × Bool) := do
  let s := (BitVec.ofInt w v).toInt
  let k ← log2IfPow2 s.natAbs
  return (k, decide (s < 0))

/-- If the `w`-bit unsigned magnitude of `v` is a nonzero power of two, return its
    base-2 logarithm. Used for `udiv`. -/
def matchUnsignedPow2Divisor (w : Nat) (v : Int) : Option Nat :=
  log2IfPow2 (unsignedMod w v)

/-- `udiv x, 2^k` -> `OP x, k`, where `OP` is `riscv.srli` (`width = 64`) or
    `riscv.srliw` (`width = 32`, the `i32` analogue). Mirrors
    `DAGCombiner::visitUDIVLike`'s `fold (udiv x, (1 << c)) -> x >>u c` (via
    `BuildLogBase2`).
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L5430-L5440 -/
def udivPow2GenLocal (dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties)
    (width : Nat) (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchUdiv op ctx.raw | return (ctx, none)
  let .integerType t := ((op.getResult 0).getType! ctx.raw).val | return (ctx, none)
  if t.bitwidth ≠ width then return (ctx, none)
  let some imm := matchConstantIntVal rhs ctx.raw | return (ctx, none)
  let some k := matchUnsignedPow2Divisor width imm | return (ctx, none)
  let (ctx, xCastOp) ← castToRegLocal ctx lhs
  let shamt := RISCVImmediateProperties.mk (BitVec.ofInt 64 k)
  let (ctx, shiftOp) ← WfRewriter.createOp! ctx dst #[RegisterType.mk] #[xCastOp.getResult 0]
      #[] #[] (cast h.symm shamt) none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (shiftOp.getResult 0)
  some (ctx, some (#[xCastOp, shiftOp, castBackOp], #[castBackOp.getResult 0]))

def udivPow2 := RewritePattern.fromLocalRewrite (udivPow2GenLocal .srli rfl 64)
def udivwPow2 := RewritePattern.fromLocalRewrite (udivPow2GenLocal .srliw rfl 32)

/-- `riscv.sub 0, x` (`riscv.subw` at `i32`, selected via `negDst`): negates `x`.
    Used to correct the quotient of a `sdiv`-by-power-of-two lowering when the
    divisor is negative. Returns the created operations (in insertion order) along
    with the negation op, whose result the caller uses. -/
def negateRegLocal (negDst : Riscv) (h : Riscv.propertiesOf negDst = Unit)
    (ctx : WfIRContext OpCode) (x : ValuePtr) :
    Option (WfIRContext OpCode × Array OperationPtr × OperationPtr) := do
  let zero := RISCVImmediateProperties.mk 0#64
  let (ctx, zeroOp) ← WfRewriter.createOp! ctx Riscv.li #[RegisterType.mk] #[]
      #[] #[] zero none
  let (ctx, negOp) ← WfRewriter.createOp! ctx negDst #[RegisterType.mk] #[zeroOp.getResult 0, x]
      #[] #[] (cast h.symm ()) none
  some (ctx, #[zeroOp, negOp], negOp)

/-- `sdiv exact x, 2^k` -> `dst x, k` (`dst` = `riscv.srai`/`riscv.sraiw`); when the
    divisor is negative, negate the shifted result via `negDst`
    (`riscv.sub`/`riscv.subw`): `sdiv exact x, -2^k` -> `negDst 0, (dst x, k)`.
    Mirrors `TargetLowering::BuildExactSDIV` (a plain arithmetic shift by the
    trailing-zero count, times a ±1 "magic factor" that the surrounding combines
    fold into a no-op or a negation). `DAGCombiner::visitSDIVLike` takes this path
    instead of the general correction sequence below whenever the `exact` flag is
    set, since it is cheaper.
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L5294-L5301
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/TargetLowering.cpp#L6454-L6510 -/
def sdivPow2ExactGenLocal (dst : Riscv) (hDst : Riscv.propertiesOf dst = RISCVImmediateProperties)
    (negDst : Riscv) (hNeg : Riscv.propertiesOf negDst = Unit) (width : Nat)
    (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, props) := matchSdiv op ctx.raw | return (ctx, none)
  if ¬ props.exact then return (ctx, none)
  let .integerType t := ((op.getResult 0).getType! ctx.raw).val | return (ctx, none)
  if t.bitwidth ≠ width then return (ctx, none)
  let some imm := matchConstantIntVal rhs ctx.raw | return (ctx, none)
  let some (k, isNeg) := matchSignedPow2Divisor width imm | return (ctx, none)
  let (ctx, xCastOp) ← castToRegLocal ctx lhs
  let shamt := RISCVImmediateProperties.mk (BitVec.ofInt 64 k)
  let (ctx, sraOp) ← WfRewriter.createOp! ctx dst #[RegisterType.mk] #[xCastOp.getResult 0]
      #[] #[] (cast hDst.symm shamt) none
  if ¬ isNeg then
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (sraOp.getResult 0)
    some (ctx, some (#[xCastOp, sraOp, castBackOp], #[castBackOp.getResult 0]))
  else
    let (ctx, negOps, negOp) ← negateRegLocal negDst hNeg ctx (sraOp.getResult 0)
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (negOp.getResult 0)
    some (ctx, some (#[xCastOp, sraOp] ++ negOps ++ #[castBackOp], #[castBackOp.getResult 0]))

def sdivPow2Exact := RewritePattern.fromLocalRewrite (sdivPow2ExactGenLocal .srai rfl .sub rfl 64)
def sdivwPow2Exact := RewritePattern.fromLocalRewrite (sdivPow2ExactGenLocal .sraiw rfl .subw rfl 32)

/-- General `sdiv x, 2^k` (`exact` not set): bias negative dividends before
    shifting so truncation rounds toward zero, then negate for a negative divisor:
    ```
    sign   := shiftDst x, (width - 1)   -- splat the sign bit
    corr   := corrDst sign, (width - k) -- 2^k - 1 if x < 0, else 0
    biased := addDst x, corr
    q      := shiftDst biased, k
    ```
    then `negDst 0, q` when the divisor is negative, where
    `(shiftDst, corrDst, addDst, negDst)` is `(riscv.srai, riscv.srli, riscv.add,
    riscv.sub)` at `width = 64` and the `w`-suffixed forms at `width = 32`. Mirrors
    the generic `sra`/`srl`/`add` sequence built by `DAGCombiner::visitSDIVLike`
    when the `exact` bit isn't set (Hacker's Delight §10-1); RISC-V's
    `BuildSDIVPow2` only replaces this with a branchy `cmov` form under
    `short-forward-branch-ialu` tuning, which we do not model, so this generic
    sequence is what RV64 emits by default.
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L5294-L5345
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVISelLowering.cpp#L27055-L27074 -/
def sdivPow2GenLocal (shiftDst : Riscv) (hShift : Riscv.propertiesOf shiftDst = RISCVImmediateProperties)
    (corrDst : Riscv) (hCorr : Riscv.propertiesOf corrDst = RISCVImmediateProperties)
    (addDst : Riscv) (hAdd : Riscv.propertiesOf addDst = Unit)
    (negDst : Riscv) (hNeg : Riscv.propertiesOf negDst = Unit) (width : Nat)
    (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, props) := matchSdiv op ctx.raw | return (ctx, none)
  if props.exact then return (ctx, none)
  let .integerType t := ((op.getResult 0).getType! ctx.raw).val | return (ctx, none)
  if t.bitwidth ≠ width then return (ctx, none)
  let some imm := matchConstantIntVal rhs ctx.raw | return (ctx, none)
  let some (k, isNeg) := matchSignedPow2Divisor width imm | return (ctx, none)
  /- `k = 0` (divisor ±1) would need a shift by the full register width, which has
     no legal immediate encoding; middle-end optimizations always turn `sdiv x, ±1`
     into `x`/`-x` well before instruction selection, so this case does not arise. -/
  if k = 0 then return (ctx, none)
  let (ctx, xCastOp) ← castToRegLocal ctx lhs
  let shSign := RISCVImmediateProperties.mk (BitVec.ofInt 64 (width - 1))
  let (ctx, signOp) ← WfRewriter.createOp! ctx shiftDst #[RegisterType.mk] #[xCastOp.getResult 0]
      #[] #[] (cast hShift.symm shSign) none
  let shCorr := RISCVImmediateProperties.mk (BitVec.ofInt 64 (width - k))
  let (ctx, corrOp) ← WfRewriter.createOp! ctx corrDst #[RegisterType.mk] #[signOp.getResult 0]
      #[] #[] (cast hCorr.symm shCorr) none
  let (ctx, biasedOp) ← WfRewriter.createOp! ctx addDst #[RegisterType.mk]
      #[xCastOp.getResult 0, corrOp.getResult 0] #[] #[] (cast hAdd.symm ()) none
  let shQ := RISCVImmediateProperties.mk (BitVec.ofInt 64 k)
  let (ctx, qOp) ← WfRewriter.createOp! ctx shiftDst #[RegisterType.mk] #[biasedOp.getResult 0]
      #[] #[] (cast hShift.symm shQ) none
  if ¬ isNeg then
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (qOp.getResult 0)
    some (ctx, some (#[xCastOp, signOp, corrOp, biasedOp, qOp, castBackOp], #[castBackOp.getResult 0]))
  else
    let (ctx, negOps, negOp) ← negateRegLocal negDst hNeg ctx (qOp.getResult 0)
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (negOp.getResult 0)
    some (ctx, some (#[xCastOp, signOp, corrOp, biasedOp, qOp] ++ negOps ++ #[castBackOp],
      #[castBackOp.getResult 0]))

def sdivPow2 := RewritePattern.fromLocalRewrite (sdivPow2GenLocal .srai rfl .srli rfl .add rfl .sub rfl 64)
def sdivwPow2 := RewritePattern.fromLocalRewrite (sdivPow2GenLocal .sraiw rfl .srliw rfl .addw rfl .subw rfl 32)

/-! ## `llvm.intr.assume`
  An assume only adds UB, so dropping it is always a refinement.
-/
def dropAssumeLocal (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  if op.getOpType! ctx.raw ≠ .llvm .intr__assume then return (ctx, none)
  some (ctx, some (#[], #[]))

def dropAssume := RewritePattern.fromLocalRewrite dropAssumeLocal

/-! # Pass implementation -/

def IselSDAG.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  /- `sdivPow2Exact`/`sdivwPow2Exact` are listed before `sdivPow2`/`sdivwPow2` to
     mirror the priority LLVM gives the `exact`-flag fast path, though both sides
     already guard on `exact`, so the two pairs are in fact mutually exclusive. -/
  let pattern := RewritePattern.GreedyRewritePattern #[
    dropAssume, udivPow2, udivwPow2, sdivPow2Exact, sdivwPow2Exact, sdivPow2, sdivwPow2]
  match RewritePattern.applyToFunctions pattern ctx op with
  | none => throw "Error while applying SDAG patterns"
  | some ctx => pure ctx

public def IselSDAG : Pass OpCode :=
  { name := "isel-sdag-riscv64"
    description :=
      "Lower LLVM IR to RISCV 64 assembly instruction selection pass."
    run := fun _ => IselSDAG.impl }
