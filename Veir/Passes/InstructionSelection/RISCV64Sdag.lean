import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Passes.InstructionSelection.Common

namespace Veir

/-!
  This file replicates instruction selection patterns from LLVM's SelectionDAG instruction selector,
  to lower LLVM IR to RISC-V assembly (64 bits).
-/

/-- The index of the single set bit of `x`, or `none` when `x` is zero or has more
    than one bit set (`u &&& (u - 1)` clears the lowest set bit; if that leaves `0`,
    there was at most one). Used for Zbs single-bit immediate selection. -/
def singleSetBit (x : BitVec 64) : Option Int :=
  let u := x.toNat
  if u == 0 || (u &&& (u - 1)) != 0 then none else some (Nat.log2 u)

/-! # SelectionDAG Lowering Patterns  -/

/--
  `and x (not y)` -> `riscv.andn x y`. The `not` may appear on either operand.
-/
def andn_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchAnd op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 then return (ctx, none)
  let some (x, y) :=
    (match matchNot rhs ctx with
     | some y => some (lhs, y)
     | none => match matchNot lhs ctx with
               | some y => some (rhs, y)
               | none => none) | return (ctx, none)
  let (ctx, xCastOp) ← castToRegLocal ctx x
  let (ctx, yCastOp) ← castToRegLocal ctx y
  let (ctx, andnOp) ← WfRewriter.createOp! ctx (.riscv .andn) #[RegisterType.mk]
      #[xCastOp.getResult 0, yCastOp.getResult 0] #[] #[] () none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (andnOp.getResult 0)
  some (ctx, some (#[xCastOp, yCastOp, andnOp, castBackOp], #[castBackOp.getResult 0]))

/--
  `and x (not y)` -> `riscv.andn x y`. The `not` may appear on either operand.
-/
def andn (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite andn_local rewriter op opInBounds

/--
  `or x (not y)` -> `riscv.orn x y`. The `not` may appear on either operand.
-/
def orn_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchOr op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 then return (ctx, none)
  let some (x, y) :=
    (match matchNot rhs ctx with
     | some y => some (lhs, y)
     | none => match matchNot lhs ctx with
               | some y => some (rhs, y)
               | none => none) | return (ctx, none)
  let (ctx, xCastOp) ← castToRegLocal ctx x
  let (ctx, yCastOp) ← castToRegLocal ctx y
  let (ctx, ornOp) ← WfRewriter.createOp! ctx (.riscv .orn) #[RegisterType.mk]
      #[xCastOp.getResult 0, yCastOp.getResult 0] #[] #[] () none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (ornOp.getResult 0)
  some (ctx, some (#[xCastOp, yCastOp, ornOp, castBackOp], #[castBackOp.getResult 0]))

/--
  `or x (not y)` -> `riscv.orn x y`. The `not` may appear on either operand.
-/
def orn (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite orn_local rewriter op opInBounds

/--
  `xor x (not y)` -> `riscv.xnor x y`. The `not` may appear on either operand.
-/
def xnor_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchXor op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 then return (ctx, none)
  let some (x, y) :=
    (match matchNot rhs ctx with
     | some y => some (lhs, y)
     | none => match matchNot lhs ctx with
               | some y => some (rhs, y)
               | none => none) | return (ctx, none)
  let (ctx, xCastOp) ← castToRegLocal ctx x
  let (ctx, yCastOp) ← castToRegLocal ctx y
  let (ctx, xnorOp) ← WfRewriter.createOp! ctx (.riscv .xnor) #[RegisterType.mk]
      #[xCastOp.getResult 0, yCastOp.getResult 0] #[] #[] () none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (xnorOp.getResult 0)
  some (ctx, some (#[xCastOp, yCastOp, xnorOp, castBackOp], #[castBackOp.getResult 0]))

/--
  `xor x (not y)` -> `riscv.xnor x y`. The `not` may appear on either operand.
-/
def xnor (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite xnor_local rewriter op opInBounds

/--
  `sub (shl M (8 - Y)) (lshr M Y)` -> `riscv.orcb M`,
  where `M = and Z (0x0101_0101_0101_0101 <<< Y)`
-/
def orcb_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (a, b, _) := matchSub op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 then return (ctx, none)
  /- left operand must be `shl M (8 - Y)` for some `0 ≤ Y < 8` -/
  let some aOp := getDefiningOp a ctx | return (ctx, none)
  let some (m, shamt, _) := matchShl aOp ctx | return (ctx, none)
  let some shc := matchConstantIntVal shamt ctx | return (ctx, none)
  if shc.value < 1 || 8 < shc.value then return (ctx, none)
  let y : Nat := (8 - shc.value).toNat
  /- right operand must be `M` itself (when `Y = 0`) or `lshr M Y` -/
  let rightMatches : Bool :=
    if y == 0 then
      decide (b = m)
    else
      match getDefiningOp b ctx with
      | none => false
      | some bOp =>
        match matchLshr bOp ctx with
        | none => false
        | some (m', yShamt, _) =>
          match matchConstantIntVal yShamt ctx with
          | none => false
          | some yc => yc.value == (y : Int) && decide (m' = m)
  if !rightMatches then return (ctx, none)
  /- soundness gate: `M = and Z (0x0101_0101_0101_0101 <<< Y)` -/
  let some mOp := getDefiningOp m ctx | return (ctx, none)
  let some (mo0, mo1, _) := matchAnd mOp ctx | return (ctx, none)
  let maskBV : BitVec 64 := BitVec.ofNat 64 0x0101010101010101 <<< y
  let isMask : ValuePtr → Bool := fun v =>
    match matchConstantIntVal v ctx with
    | some attr => BitVec.ofInt 64 attr.value == maskBV
    | none => false
  if !(isMask mo0 || isMask mo1) then return (ctx, none)
  let (ctx, mCastOp) ← castToRegLocal ctx m
  /- actual `riscv.orcb` -/
  let (ctx, orcbOp) ← WfRewriter.createOp! ctx (.riscv .orcb) #[RegisterType.mk] #[mCastOp.getResult 0]
      #[] #[] () none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (orcbOp.getResult 0)
  some (ctx, some (#[mCastOp, orcbOp, castBackOp], #[castBackOp.getResult 0]))

/--
  `sub (shl M (8 - Y)) (lshr M Y)` -> `riscv.orcb M`,
  where `M = and Z (0x0101_0101_0101_0101 <<< Y)`
-/
def orcb (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite orcb_local rewriter op opInBounds



/-! ## Immediate selection

  These rules replicate LLVM's `PatGprImm` family from `RISCVInstrInfo.td` /
  `RISCVInstrInfoZb.td`: an arithmetic/logic node with a constant operand selects
  directly to the immediate form of the instruction, rather than materializing the
  constant into a register first. Each rule matches the LLVM op with an
  `llvm.mlir.constant` operand and, when the immediate fits the instruction's field,
  emits the immediate-form RISC-V op. The constant is matched only on the right
  operand, since the canonicalizer (run before isel) places it there — mirroring
  `PatGprImm`'s `(OpNode GPR:$rs1, imm)` shape. The reg-reg fallback (non-constant
  operand, or out-of-range immediate) is handled by the generic `isel-riscv64` pass.

  See the `PatGprImm`/`PatGprSimm12`/`PatGprUimmLog2XLen` classes:
  https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfo.td#L1386-L1393
-/

/--
  `OP x (const imm)` -> `OPi x imm`, when the op's result has width `width` and the
  immediate lies in `[lo, hi]`. Mirrors `PatGprImm<OpNode, Inst, ImmType>`. The
  matcher's trailing properties component (`α`) is ignored.
-/
def selectBinopImmLocal {α} (matchPair : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × α))
    (dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties) (width : Nat) (lo hi : Int)
    (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchPair op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ width then return (ctx, none)
  let some imm := matchConstantIntVal rhs ctx | return (ctx, none)
  if imm.value < lo || imm.value > hi then return (ctx, none)
  let (ctx, xCastOp) ← castToRegLocal ctx lhs
  let immProps := RISCVImmediateProperties.mk (IntegerAttr.mk imm.value (IntegerType.mk 64))
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.riscv dst) #[RegisterType.mk] #[xCastOp.getResult 0]
      #[] #[] (cast h.symm immProps) none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (newOp.getResult 0)
  some (ctx, some (#[xCastOp, newOp, castBackOp], #[castBackOp.getResult 0]))

/-- imm12 binops on i64: `add/or/and/xor x (const ∈ [-2048, 2047])` -> `addi/ori/andi/xori`.
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfo.td#L1467-L1474 -/
def addi := RewritePattern.fromLocalRewrite (selectBinopImmLocal matchAdd .addi rfl 64 (-2048) 2047)
def ori  := RewritePattern.fromLocalRewrite (selectBinopImmLocal matchOr  .ori  rfl 64 (-2048) 2047)
def andi := RewritePattern.fromLocalRewrite (selectBinopImmLocal matchAnd .andi rfl 64 (-2048) 2047)
def xori := RewritePattern.fromLocalRewrite (selectBinopImmLocal matchXor .xori rfl 64 (-2048) 2047)

/-- uimm6 shifts on i64: `shl/lshr/ashr x (const ∈ [0, 63])` -> `slli/srli/srai`.
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfo.td#L1475-L1477 -/
def slli := RewritePattern.fromLocalRewrite (selectBinopImmLocal matchShl  .slli rfl 64 0 63)
def srli := RewritePattern.fromLocalRewrite (selectBinopImmLocal matchLshr .srli rfl 64 0 63)
def srai := RewritePattern.fromLocalRewrite (selectBinopImmLocal matchAshr .srai rfl 64 0 63)

/-- Word `*w` immediate forms (best-effort: gated on an i32 result as a proxy for
    LLVM's `binop_allwusers`, which we lack the demanded-bits analysis to model).
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfo.td#L2249-L2254 -/
def addiw := RewritePattern.fromLocalRewrite (selectBinopImmLocal matchAdd  .addiw rfl 32 (-2048) 2047)
def slliw := RewritePattern.fromLocalRewrite (selectBinopImmLocal matchShl  .slliw rfl 32 0 31)
def srliw := RewritePattern.fromLocalRewrite (selectBinopImmLocal matchLshr .srliw rfl 32 0 31)
def sraiw := RewritePattern.fromLocalRewrite (selectBinopImmLocal matchAshr .sraiw rfl 32 0 31)

/--
  Immediate-form integer comparison selection (`PatGprSimm12` family). When the
  rhs is a constant that fits a signed 12-bit immediate, lower `icmp` directly to
  `slti`/`sltiu`, inverting the sense with `xori _ 1` for the `≥` predicates and
  using the identity `x ≤ C  ==  x < C+1` for the `≤` predicates:

      slt  x C  ->       slti  x C
      ult  x C  ->       sltiu x C
      sge  x C  -> xori (slti  x C)      1
      uge  x C  -> xori (sltiu x C)      1
      sle  x C  ->       slti  x (C+1)
      ule  x C  ->       sltiu x (C+1)              (requires C ≠ -1)

  Canonicalization moves the constant to the rhs before isel, so we only match
  there. Each emitted immediate (`C` or `C+1`) must still land in `[-2048, 2047]`,
  otherwise we bail and defer to the reg-reg `icmp` lowering in `isel-riscv64`.
  For the unsigned `≤` off-by-one form, `C = -1` (unsigned `UINT_MAX`) is
  excluded: there `C+1` wraps to `0` and `x < 0` would not equal `x ≤ UINT_MAX`.

  The `>` predicates (`sgt`/`ugt`) are deliberately *not* handled: their reg-reg
  lowering (`slt`/`sltu` with swapped operands, no `xori`) is already the same
  instruction count, and folding the constant is strictly worse for `x > 0`,
  which the reg-reg path plus the `li 0 -> x0` combine lowers to a single
  `slt x0, x`.

  LLVM correspondence (commit d9906882fc61):
  * `slt`/`ult` immediate: `PatGprSimm12<setlt, SLTI>` / `<setult, SLTIU>`
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVInstrInfo.td#L1636-L1638
  * `sle`/`ule` off-by-one (`x <= C == x < C+1`, plus the `x <= MAX -> true`
    fold that motivates the `C = -1` guard): generic `SimplifySetCC`
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/CodeGen/SelectionDAG/TargetLowering.cpp#L5273-L5290
  * `sge`/`uge` `xori`-inversion: `SETGE`/`SETUGE` are `Expand`ed (legalized to
    `xor (setlt ...), 1`)
    https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVISelLowering.cpp#L326-L332
-/
def slti_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, prop) := matchIcmp op ctx | return (ctx, none)
  let .integerType lt := (lhs.getType! ctx.raw).val | return (ctx, none)
  if lt.bitwidth ≠ 64 then return (ctx, none)
  let some cst := matchConstantIntVal rhs ctx | return (ctx, none)
  let c := cst.value
  /- Emit `[xori _ 1] (<dst> x immVal)`, or bail (leaving `op` for the reg-reg
     lowering) when `immVal` does not fit a signed 12-bit field. `dst` is either
     `.slti` or `.sltiu`, both with `RISCVImmediateProperties` (hence `h`). -/
  let emit (dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties)
      (immVal : Int) (wrap : Bool) :
      Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
    if immVal < -2048 || immVal > 2047 then return (ctx, none)
    let immProps := RISCVImmediateProperties.mk (IntegerAttr.mk immVal (IntegerType.mk 64))
    let (ctx, xCastOp) ← castToRegLocal ctx lhs
    let (ctx, cmpOp) ← WfRewriter.createOp! ctx (.riscv dst) #[RegisterType.mk] #[xCastOp.getResult 0]
        #[] #[] (cast h.symm immProps) none
    if wrap then
      let one := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (ctx, xorOp) ← WfRewriter.createOp! ctx (.riscv .xori) #[RegisterType.mk] #[cmpOp.getResult 0]
          #[] #[] one none
      let (ctx, castBackOp) ← replaceWithRegLocal ctx op (xorOp.getResult 0)
      some (ctx, some (#[xCastOp, cmpOp, xorOp, castBackOp], #[castBackOp.getResult 0]))
    else
      let (ctx, castBackOp) ← replaceWithRegLocal ctx op (cmpOp.getResult 0)
      some (ctx, some (#[xCastOp, cmpOp, castBackOp], #[castBackOp.getResult 0]))
  match prop.predicate with
  | .slt => emit .slti  rfl c       false
  | .ult => emit .sltiu rfl c       false
  | .sge => emit .slti  rfl c       true
  | .uge => emit .sltiu rfl c       true
  | .sle => emit .slti  rfl (c + 1) false
  | .ule => if c = -1 then return (ctx, none) else emit .sltiu rfl (c + 1) false
  | _    => return (ctx, none)

/-- Immediate-form integer comparison selection (`PatGprSimm12` family, see `slti_local`). -/
def slti (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite slti_local rewriter op opInBounds

/-! ## Zbs single-bit immediate selection

  These mirror the Zbs mask patterns in `RISCVInstrInfoZb.td`: `bseti`/`binvi`/`bclri`
  recognize an `or`/`xor`/`and` against a constant whose (complemented, for `bclri`)
  value is a single set bit, and emit the bit *index*. The `!isInt<12>` guard matches
  the `SingleBitSetMask`/`BCLRMask` `ImmLeaf` predicates, so the plain `andi`/`ori`/`xori`
  forms win whenever the immediate already fits a signed 12-bit field.

  `BCLRMask`/`SingleBitSetMask` predicates:
  https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfoZb.td#L69-L80
  `bclri`/`bseti`/`binvi` select patterns:
  https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfoZb.td#L529-L534
-/

/--
  Single-bit immediate selection. `complement = false` for `bseti`/`binvi` (the
  immediate itself is a single set bit); `complement = true` for `bclri` (the
  *complement* of the immediate is a single set bit). The emitted immediate is the
  bit index. Only fires when the immediate does not fit a signed 12-bit field.
-/
def selectSingleBitLocal {α} (matchPair : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × α))
    (dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties) (complement : Bool)
    (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchPair op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 then return (ctx, none)
  let some imm := matchConstantIntVal rhs ctx | return (ctx, none)
  /- ANDI/ORI/XORI handle the simm12 cases; only fire when the immediate doesn't fit. -/
  if !(imm.value < -2048 || imm.value > 2047) then return (ctx, none)
  let bv := BitVec.ofInt 64 imm.value
  let some n := singleSetBit (if complement then ~~~ bv else bv) | return (ctx, none)
  let (ctx, xCastOp) ← castToRegLocal ctx lhs
  let immProps := RISCVImmediateProperties.mk (IntegerAttr.mk n (IntegerType.mk 64))
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.riscv dst) #[RegisterType.mk] #[xCastOp.getResult 0]
      #[] #[] (cast h.symm immProps) none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (newOp.getResult 0)
  some (ctx, some (#[xCastOp, newOp, castBackOp], #[castBackOp.getResult 0]))

def bseti := RewritePattern.fromLocalRewrite (selectSingleBitLocal matchOr  .bseti rfl false)
def binvi := RewritePattern.fromLocalRewrite (selectSingleBitLocal matchXor .binvi rfl false)
def bclri := RewritePattern.fromLocalRewrite (selectSingleBitLocal matchAnd .bclri rfl true)

/-- `and (lshr x n) 1` -> `riscv.bexti x n` (`PatGprImm`-style single-bit extract).
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfoZb.td#L536-L537 -/
def bexti_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchAnd op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 then return (ctx, none)
  let some one := matchConstantIntVal rhs ctx | return (ctx, none)
  if one.value ≠ 1 then return (ctx, none)
  let some shrOp := getDefiningOp lhs ctx | return (ctx, none)
  let some (x, shamt, _) := matchLshr shrOp ctx | return (ctx, none)
  let some sh := matchConstantIntVal shamt ctx | return (ctx, none)
  if sh.value < 0 || sh.value > 63 then return (ctx, none)
  let (ctx, xCastOp) ← castToRegLocal ctx x
  let immProps := RISCVImmediateProperties.mk (IntegerAttr.mk sh.value (IntegerType.mk 64))
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.riscv .bexti) #[RegisterType.mk] #[xCastOp.getResult 0]
      #[] #[] immProps none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (newOp.getResult 0)
  some (ctx, some (#[xCastOp, newOp, castBackOp], #[castBackOp.getResult 0]))

/-- `and (lshr x n) 1` -> `riscv.bexti x n` (see `bexti_local`). -/
def bexti (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite bexti_local rewriter op opInBounds

/-- `fshr x x (const)` on i32 is a constant word rotate-right -> `riscv.roriw`
    (i32 analogue of `fshrConst` -> `rori`; mirrors `PatGprImm<riscv_rorw, RORIW, uimm5>`).
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfoZb.td#L504 -/
def roriw_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (a, b, amt) := matchFshr op ctx | return (ctx, none)
  if a ≠ b then return (ctx, none)
  let some amtAttr := matchConstantIntVal amt ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 32 then return (ctx, none)
  let sh : Int := ((amtAttr.value % 32) + 32) % 32
  let (ctx, valCastOp) ← castToRegLocal ctx a
  let immProps := RISCVImmediateProperties.mk (IntegerAttr.mk sh (IntegerType.mk 64))
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.riscv .roriw) #[RegisterType.mk] #[valCastOp.getResult 0]
      #[] #[] immProps none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (newOp.getResult 0)
  some (ctx, some (#[valCastOp, newOp, castBackOp], #[castBackOp.getResult 0]))

/-- `fshr x x (const)` on i32 -> `riscv.roriw` (see `roriw_local`). -/
def roriw (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite roriw_local rewriter op opInBounds

/-- `fshl x x (const)` on i32 is a constant word rotate-left. There is no `roliw`,
    so (like `fshlConst` at i64) it lowers to `riscv.roriw` with the negated immediate
    `(32 - amt) mod 32` (i32 analogue of `fshlConst`). -/
def roliw_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (a, b, amt) := matchFshl op ctx | return (ctx, none)
  if a ≠ b then return (ctx, none)
  let some amtAttr := matchConstantIntVal amt ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 32 then return (ctx, none)
  /- rotate-left by `sh` == rotate-right by `32 - sh` (mod 32). -/
  let sh : Int := ((amtAttr.value % 32) + 32) % 32
  let imm : Int := (32 - sh) % 32
  let (ctx, valCastOp) ← castToRegLocal ctx a
  let immProps := RISCVImmediateProperties.mk (IntegerAttr.mk imm (IntegerType.mk 64))
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.riscv .roriw) #[RegisterType.mk] #[valCastOp.getResult 0]
      #[] #[] immProps none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (newOp.getResult 0)
  some (ctx, some (#[valCastOp, newOp, castBackOp], #[castBackOp.getResult 0]))

/-- `fshl x x (const)` on i32 -> `riscv.roriw` with negated immediate (see `roliw_local`). -/
def roliw (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite roliw_local rewriter op opInBounds

/-- `shl (zext i32->i64 x) (const ∈ [0,31])` -> `riscv.slliuw x shamt`
    (Zba: `(i64 (shl (and GPR, 0xFFFFFFFF), uimm5)) -> SLLI_UW`; our `zext` is the mask).
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfoZb.td#L821-L822 -/
def slliuw_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (base, shamt, _) := matchShl op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 then return (ctx, none)
  let some sh := matchConstantIntVal shamt ctx | return (ctx, none)
  if sh.value < 0 || sh.value > 31 then return (ctx, none)
  let some baseOp := getDefiningOp base ctx | return (ctx, none)
  let some (x, _) := matchZext baseOp ctx | return (ctx, none)
  let .integerType srcT := (x.getType! ctx.raw).val | return (ctx, none)
  if srcT.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, xCastOp) ← castToRegLocal ctx x
  let immProps := RISCVImmediateProperties.mk (IntegerAttr.mk sh.value (IntegerType.mk 64))
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.riscv .slliuw) #[RegisterType.mk] #[xCastOp.getResult 0]
      #[] #[] immProps none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (newOp.getResult 0)
  some (ctx, some (#[xCastOp, newOp, castBackOp], #[castBackOp.getResult 0]))

/-- `shl (zext i32->i64 x) (const ∈ [0,31])` -> `riscv.slliuw x shamt` (see `slliuw_local`). -/
def slliuw (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite slliuw_local rewriter op opInBounds

/-- llvm.zext x i1 to i64 -> and x 1 -/
def zext_1_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operand, _) := matchZext op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 then return (ctx, none)
  let .integerType opType := (operand.getType! ctx.raw).val | return (ctx, none)
  if opType.bitwidth ≠ 1 then return (ctx, none)
  /- First, cast the operand to registers -/
  let (ctx, opCastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand]
      #[] #[] () none
  let imm := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
  let (ctx, andiOp) ← WfRewriter.createOp! ctx (.riscv .andi) #[RegisterType.mk] #[opCastOp.getResult 0]
      #[] #[] imm none
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[t] #[andiOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[opCastOp, andiOp, castOp], #[castOp.getResult 0]))

/-- llvm.zext x i1 to i64 -> and x 1 -/
def zext_1 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite zext_1_local rewriter op opInBounds

/-- llvm.sext x i1 to i64 -> srai (slli x 63) 63 -/
def sext_1_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operand, _) := matchSext op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 then return (ctx, none)
  let .integerType opType := (operand.getType! ctx.raw).val | return (ctx, none)
  if opType.bitwidth ≠ 1 then return (ctx, none)
  /- First, cast the operand to registers -/
  let (ctx, opCastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand]
      #[] #[] () none
  let imm := RISCVImmediateProperties.mk (IntegerAttr.mk 63 (IntegerType.mk 64))
  let (ctx, slliOp) ← WfRewriter.createOp! ctx (.riscv .slli) #[RegisterType.mk] #[opCastOp.getResult 0]
      #[] #[] imm none
  let (ctx, sraiOp) ← WfRewriter.createOp! ctx (.riscv .srai) #[RegisterType.mk] #[slliOp.getResult 0]
      #[] #[] imm none
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[t] #[sraiOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[opCastOp, slliOp, sraiOp, castOp], #[castOp.getResult 0]))

/-- llvm.sext x i1 to i64 -> srai (slli x 63) 63 -/
def sext_1 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sext_1_local rewriter op opInBounds

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
def matchSignedPow2Divisor (v : Int) : Option (Nat × Bool) := do
  let k ← log2IfPow2 v.natAbs
  return (k, decide (v < 0))

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
  let some (lhs, rhs, _) := matchUdiv op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ width then return (ctx, none)
  let some imm := matchConstantIntVal rhs ctx | return (ctx, none)
  let some k := matchUnsignedPow2Divisor width imm.value | return (ctx, none)
  let (ctx, xCastOp) ← castToRegLocal ctx lhs
  let shamt := RISCVImmediateProperties.mk (IntegerAttr.mk k (IntegerType.mk 64))
  let (ctx, shiftOp) ← WfRewriter.createOp! ctx (.riscv dst) #[RegisterType.mk] #[xCastOp.getResult 0]
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
  let zero := RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64))
  let (ctx, zeroOp) ← WfRewriter.createOp! ctx (.riscv .li) #[RegisterType.mk] #[]
      #[] #[] zero none
  let (ctx, negOp) ← WfRewriter.createOp! ctx (.riscv negDst) #[RegisterType.mk] #[zeroOp.getResult 0, x]
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
  let some (lhs, rhs, props) := matchSdiv op ctx | return (ctx, none)
  if ¬ props.exact then return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ width then return (ctx, none)
  let some imm := matchConstantIntVal rhs ctx | return (ctx, none)
  let some (k, isNeg) := matchSignedPow2Divisor imm.value | return (ctx, none)
  let (ctx, xCastOp) ← castToRegLocal ctx lhs
  let shamt := RISCVImmediateProperties.mk (IntegerAttr.mk k (IntegerType.mk 64))
  let (ctx, sraOp) ← WfRewriter.createOp! ctx (.riscv dst) #[RegisterType.mk] #[xCastOp.getResult 0]
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
  let some (lhs, rhs, props) := matchSdiv op ctx | return (ctx, none)
  if props.exact then return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ width then return (ctx, none)
  let some imm := matchConstantIntVal rhs ctx | return (ctx, none)
  let some (k, isNeg) := matchSignedPow2Divisor imm.value | return (ctx, none)
  /- `k = 0` (divisor ±1) would need a shift by the full register width, which has
     no legal immediate encoding; middle-end optimizations always turn `sdiv x, ±1`
     into `x`/`-x` well before instruction selection, so this case does not arise. -/
  if k = 0 then return (ctx, none)
  let (ctx, xCastOp) ← castToRegLocal ctx lhs
  let shSign := RISCVImmediateProperties.mk (IntegerAttr.mk (width - 1) (IntegerType.mk 64))
  let (ctx, signOp) ← WfRewriter.createOp! ctx (.riscv shiftDst) #[RegisterType.mk] #[xCastOp.getResult 0]
      #[] #[] (cast hShift.symm shSign) none
  let shCorr := RISCVImmediateProperties.mk (IntegerAttr.mk (width - k) (IntegerType.mk 64))
  let (ctx, corrOp) ← WfRewriter.createOp! ctx (.riscv corrDst) #[RegisterType.mk] #[signOp.getResult 0]
      #[] #[] (cast hCorr.symm shCorr) none
  let (ctx, biasedOp) ← WfRewriter.createOp! ctx (.riscv addDst) #[RegisterType.mk]
      #[xCastOp.getResult 0, corrOp.getResult 0] #[] #[] (cast hAdd.symm ()) none
  let shQ := RISCVImmediateProperties.mk (IntegerAttr.mk k (IntegerType.mk 64))
  let (ctx, qOp) ← WfRewriter.createOp! ctx (.riscv shiftDst) #[RegisterType.mk] #[biasedOp.getResult 0]
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

/-! # Pass implementation -/

def IselSDAG.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  /- Order matters where patterns overlap: the more specific Zbs/Zba rules (`bexti`,
     `slliuw`) must precede the generic `andi`/`slli` forms they would otherwise be
     shadowed by. The `bseti`/`bclri`/`binvi` rules are mutually exclusive with
     `ori`/`andi`/`xori` via their `!isInt<12>` guard, so their order is immaterial.
     `sdivPow2Exact`/`sdivwPow2Exact` are listed before `sdivPow2`/`sdivwPow2` to
     mirror the priority LLVM gives the `exact`-flag fast path, though both sides
     already guard on `exact`, so the two pairs are in fact mutually exclusive. -/
  let pattern := RewritePattern.GreedyRewritePattern #[andn, orn, xnor, orcb,
    bexti, bseti, bclri, binvi, slliuw,
    addi, ori, andi, xori, slli, srli, srai, slti,
    addiw, slliw, srliw, sraiw, roriw, roliw, zext_1, sext_1,
    udivPow2, udivwPow2, sdivPow2Exact, sdivwPow2Exact, sdivPow2, sdivwPow2]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying SDAG patterns"
  | some ctx => pure ctx

public def IselSDAG : Pass OpCode :=
  { name := "isel-sdag-riscv64"
    description :=
      "Lower LLVM IR to RISCV 64 assembly instruction selection pass."
    run := IselSDAG.impl }
