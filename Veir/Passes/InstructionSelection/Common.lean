module

public import Veir.Pass
public import Veir.PatternRewriter.Puddle.Builders

public section

namespace Veir

/-!
  Shared helpers for the RISC-V instruction-selection lowering patterns.
-/

/--
  Create a detached `unrealized_conversion_cast : (typeof v) -> !riscv.reg`,
  returning the updated context and the register-typed cast operation. The
  caller is responsible for inserting the returned operation.
-/
def castToRegLocal (ctx : WfIRContext OpCode) (v : ValuePtr) :
    Option (WfIRContext OpCode × OperationPtr) :=
  WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast
      #[RegisterType.mk] #[v] #[] #[] () none

/--
  Create a detached `unrealized_conversion_cast` from `reg` back to `op`'s
  result type, returning the updated context and the cast operation. The target
  type is read from `op`, so this is type-agnostic (it also handles non-`i64`
  results, e.g. the `!llvm.ptr` produced by `getelementptr`). The caller is
  responsible for inserting the returned operation and replacing `op`'s result
  with its result.
-/
def replaceWithRegLocal (ctx : WfIRContext OpCode) (op : OperationPtr) (reg : ValuePtr) :
    Option (WfIRContext OpCode × OperationPtr) :=
  let type := (op.getResult 0).getType! ctx.raw
  WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast
      #[type] #[reg] #[] #[] () none

/-- Immediate properties holding `value` as a 64-bit immediate. -/
def mkRISCVImm (value : Int) : RISCVImmediateProperties :=
  RISCVImmediateProperties.mk (BitVec.ofInt 64 value)

/-- Create a detached register-result `dst` op with immediate `value`. -/
def createRISCVImmLocal (ctx : WfIRContext OpCode)
    (dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties)
    (operands : Array ValuePtr) (value : Int) :
    Option (WfIRContext OpCode × OperationPtr) :=
  WfRewriter.createOp! ctx dst #[RegisterType.mk] operands #[] #[]
      (cast h.symm (mkRISCVImm value)) none

/-- Create a detached register-result `dst` op without properties. -/
def createRISCVUnitLocal (ctx : WfIRContext OpCode)
    (dst : Riscv) (h : Riscv.propertiesOf dst = Unit) (operands : Array ValuePtr) :
    Option (WfIRContext OpCode × OperationPtr) :=
  WfRewriter.createOp! ctx dst #[RegisterType.mk] operands #[] #[]
      (cast h.symm ()) none

/-- The index of the single set bit of `x`, or `none` when `x` is zero or has more
    than one bit set (`u &&& (u - 1)` clears the lowest set bit; if that leaves `0`,
    there was at most one). Used for Zbs single-bit immediate selection. -/
def singleSetBit (x : BitVec 64) : Option Int :=
  let u := x.toNat
  if u == 0 || (u &&& (u - 1)) != 0 then none else some (Nat.log2 u)

/-- The mask the `orcb` selection's soundness gate looks for: `0x0101_0101_0101_0101 <<< Y`, whose only
    set bit in each byte is bit `Y`. -/
def orcbMaskBV (y : Nat) : BitVec 64 := BitVec.ofNat 64 0x0101010101010101 <<< y

/-! ## Puddle lowering patterns -/

section
open Puddle

/--
  RISC-V lowerings with Puddle for unary operations.
  `guard` adds conditions on the matched operand and result types and on the properties of the
  `srcOp` operation.
-/
def lowerUnary (srcOp : OpCode) (bw : Nat) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp))
    (guard : Handle OpCode .type → Handle OpCode .type → Handle OpCode (.prop srcOp) →
      MatchProg.Builder Unit := fun _ _ _ => pure ()) : Pattern OpCode :=
  Pattern.Builder
    (do
      let opType ← MatchProg.type (Attr := IntegerType) (·.bitwidth = bw)
      let resType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value opType
      let root ← MatchProg.root srcOp #[x] #[resType]
      guard opType resType root.properties
      return (resType, x))
    (fun (resType, x) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let castOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[x] #[regType]
      let riscvResOp ← CreateProg.operation (.riscv riscvOp)
          #[castOp.res[0]!] #[regType] riscvProps
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[riscvResOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/--
  RISC-V for binary operations that share a single integer type between both operands and the
  result: cast both operands to registers, optionally apply `extend` to each register first (e.g.
  `riscv.sextw` for the signed min/max `i32` arms, since `castToRegLocal`'s zero-extension does not
  preserve signed order), apply `riscvOp`, and cast the result back to the source type.
  `guard` adds conditions on the matched type and on the properties of the `srcOp` operation.
-/
def lowerBinary (srcOp : OpCode) (typeMatcher : IntegerType → Bool) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp))
    (extend : Option (Σ extOp : Riscv, propertiesOf (OpCode.riscv extOp)) := none)
    (guard : Handle OpCode .type → Handle OpCode (.prop srcOp) → MatchProg.Builder Unit :=
      fun _ _ => pure ()) : Pattern OpCode :=
  Pattern.Builder
    (do
      let opType ← MatchProg.type (Attr := IntegerType) typeMatcher
      let lhs ← MatchProg.value opType
      let rhs ← MatchProg.value opType
      let root ← MatchProg.root srcOp #[lhs, rhs] #[opType]
      guard opType root.properties
      return (opType, lhs, rhs))
    (fun (opType, lhs, rhs) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let lcastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[lhs] #[regType]
      let rcastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[rhs] #[regType]
      let (lval, rval) ← match extend with
        | some ⟨extOp, extProps⟩ => do
          let lextOp ← CreateProg.operation (.riscv extOp) #[lcastOp.res[0]!] #[regType] extProps
          let rextOp ← CreateProg.operation (.riscv extOp) #[rcastOp.res[0]!] #[regType] extProps
          pure (lextOp.res[0]!, rextOp.res[0]!)
        | none => pure (lcastOp.res[0]!, rcastOp.res[0]!)
      let riscvResOp ← CreateProg.operation (.riscv riscvOp)
          #[lval, rval] #[regType] riscvProps
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[riscvResOp.res[0]!] #[opType]
      return castBackOp)
    (fun castBackOp => castBackOp)

end

end Veir
