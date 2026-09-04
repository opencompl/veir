module

public import Veir.Analysis.DataFlow.Domains.KnownBitsDomain
public import Veir.Analysis.DataFlow.SparseForwardDataFlowAnalysis
public import Veir.Interpreter.Evaluate

import Veir.Interfaces.FoldInterfaces
import Veir.Meta.BVDecide

public section

namespace Veir

/-!
# Known-bits analysis

This sparse forward analysis tracks fixed-width integer bits that are provably zero
or one. It currently understands integer constants and the `and`, `or`, and `xor`
operations in the Arith, Comb, and LLVM dialects. Other integer-producing operations
conservatively produce an unknown value of the result width.
-/

namespace KnownBits

/-- Known bits produced by bitwise AND. -/
def bitwiseAnd? (lhs rhs : KnownBits) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhsZero := h ▸ rhs.zero
    let rhsOne := h ▸ rhs.one
    some
      { bitwidth := lhs.bitwidth
        zero := lhs.zero ||| rhsZero
        one := lhs.one &&& rhsOne }
  else
    none

/-- Known bits produced by bitwise OR. -/
def bitwiseOr? (lhs rhs : KnownBits) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhsZero := h ▸ rhs.zero
    let rhsOne := h ▸ rhs.one
    some
      { bitwidth := lhs.bitwidth
        zero := lhs.zero &&& rhsZero
        one := lhs.one ||| rhsOne }
  else
    none

/-- Known bits produced by bitwise XOR. -/
def bitwiseXor? (lhs rhs : KnownBits) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhsZero := h ▸ rhs.zero
    let rhsOne := h ▸ rhs.one
    some
      { bitwidth := lhs.bitwidth
        zero := (lhs.zero &&& rhsZero) ||| (lhs.one &&& rhsOne)
        one := (lhs.zero &&& rhsOne) ||| (lhs.one &&& rhsZero) }
  else
    none

end KnownBits

namespace KnownBitsLattice

/-- Transfer known bits through bitwise AND. -/
def bitwiseAnd : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice
  | .bottom, _ | _, .bottom => .bottom
  | .top, .top => .top
  | .known lhs, .top | .top, .known lhs =>
      .known { lhs with one := 0 }
  | .known lhs, .known rhs =>
      match lhs.bitwiseAnd? rhs with
      | some bits => .known bits
      | none => .top

/--
Known-bits AND soundly over-approximates every result produced by the LLVM
interpreter from concrete values represented by its abstract operands.
-/
theorem bitwiseAnd_sound
    (lhs rhs : KnownBitsLattice)
    (bitwidth : Nat)
    (lhsValue rhsValue resultValue : BitVec bitwidth)
    (hlhs : RuntimeValue.int bitwidth (.val lhsValue) ∈ γ lhs)
    (hrhs : RuntimeValue.int bitwidth (.val rhsValue) ∈ γ rhs)
    (heval :
      foldEvaluate (.llvm .and) () #[IntegerType.mk bitwidth]
          #[.int bitwidth (.val lhsValue), .int bitwidth (.val rhsValue)] =
        .ok #[.int bitwidth (.val resultValue)]) :
    RuntimeValue.int bitwidth (.val resultValue) ∈ γ (bitwiseAnd lhs rhs) := by
  obtain rfl : resultValue = lhsValue &&& rhsValue := by
    simpa [foldEvaluate_llvm_and] using heval.symm
  cases lhs <;> cases rhs <;> simp_all only [not_mem_γ_bottom, mem_γ_top, bitwiseAnd]
  case known.top | top.known =>
    first
      | (obtain ⟨zero, _, rfl, hzero, _⟩ := mem_γ_known_iff.mp hlhs)
      | (obtain ⟨zero, _, rfl, hzero, _⟩ := mem_γ_known_iff.mp hrhs)
    refine mem_γ_known_iff.mpr
      ⟨zero, 0, rfl, fun i hi h => by simp [hzero i hi h], by simp⟩
  case known.known =>
    obtain ⟨lhsZero, lhsOne, rfl, hlzero, hlone⟩ := mem_γ_known_iff.mp hlhs
    obtain ⟨rhsZero, rhsOne, rfl, hrzero, hrone⟩ := mem_γ_known_iff.mp hrhs
    simp only [KnownBits.bitwiseAnd?]
    refine mem_γ_known_iff.mpr
      ⟨lhsZero ||| rhsZero, lhsOne &&& rhsOne, rfl, ?_,
        fun i hi h => by simp_all [hlone i hi, hrone i hi]⟩
    · intro i hi hresultZero
      specialize hlzero i hi
      specialize hrzero i hi
      simp_all <;> veir_bv_decide

/-- Transfer known bits through bitwise OR. -/
def bitwiseOr : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice
  | .bottom, _ | _, .bottom => .bottom
  | .top, .top => .top
  | .known lhs, .top | .top, .known lhs =>
      .known { lhs with zero := 0 }
  | .known lhs, .known rhs =>
      match lhs.bitwiseOr? rhs with
      | some bits => .known bits
      | none => .top

/-- Transfer known bits through bitwise XOR. -/
def bitwiseXor : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice
  | .bottom, _ | _, .bottom => .bottom
  | .top, .top => .top
  | .known lhs, .top | .top, .known lhs => .unknown lhs.bitwidth
  | .known lhs, .known rhs =>
      match lhs.bitwiseXor? rhs with
      | some bits => .known bits
      | none => .top

end KnownBitsLattice

namespace KnownBitsAnalysis

instance : SparseFactSpec .knownBits KnownBitsLattice where
  payloadEq := rfl

private def transferBitwise
    (operation : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice)
    (numResults : Nat)
    (operands : Array KnownBitsLattice) : Array KnownBitsLattice :=
  match operands.toList with
  | [] => Array.replicate numResults ⊥
  | first :: rest => Array.replicate numResults (rest.foldl operation first)

/--
Infer known bits for one operation. Bottom operands cause the transfer to wait for
more information; unsupported integer results receive a width-aware unknown value.
-/
def transfer
    (op : OperationPtr)
    (operands : Array KnownBitsLattice)
    (irCtx : WfIRContext OpCode) : Array KnownBitsLattice :=
  let numResults := op.getNumResults! irCtx.raw
  let resultTypes := op.getResultTypes! irCtx.raw
  let pessimisticUpdates := resultTypes.map fun resultType =>
    match resultType.val with
    | .integerType intType => .unknown intType.bitwidth
    | _ => ⊥

  if op.getNumRegions! irCtx.raw ≠ 0 then
    pessimisticUpdates
  else if operands.any (· = ⊥) then
    Array.replicate numResults ⊥
  else
    let opType := op.getOpType! irCtx.raw
    let exactOperands := operands.map fun
      | .known bits =>
          if bits.zero = ~~~bits.one then
            some (.int bits.bitwidth (.val bits.one))
          else
            none
      | _ => none
    match opType.foldsTo (op.getProperties! irCtx.raw opType) resultTypes exactOperands with
    | some results =>
        (results.zip resultTypes).map fun (result, resultType) =>
          match resultType.val, result with
          | .integerType _, .useOperand index => operands[index]?.getD ⊤
          | .integerType intType, .useConstant (.int bitwidth (.val value)) =>
              if h : bitwidth = intType.bitwidth then
                let value := value.cast h
                .known { bitwidth := intType.bitwidth, zero := ~~~value, one := value }
              else
                ⊤
          | .integerType _, .useConstant _ => ⊤
          | _, _ => ⊥
    | none =>
        match opType with
        | OpCode.arith Arith.constant =>
          let props := op.getProperties! irCtx.raw (OpCode.arith Arith.constant)
          Array.replicate numResults
            (.constant props.value.type.bitwidth props.value.value)
        | OpCode.llvm Llvm.mlir__constant =>
          let props := op.getProperties! irCtx.raw (OpCode.llvm Llvm.mlir__constant)
          match props.value with
          | .integer attr =>
              Array.replicate numResults (.constant attr.type.bitwidth attr.value)
          | _ => pessimisticUpdates
        | OpCode.hw HW.constant =>
          let props := op.getProperties! irCtx.raw (OpCode.hw HW.constant)
          Array.replicate numResults
            (.constant props.value.type.bitwidth props.value.value)
        | OpCode.arith Arith.andi
        | OpCode.llvm Llvm.and
        | OpCode.comb Comb.and =>
          transferBitwise KnownBitsLattice.bitwiseAnd numResults operands
        | OpCode.arith Arith.ori
        | OpCode.llvm Llvm.or
        | OpCode.comb Comb.or =>
          transferBitwise KnownBitsLattice.bitwiseOr numResults operands
        | OpCode.arith Arith.xori
        | OpCode.llvm Llvm.xor
        | OpCode.comb Comb.xor =>
          transferBitwise KnownBitsLattice.bitwiseXor numResults operands
        | _ => pessimisticUpdates

end KnownBitsAnalysis

/-- Sparse forward known-bits analysis for fixed-width integer SSA values. -/
def KnownBitsAnalysis : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new
    .knownBits
    .knownBits
    KnownBitsAnalysis.transfer
    (entryState := fun value irCtx =>
      match (value.getType! irCtx.raw).val with
      | .integerType intType => .unknown intType.bitwidth
      | _ => ⊤)

end Veir
