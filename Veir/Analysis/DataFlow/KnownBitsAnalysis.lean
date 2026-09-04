module

public import Veir.Analysis.DataFlow.Domains.KnownBitsDomain
public import Veir.Analysis.DataFlow.SparseForwardDataFlowAnalysis

import Veir.Interfaces.FoldInterfaces

public section

namespace Veir

/-!
# Known-bits analysis

This sparse forward analysis tracks fixed-width integer bits that are provably zero
or one. It currently understands integer constants and the `and`, `or`, and `xor`
operations in the Arith, Comb, and LLVM dialects. Other integer-producing operations
conservatively produce an unknown value of the result width.
-/

namespace KnownBitsAnalysis

instance : SparseFactSpec .knownBits KnownBitsLattice where
  payloadEq := rfl

private def transferBitwise
    (operation : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice)
    (numResults : Nat)
    (operands : Array KnownBitsLattice) : Array (Option KnownBitsLattice) :=
  match operands.toList with
  | [] => Array.replicate numResults none
  | first :: rest => Array.replicate numResults (some (rest.foldl operation first))

/--
Infer known bits for one operation. Bottom operands cause the transfer to wait for
more information; unsupported integer results receive a width-aware unknown value.
-/
def transfer
    (op : OperationPtr)
    (operands : Array KnownBitsLattice)
    (irCtx : WfIRContext OpCode) : Array (Option KnownBitsLattice) :=
  let numResults := op.getNumResults! irCtx.raw
  let resultTypes := op.getResultTypes! irCtx.raw
  let pessimisticUpdates := resultTypes.map fun resultType =>
    match resultType.val with
    | .integerType intType => some (.unknown intType.bitwidth)
    | _ => none

  if op.getNumRegions! irCtx.raw ≠ 0 then
    pessimisticUpdates
  else if operands.any (· = ⊥) then
    Array.replicate numResults none
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
          | .integerType _, .useOperand index => some (operands[index]?.getD ⊤)
          | .integerType intType, .useConstant (.int bitwidth (.val value)) =>
              if h : bitwidth = intType.bitwidth then
                let value := value.cast h
                some (.known { bitwidth := intType.bitwidth, zero := ~~~value, one := value })
              else
                some ⊤
          | .integerType _, .useConstant _ => some ⊤
          | _, _ => none
    | none =>
        match opType with
        | OpCode.arith Arith.constant =>
          let props := op.getProperties! irCtx.raw (OpCode.arith Arith.constant)
          Array.replicate numResults
            (some (.constant props.value.type.bitwidth props.value.value))
        | OpCode.llvm Llvm.mlir__constant =>
          let props := op.getProperties! irCtx.raw (OpCode.llvm Llvm.mlir__constant)
          match props.value with
          | .integer attr =>
              Array.replicate numResults (some (.constant attr.type.bitwidth attr.value))
          | _ => pessimisticUpdates
        | OpCode.hw HW.constant =>
          let props := op.getProperties! irCtx.raw (OpCode.hw HW.constant)
          Array.replicate numResults
            (some (.constant props.value.type.bitwidth props.value.value))
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
