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

def kind : AnalysisKind :=
  .knownBits

/-- Read the current known-bits fact attached to an SSA value. -/
def getKnownBits (value : ValuePtr) (dfCtx : DataFlowContext) : KnownBitsLattice :=
  SparseFact.getElement .knownBits value dfCtx

/-- The pessimistic value for a typed integer retains its width but knows no bits. -/
def unknownFor (value : ValuePtr) (irCtx : IRContext OpCode) : KnownBitsLattice :=
  match (value.getType! irCtx).val with
  | .integerType intType => .unknown intType.bitwidth
  | _ => ⊤

private def constant (attr : IntegerAttr) : KnownBitsLattice :=
  .constant attr.type.bitwidth attr.value

private def runtimeValueOfExactKnownBits : KnownBitsLattice → Option RuntimeValue
  | .known bits =>
      if bits.zero = ~~~bits.one then
        some (.int bits.bitwidth (.val bits.one))
      else
        none
  | _ => none

private def updateOfFoldResult
    (result : FoldResult)
    (resultType : TypeAttr)
    (operands : Array KnownBitsLattice) : Option KnownBitsLattice :=
  match resultType.val with
  | .integerType intType =>
      match result with
      | .useOperand index => some (operands[index]?.getD ⊤)
      | .useConstant (.int bitwidth (.val value)) =>
          if h : bitwidth = intType.bitwidth then
            let value := value.cast h
            some (.known { bitwidth := intType.bitwidth, zero := ~~~value, one := value })
          else
            some ⊤
      | .useConstant _ => some ⊤
  | _ => none

private def foldAbstractOperands
    (operation : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice)
    (operands : List KnownBitsLattice) : Option KnownBitsLattice :=
  match operands with
  | [] => none
  | first :: rest =>
      if first = ⊥ then
        none
      else
        rest.foldl
          (fun accumulated operand =>
            match accumulated with
            | none => none
            | some value => if operand = ⊥ then none else some (operation value operand))
          (some first)

private def transferBitwise
    (operation : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice)
    (numResults : Nat)
    (operands : Array KnownBitsLattice) : Array (Option KnownBitsLattice) :=
  match foldAbstractOperands operation operands.toList with
  | some result => Array.replicate numResults (some result)
  | none => Array.replicate numResults none

/--
Infer known bits for one operation. Bottom operands cause the transfer to wait for
more information; unsupported integer results receive a width-aware unknown value.
-/
def transfer
    (op : OperationPtr)
    (operands : Array KnownBitsLattice)
    (irCtx : WfIRContext OpCode) : Array (Option KnownBitsLattice) :=
  let numResults := op.getNumResults! irCtx.raw
  let pessimisticUpdates := (op.getResults! irCtx.raw).map fun result =>
    match (result.getType! irCtx.raw).val with
    | .integerType intType => some (.unknown intType.bitwidth)
    | _ => none

  if op.getNumRegions! irCtx.raw ≠ 0 then
    pessimisticUpdates
  else if operands.any (· = ⊥) then
    Array.replicate numResults none
  else
    let exactOperands := operands.map runtimeValueOfExactKnownBits
    if opInBounds : op.InBounds irCtx.raw then
      match op.foldsTo irCtx opInBounds exactOperands with
      | some results =>
          results.zipIdx.map fun (result, index) =>
            match (op.getResultTypes irCtx.raw opInBounds)[index]? with
            | some resultType => updateOfFoldResult result resultType operands
            | none => some ⊤
      | none =>
          match op.getOpType irCtx.raw opInBounds with
          | OpCode.arith Arith.constant =>
            let props := op.getProperties! irCtx.raw (OpCode.arith Arith.constant)
            Array.replicate numResults (some (constant props.value))
          | OpCode.llvm Llvm.mlir__constant =>
            let props := op.getProperties! irCtx.raw (OpCode.llvm Llvm.mlir__constant)
            match props.value with
            | .integer attr => Array.replicate numResults (some (constant attr))
            | _ => pessimisticUpdates
          | OpCode.hw HW.constant =>
            let props := op.getProperties! irCtx.raw (OpCode.hw HW.constant)
            Array.replicate numResults (some (constant props.value))
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
    else
      pessimisticUpdates

end KnownBitsAnalysis

/-- Sparse forward known-bits analysis for fixed-width integer SSA values. -/
def KnownBitsAnalysis : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new
    .knownBits
    KnownBitsAnalysis.kind
    KnownBitsAnalysis.transfer
    (entryState := fun value irCtx => KnownBitsAnalysis.unknownFor value irCtx.raw)

end Veir
