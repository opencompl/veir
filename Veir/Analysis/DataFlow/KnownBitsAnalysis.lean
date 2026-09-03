module

public import Veir.Analysis.DataFlow.Domains.KnownBitsDomain
public import Veir.Analysis.DataFlow.SparseForwardDataFlowAnalysis

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

private def foldOperands
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
  match foldOperands operation operands.toList with
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
  else
    match op.getOpType! irCtx.raw with
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

end KnownBitsAnalysis

/-- Sparse forward known-bits analysis for fixed-width integer SSA values. -/
def KnownBitsAnalysis : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new
    .knownBits
    KnownBitsAnalysis.kind
    KnownBitsAnalysis.transfer
    (entryState := fun value irCtx => KnownBitsAnalysis.unknownFor value irCtx.raw)

end Veir
