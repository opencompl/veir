module

public import Veir.IR.OpInfo

/-!
# ControlFlowInterfaces

This file provides support for querying which operands are forwarded to a successor,
mapping those operands to successor block arguments, and selecting a successor from
known constant operands.
-/

namespace Veir

public section

/-- Whether this operation implements the branch operation interface. -/
def OperationPtr.isBranchLike {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (raw : IRContext OpInfo) : Bool :=
  (HasOpInfo.branchOpInterface? (op.getOpType! raw)).isSome

namespace BranchOpInterface

/-- Return the index of the true or false successor of a conditional branch. -/
def getConditionalSuccessorIndex (condition : Bool) : Nat :=
  if condition then 0 else 1

/--
Return the operands in the successor segment of an operation whose fixed operands
precede one operand segment per successor.
-/
def getSegmentedSuccessorOperands?
    (fixedOperandCount : Nat) (segmentSizes : Array Int) (operands : Array ValuePtr)
    (successorIndex : Nat) : Option SuccessorOperands := do
  let segmentIndex := fixedOperandCount + successorIndex
  let forwardedCountRaw ← segmentSizes[segmentIndex]?
  let forwardedCount := forwardedCountRaw.toNat
  let forwardedStart := fixedOperandCount +
    (segmentSizes.extract fixedOperandCount segmentIndex).foldl
      (init := 0) fun acc value => acc + value.toNat
  some {
    forwardedOperands := operands.extract forwardedStart (forwardedStart + forwardedCount)
  }

/--
  Return the operands passed to `successorIndex` of a branch operation.
-/
def getSuccessorOperands? {OpInfo : Type} [HasOpInfo OpInfo]
    (branchOp : OperationPtr) (successorIndex : Nat) (raw : IRContext OpInfo) :
    Option SuccessorOperands := do
  let opType := branchOp.getOpType! raw
  let some interface := HasOpInfo.branchOpInterface? opType | none
  interface.getSuccessorOperandsImpl? (branchOp.getProperties! raw opType)
    (branchOp.getOperands! raw) successorIndex

/-- Return the SSA value forwarded to a successor block argument. -/
def getSuccessorOperand? {OpInfo : Type} [HasOpInfo OpInfo]
    (branchOp : OperationPtr) (successorIndex blockArgumentIndex : Nat)
    (raw : IRContext OpInfo) : Option ValuePtr :=
  getSuccessorOperands? branchOp successorIndex raw >>= fun operands =>
    operands[blockArgumentIndex]?

/--
Return the index of the successor selected by the known constant operands of a
branch operation. An operand is `none` when its value is unknown. Returns `none`
when the operation is not a supported branch or a single successor cannot be
determined.
-/
def getSuccessorIndexForOperands? {OpInfo : Type} [HasOpInfo OpInfo]
    (branchOp : OperationPtr) (operands : Array (Option RuntimeValue))
    (raw : IRContext OpInfo) : Option Nat := do
  let opType := branchOp.getOpType! raw
  let some interface := HasOpInfo.branchOpInterface? opType | none
  let index ← interface.getSuccessorIndexForOperandsImpl?
    (branchOp.getProperties! raw opType) operands
  guard (index < branchOp.getNumSuccessors! raw)
  return index

/--
Return the successor selected by the known constant operands of a branch operation.
An operand is `none` when its value is unknown. Returns `none` when the operation is
not a supported branch or a single successor cannot be determined.
-/
def getSuccessorForOperands? {OpInfo : Type} [HasOpInfo OpInfo]
    (branchOp : OperationPtr) (operands : Array (Option RuntimeValue))
    (raw : IRContext OpInfo) : Option BlockPtr := do
  let index ← getSuccessorIndexForOperands? branchOp operands raw
  (branchOp.getSuccessors! raw)[index]?

end BranchOpInterface

end

end Veir
