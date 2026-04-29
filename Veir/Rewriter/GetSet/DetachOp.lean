module

public import Veir.IR.Basic
public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic

import Veir.Rewriter.LinkedList.GetSet
import Veir.ForLean
import Veir.IR.DeallocLemmas
import Veir.Rewriter.GetSet.DetachOperands
import Veir.Rewriter.GetSet.DetachBlockOperands

public section

/-
 - The getters we consider are:
 - * BlockPtr.get! optionally replaced by the following special cases:
 -   * Block.firstUse
 -   * Block.prev
 -   * Block.next
 -   * Block.parent
 -   * Block.firstOp
 -   * Block.lastOp
 - * OperationPtr.get! optionally replaced by the following special cases:
 -   * Operation.prev
 -   * Operation.next
 -   * Operation.parent
 -   * Operation.opType
 -   * Operation.attrs
 - * OperationPtr.getProperties!
 - * OperationPtr.getNumResults!
 - * OpResultPtr.get!
 - * OperationPtr.getNumOperands!
 - * OpOperandPtr.get! optionally replaced by the following special case:
 - * OperationPtr.getOperands!
 - * OperationPtr.getNumSuccessors!
 - * BlockOperandPtr.get!
 - * OperationPtr.getSuccessor!
 - * OperationPtr.getSuccessors!
 - * OperationPtr.getNumRegions!
 - * OperationPtr.getRegion!
 - * BlockOperandPtrPtr.get!
 - * BlockPtr.getNumArguments!
 - * BlockArgumentPtr.get!
 - * RegionPtr.get! with optionally special cases for:
 -   * firstBlock
 -   * lastBlock
 -   * parent
 - * ValuePtr.getFirstUse!
 - * ValuePtr.getType!
 - * OpOperandPtrPtr.get!
 -/

namespace Veir

variable {OpInfo} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}
section Rewriter.unsetParentAndNeighbors

attribute [local grind] Rewriter.unsetParentAndNeighbors

@[simp, grind =]
theorem BlockPtr.firstUse!_unsetParentAndNeighbors {block : BlockPtr} :
    (block.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).firstUse = (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_unsetParentAndNeighbors {block : BlockPtr} :
    (block.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).prev = (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_unsetParentAndNeighbors {block : BlockPtr} :
    (block.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).next = (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_unsetParentAndNeighbors {block : BlockPtr} :
    (block.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).parent = (block.get! ctx).parent := by
  grind

@[grind =]
theorem BlockPtr.firstOp!_unsetParentAndNeighbors {block : BlockPtr} :
    (block.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[grind =]
theorem BlockPtr.lastOp!_unsetParentAndNeighbors {block : BlockPtr} :
    (block.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[grind =]
theorem OperationPtr.prev!_unsetParentAndNeighbors {operation : OperationPtr} :
    (operation.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).prev =
    if operation = op' then
      none
    else
      (operation.get! ctx).prev := by
  grind

@[grind =]
theorem OperationPtr.next!_unsetParentAndNeighbors {operation : OperationPtr} :
    (operation.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).next =
    if operation = op' then
      none
    else
      (operation.get! ctx).next := by
  grind

@[grind =]
theorem OperationPtr.parent!_unsetParentAndNeighbors {operation : OperationPtr} :
    (operation.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).parent =
    if operation = op' then none else (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_unsetParentAndNeighbors {operation : OperationPtr} :
    (operation.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_unsetParentAndNeighbors {operation : OperationPtr} :
    (operation.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getProperties! (Rewriter.unsetParentAndNeighbors ctx op' hIn) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_unsetParentAndNeighbors {opResult : OpResultPtr} :
    opResult.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.unsetParentAndNeighbors ctx op' hIn) = operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_unsetParentAndNeighbors {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) = opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getOperands! (Rewriter.unsetParentAndNeighbors ctx op' hIn) = operation.getOperands! ctx := by
  simp only [Rewriter.unsetParentAndNeighbors]
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_unsetParentAndNeighbors {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.unsetParentAndNeighbors ctx op' hIn) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getRegion! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    operation.getRegion! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_unsetParentAndNeighbors {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_unsetParentAndNeighbors {block : BlockPtr} :
    block.getNumArguments! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_unsetParentAndNeighbors {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_unsetParentAndNeighbors {region : RegionPtr} :
    region.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_unsetParentAndNeighbors {value : ValuePtr} :
    value.getFirstUse! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_unsetParentAndNeighbors {value : ValuePtr} :
    value.getType! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_unsetParentAndNeighbors {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) = opOperandPtr.get! ctx := by
  grind

end Rewriter.unsetParentAndNeighbors
section Rewriter.detachOp

variable {op : OperationPtr}

attribute [local grind] Rewriter.detachOp

@[simp, grind =]
theorem BlockPtr.firstUse!_detachOp {block : BlockPtr} :
    (block.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).firstUse = (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_detachOp {block : BlockPtr} :
    (block.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).prev = (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_detachOp {block : BlockPtr} :
    (block.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).next = (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_detachOp {block : BlockPtr} :
    (block.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).parent = (block.get! ctx).parent := by
  grind

@[grind =]
theorem BlockPtr.firstOp!_detachOp {block : BlockPtr} :
    (block.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).firstOp =
    if (op'.get! ctx).prev = none ∧ block = (op'.get! ctx).parent then
      (op'.get! ctx).next
    else
      (block.get! ctx).firstOp := by
  grind

@[grind =]
theorem BlockPtr.lastOp!_detachOp {block : BlockPtr} :
    (block.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).lastOp =
    if (op'.get! ctx).next = none ∧ block = (op'.get! ctx).parent then
      (op'.get! ctx).prev
    else
      (block.get! ctx).lastOp := by
  grind

@[grind =]
theorem OperationPtr.prev!_detachOp {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).prev =
    if operation = (op'.get! ctx).next then
      (op'.get! ctx).prev
    else if operation = op' then
      none
    else
      (operation.get! ctx).prev := by
  grind

@[grind =]
theorem OperationPtr.next!_detachOp {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).next =
    if operation = (op'.get! ctx).prev then
      (op'.get! ctx).next
    else if operation = op' then
      none
    else
      (operation.get! ctx).next := by
  grind

@[grind =]
theorem OperationPtr.parent!_detachOp {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).parent =
    if operation = op' then none else (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_detachOp {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_detachOp {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_detachOp {operation : OperationPtr} :
    operation.getProperties! (Rewriter.detachOp ctx op' h₁ h₂ h₃) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_detachOp {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_detachOp {opResult : OpResultPtr} :
    opResult.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_detachOp {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.detachOp ctx op' h₁ h₂ h₃) = operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_detachOp {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) = opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_detachOp {operation : OperationPtr} :
    operation.getOperands! (Rewriter.detachOp ctx op' h₁ h₂ h₃) = operation.getOperands! ctx := by
  simp only [Rewriter.detachOp]
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_detachOp {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_detachOp {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_detachOp {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.detachOp ctx op' h₁ h₂ h₃) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_detachOp {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_detachOp {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_detachOp {operation : OperationPtr} :
    operation.getRegion! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    operation.getRegion! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_detachOp {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_detachOp {block : BlockPtr} :
    block.getNumArguments! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_detachOp {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_detachOp {region : RegionPtr} :
    region.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_detachOp {value : ValuePtr} :
    value.getFirstUse! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_detachOp {value : ValuePtr} :
    value.getType! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_detachOp {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) = opOperandPtr.get! ctx := by
  grind

end Rewriter.detachOp
section Rewriter.detachOpIfAttached

variable {op : OperationPtr}

attribute [local grind] Rewriter.detachOpIfAttached

@[simp, grind =]
theorem BlockPtr.firstUse!_detachOpIfAttached {block : BlockPtr} :
    (block.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).firstUse = (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_detachOpIfAttached {block : BlockPtr} :
    (block.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).prev = (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_detachOpIfAttached {block : BlockPtr} :
    (block.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).next = (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_detachOpIfAttached {block : BlockPtr} :
    (block.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).parent = (block.get! ctx).parent := by
  grind

@[grind =]
theorem BlockPtr.firstOp!_detachOpIfAttached {block : BlockPtr} :
    (block.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).firstOp =
    if (op'.get! ctx).prev = none ∧ block = (op'.get! ctx).parent then
      (op'.get! ctx).next
    else
      (block.get! ctx).firstOp := by
  grind

@[grind =]
theorem BlockPtr.lastOp!_detachOpIfAttached {block : BlockPtr} :
    (block.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).lastOp =
    if (op'.get! ctx).next = none ∧ block = (op'.get! ctx).parent then
      (op'.get! ctx).prev
    else
      (block.get! ctx).lastOp := by
  grind

@[grind =]
theorem OperationPtr.prev!_detachOpIfAttached {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).prev =
    if (op'.get! ctx).parent ≠ none ∧ operation = (op'.get! ctx).next then
      (op'.get! ctx).prev
    else if (op'.get! ctx).parent ≠ none ∧ operation = op' then
      none
    else
      (operation.get! ctx).prev := by
  grind

@[grind =]
theorem OperationPtr.next!_detachOpIfAttached {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).next =
    if (op'.get! ctx).parent ≠ none ∧ operation = (op'.get! ctx).prev then
      (op'.get! ctx).next
    else if (op'.get! ctx).parent ≠ none ∧ operation = op' then
      none
    else
      (operation.get! ctx).next := by
  grind

@[grind =]
theorem OperationPtr.parent!_detachOpIfAttached {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).parent =
    if operation = op' then none else (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_detachOpIfAttached {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_detachOpIfAttached {operation : OperationPtr} :
    (operation.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_detachOpIfAttached {operation : OperationPtr} :
    operation.getProperties! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_detachOpIfAttached {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_detachOpIfAttached {opResult : OpResultPtr} :
    opResult.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_detachOpIfAttached {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) = operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_detachOpIfAttached {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) = opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_detachOpIfAttached {operation : OperationPtr} :
    operation.getOperands! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) = operation.getOperands! ctx := by
  simp only [Rewriter.detachOpIfAttached]
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_detachOpIfAttached {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_detachOpIfAttached {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_detachOpIfAttached {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_detachOpIfAttached {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_detachOpIfAttached {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_detachOpIfAttached {operation : OperationPtr} :
    operation.getRegion! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    operation.getRegion! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_detachOpIfAttached {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_detachOpIfAttached {block : BlockPtr} :
    block.getNumArguments! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_detachOpIfAttached {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_detachOpIfAttached {region : RegionPtr} :
    region.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_detachOpIfAttached {value : ValuePtr} :
    value.getFirstUse! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_detachOpIfAttached {value : ValuePtr} :
    value.getType! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_detachOpIfAttached {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) = opOperandPtr.get! ctx := by
  grind

end Rewriter.detachOpIfAttached
section Rewriter.eraseOp

variable {op : OperationPtr}

attribute [local grind] Rewriter.eraseOp

-- The theorem `BlockPtr.firstUse!_detachBlockOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =]
theorem BlockPtr.prev!_eraseOp {block : BlockPtr} :
    (block.get! (Rewriter.eraseOp ctx op hCtx hOp)).prev = (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_eraseOp {block : BlockPtr} :
    (block.get! (Rewriter.eraseOp ctx op hCtx hOp)).next = (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_eraseOp {block : BlockPtr} :
    (block.get! (Rewriter.eraseOp ctx op hCtx hOp)).parent = (block.get! ctx).parent := by
  grind

@[grind =]
theorem BlockPtr.firstOp!_eraseOp {block : BlockPtr} :
    (block.get! (Rewriter.eraseOp ctx op hCtx hOp)).firstOp =
    if (op.get! ctx).prev = none ∧ block = (op.get! ctx).parent then
      (op.get! ctx).next
    else
      (block.get! ctx).firstOp := by
  grind

@[grind =]
theorem BlockPtr.lastOp!_eraseOp {block : BlockPtr} :
    (block.get! (Rewriter.eraseOp ctx op hCtx hOp)).lastOp =
    if (op.get! ctx).next = none ∧ block = (op.get! ctx).parent then
      (op.get! ctx).prev
    else
      (block.get! ctx).lastOp := by
  grind

@[grind =]
theorem OperationPtr.prev!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    (operation.get! (Rewriter.eraseOp ctx op hCtx hOp)).prev =
    if (op.get! ctx).parent ≠ none ∧ operation = (op.get! ctx).next then
      (op.get! ctx).prev
    else if (op.get! ctx).parent ≠ none ∧ operation = op then
      none
    else
      (operation.get! ctx).prev := by
  grind

@[grind =]
theorem OperationPtr.next!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    (operation.get! (Rewriter.eraseOp ctx op hCtx hOp)).next =
    if (op.get! ctx).parent ≠ none ∧ operation = (op.get! ctx).prev then
      (op.get! ctx).next
    else if (op.get! ctx).parent ≠ none ∧ operation = op then
      none
    else
      (operation.get! ctx).next := by
  grind

@[grind =]
theorem OperationPtr.parent!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    (operation.get! (Rewriter.eraseOp ctx op hCtx hOp)).parent =
    if operation = op then none else (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    (operation.get! (Rewriter.eraseOp ctx op hCtx hOp)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    (operation.get! (Rewriter.eraseOp ctx op hCtx hOp)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getProperties! (Rewriter.eraseOp ctx op hCtx hOp) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getNumOperands! (Rewriter.eraseOp ctx op hCtx hOp) =
    operation.getNumOperands! ctx := by
  grind

-- The theorem `OpResultPtr.get!_eraseOp` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

-- The theorem `OpOperandPtr.get!_eraseOp` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.OpChain` directly.

@[simp, grind =]
theorem OperationPtr.getOperands!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getOperands! (Rewriter.eraseOp ctx op hCtx hOp) = operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getNumSuccessors! (Rewriter.eraseOp ctx op hCtx hOp) =
    operation.getNumSuccessors! ctx := by
  grind

-- The theorem `BlockOperandPtr.get!_eraseOp` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =]
theorem OperationPtr.getSuccessor!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getSuccessor! (Rewriter.eraseOp ctx op hCtx hOp) index =
    operation.getSuccessor! ctx index := by
  grind [_=_ OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getSuccessors! (Rewriter.eraseOp ctx op hCtx hOp) =
    operation.getSuccessors! ctx := by
  grind [_=_ OperationPtr.getSuccessors!_def]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getNumRegions! (Rewriter.eraseOp ctx op hCtx hOp) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getRegion! (Rewriter.eraseOp ctx op hCtx hOp) idx =
    operation.getRegion! ctx idx := by
  grind

-- The theorem `BlockOperandPtrPtr.get!_eraseOp` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =]
theorem BlockPtr.getNumArguments!_eraseOp {block : BlockPtr} :
    block.getNumArguments! (Rewriter.eraseOp ctx op hCtx hOp) =
    block.getNumArguments! ctx := by
  grind

-- The theorem `BlockArgumentPtr.get!_eraseOp` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =]
theorem RegionPtr.firstBlock!_eraseOp {region : RegionPtr} :
    (region.get! (Rewriter.eraseOp ctx op hCtx hOp)).firstBlock =
    (region.get! ctx).firstBlock := by
  grind

@[simp, grind =]
theorem RegionPtr.lastBlock!_eraseOp {region : RegionPtr} :
    (region.get! (Rewriter.eraseOp ctx op hCtx hOp)).lastBlock =
    (region.get! ctx).lastBlock := by
  grind

@[simp, grind =]
theorem RegionPtr.parent!_eraseOp {region : RegionPtr} :
    (region.get! (Rewriter.eraseOp ctx op hCtx hOp)).parent =
    (region.get! ctx).parent := by
  grind

-- The theorem `ValuePtr.getFirstUse!_eraseOp` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =]
theorem ValuePtr.getType!_eraseOp {value : ValuePtr} :
    value.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    value.getType! (Rewriter.eraseOp ctx op hCtx hOp) =
    value.getType! ctx := by
  grind

-- The theorem `OpOperandPtr.get!_eraseOp` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

end Rewriter.eraseOp

end Veir
