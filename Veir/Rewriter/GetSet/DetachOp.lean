module

public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic
import all Veir.IR.Basic
import all Veir.IR.GetSet
import all Veir.Rewriter.LinkedList.GetSet
import Veir.Rewriter.WfRewriter.GetSetTactic

import all Veir.Rewriter.GetSet.DetachOperands
import all Veir.Rewriter.GetSet.DetachBlockOperands

public section

namespace Veir

variable {OpInfo} [HasOpInfo OpInfo]

-- Relate the getters to the fields of the underlying structures.
attribute [local grind _=_]
  OperationPtr.getNextOp!_def OperationPtr.getPrevOp!_def OperationPtr.getParent!_def
  OperationPtr.getAttributes!_def OpOperandPtr.getNextUse!_def OpOperandPtr.getBack!_def
  OpOperandPtr.getOwner!_def OpOperandPtr.getValue!_def BlockOperandPtr.getNextUse!_def
  BlockOperandPtr.getBack!_def BlockOperandPtr.getOwner!_def BlockOperandPtr.getValue!_def
  OpResultPtr.getType!_def OpResultPtr.getFirstUse!_def OpResultPtr.getOwner!_def
  BlockPtr.getParent!_def BlockPtr.getFirstUse!_def BlockPtr.getFirstOp!_def
  BlockPtr.getLastOp!_def BlockPtr.getNextBlock!_def BlockPtr.getPrevBlock!_def
  BlockArgumentPtr.getType!_def BlockArgumentPtr.getFirstUse!_def
  BlockArgumentPtr.getIndex!_def BlockArgumentPtr.getLoc!_def
  BlockArgumentPtr.getOwner!_def RegionPtr.getParent!_def RegionPtr.getFirstBlock!_def
  RegionPtr.getLastBlock!_def OpResultPtr.getIndex!_def
variable {ctx : IRContext OpInfo}
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
variable {opCode : Dialect}
section Rewriter.unsetParentAndNeighbors

attribute [local grind] Rewriter.unsetParentAndNeighbors

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_unsetParentAndNeighbors {block : BlockPtr} :
    block.getFirstUse! (Rewriter.unsetParentAndNeighbors ctx op' hIn) = block.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_unsetParentAndNeighbors {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.unsetParentAndNeighbors ctx op' hIn) = block.getPrevBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_unsetParentAndNeighbors {block : BlockPtr} :
    block.getNextBlock! (Rewriter.unsetParentAndNeighbors ctx op' hIn) = block.getNextBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_unsetParentAndNeighbors {block : BlockPtr} :
    block.getParent! (Rewriter.unsetParentAndNeighbors ctx op' hIn) = block.getParent! ctx := by
  grind

@[grind =, simp_getset]
theorem BlockPtr.getFirstOp!_unsetParentAndNeighbors {block : BlockPtr} :
    block.getFirstOp! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    block.getFirstOp! ctx := by
  grind

@[grind =, simp_getset]
theorem BlockPtr.getLastOp!_unsetParentAndNeighbors {block : BlockPtr} :
    block.getLastOp! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    block.getLastOp! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getPrevOp!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    if operation = op' then
      none
    else
      operation.getPrevOp! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getNextOp!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    if operation = op' then
      none
    else
      operation.getNextOp! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getParent!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getParent! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    if operation = op' then none else (operation.getParent! ctx) := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getOpType! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getProperties! (Rewriter.unsetParentAndNeighbors ctx op' hIn) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OpResultPtr.get!_unsetParentAndNeighbors {opResult : OpResultPtr} :
    opResult.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    opResult.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_unsetParentAndNeighbors {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_unsetParentAndNeighbors {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_unsetParentAndNeighbors {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_unsetParentAndNeighbors {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.unsetParentAndNeighbors ctx op' hIn) = operation.getNumOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OpOperandPtr.get!_unsetParentAndNeighbors {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) = opOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_unsetParentAndNeighbors {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_unsetParentAndNeighbors {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_unsetParentAndNeighbors {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_unsetParentAndNeighbors {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getOperands! (Rewriter.unsetParentAndNeighbors ctx op' hIn) = operation.getOperands! ctx := by
  simp only [Rewriter.unsetParentAndNeighbors]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem BlockOperandPtr.get!_unsetParentAndNeighbors {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_unsetParentAndNeighbors {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_unsetParentAndNeighbors {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_unsetParentAndNeighbors {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_unsetParentAndNeighbors {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.unsetParentAndNeighbors ctx op' hIn) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_unsetParentAndNeighbors {operation : OperationPtr} :
    operation.getRegion! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    operation.getRegion! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem BlockOperandPtrPtr.get!_unsetParentAndNeighbors {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_unsetParentAndNeighbors {block : BlockPtr} :
    block.getNumArguments! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem BlockArgumentPtr.get!_unsetParentAndNeighbors {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    blockArg.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_unsetParentAndNeighbors {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_unsetParentAndNeighbors {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_unsetParentAndNeighbors {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getLoc!_unsetParentAndNeighbors {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_unsetParentAndNeighbors {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
private theorem RegionPtr.get!_unsetParentAndNeighbors {region : RegionPtr} :
    region.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    region.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_unsetParentAndNeighbors {region : RegionPtr} :
    region.getParent! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_unsetParentAndNeighbors {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_unsetParentAndNeighbors {region : RegionPtr} :
    region.getLastBlock! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getFirstUse!_unsetParentAndNeighbors {value : ValuePtr} :
    value.getFirstUse! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getType!_unsetParentAndNeighbors {value : ValuePtr} :
    value.getType! (Rewriter.unsetParentAndNeighbors ctx op' hIn) =
    value.getType! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OpOperandPtrPtr.get!_unsetParentAndNeighbors {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.unsetParentAndNeighbors ctx op' hIn) = opOperandPtr.get! ctx := by
  grind

end Rewriter.unsetParentAndNeighbors
section Rewriter.detachOp

variable {op : OperationPtr}

attribute [local grind] Rewriter.detachOp

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_detachOp {block : BlockPtr} :
    block.getFirstUse! (Rewriter.detachOp ctx op' h₁ h₂ h₃) = block.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_detachOp {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.detachOp ctx op' h₁ h₂ h₃) = block.getPrevBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_detachOp {block : BlockPtr} :
    block.getNextBlock! (Rewriter.detachOp ctx op' h₁ h₂ h₃) = block.getNextBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_detachOp {block : BlockPtr} :
    block.getParent! (Rewriter.detachOp ctx op' h₁ h₂ h₃) = block.getParent! ctx := by
  grind

@[grind =, simp_getset]
theorem BlockPtr.getFirstOp!_detachOp {block : BlockPtr} :
    block.getFirstOp! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    if op'.getPrevOp! ctx = none ∧ block = op'.getParent! ctx then
      op'.getNextOp! ctx
    else
      block.getFirstOp! ctx := by
  grind

@[grind =, simp_getset]
theorem BlockPtr.getLastOp!_detachOp {block : BlockPtr} :
    block.getLastOp! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    if op'.getNextOp! ctx = none ∧ block = op'.getParent! ctx then
      op'.getPrevOp! ctx
    else
      block.getLastOp! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getPrevOp!_detachOp {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    if operation = op'.getNextOp! ctx then
      op'.getPrevOp! ctx
    else if operation = op' then
      none
    else
      operation.getPrevOp! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getNextOp!_detachOp {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    if operation = op'.getPrevOp! ctx then
      op'.getNextOp! ctx
    else if operation = op' then
      none
    else
      operation.getNextOp! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getParent!_detachOp {operation : OperationPtr} :
    operation.getParent! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    if operation = op' then none else (operation.getParent! ctx) := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_detachOp {operation : OperationPtr} :
    operation.getOpType! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_detachOp {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_detachOp {operation : OperationPtr} :
    operation.getProperties! (Rewriter.detachOp ctx op' h₁ h₂ h₃) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_detachOp {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OpResultPtr.get!_detachOp {opResult : OpResultPtr} :
    opResult.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    opResult.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_detachOp {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_detachOp {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_detachOp {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_detachOp {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_detachOp {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.detachOp ctx op' h₁ h₂ h₃) = operation.getNumOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OpOperandPtr.get!_detachOp {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) = opOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_detachOp {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_detachOp {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_detachOp {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_detachOp {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_detachOp {operation : OperationPtr} :
    operation.getOperands! (Rewriter.detachOp ctx op' h₁ h₂ h₃) = operation.getOperands! ctx := by
  simp only [Rewriter.detachOp]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_detachOp {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem BlockOperandPtr.get!_detachOp {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_detachOp {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_detachOp {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_detachOp {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_detachOp {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_detachOp {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.detachOp ctx op' h₁ h₂ h₃) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_detachOp {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_detachOp {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_detachOp {operation : OperationPtr} :
    operation.getRegion! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    operation.getRegion! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem BlockOperandPtrPtr.get!_detachOp {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_detachOp {block : BlockPtr} :
    block.getNumArguments! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem BlockArgumentPtr.get!_detachOp {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    blockArg.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_detachOp {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_detachOp {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_detachOp {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getLoc!_detachOp {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_detachOp {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
private theorem RegionPtr.get!_detachOp {region : RegionPtr} :
    region.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    region.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_detachOp {region : RegionPtr} :
    region.getParent! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_detachOp {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_detachOp {region : RegionPtr} :
    region.getLastBlock! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getFirstUse!_detachOp {value : ValuePtr} :
    value.getFirstUse! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getType!_detachOp {value : ValuePtr} :
    value.getType! (Rewriter.detachOp ctx op' h₁ h₂ h₃) =
    value.getType! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OpOperandPtrPtr.get!_detachOp {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.detachOp ctx op' h₁ h₂ h₃) = opOperandPtr.get! ctx := by
  grind

end Rewriter.detachOp
section Rewriter.detachOpIfAttached

variable {op : OperationPtr}

attribute [local grind] Rewriter.detachOpIfAttached

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_detachOpIfAttached {block : BlockPtr} :
    block.getFirstUse! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) = block.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_detachOpIfAttached {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) = block.getPrevBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_detachOpIfAttached {block : BlockPtr} :
    block.getNextBlock! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) = block.getNextBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_detachOpIfAttached {block : BlockPtr} :
    block.getParent! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) = block.getParent! ctx := by
  grind

@[grind =, simp_getset]
theorem BlockPtr.getFirstOp!_detachOpIfAttached {block : BlockPtr} :
    block.getFirstOp! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    if op'.getPrevOp! ctx = none ∧ block = op'.getParent! ctx then
      op'.getNextOp! ctx
    else
      block.getFirstOp! ctx := by
  grind

@[grind =, simp_getset]
theorem BlockPtr.getLastOp!_detachOpIfAttached {block : BlockPtr} :
    block.getLastOp! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    if op'.getNextOp! ctx = none ∧ block = op'.getParent! ctx then
      op'.getPrevOp! ctx
    else
      block.getLastOp! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getPrevOp!_detachOpIfAttached {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    if op'.getParent! ctx ≠ none ∧ operation = op'.getNextOp! ctx then
      op'.getPrevOp! ctx
    else if op'.getParent! ctx ≠ none ∧ operation = op' then
      none
    else
      operation.getPrevOp! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getNextOp!_detachOpIfAttached {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    if op'.getParent! ctx ≠ none ∧ operation = op'.getPrevOp! ctx then
      op'.getNextOp! ctx
    else if op'.getParent! ctx ≠ none ∧ operation = op' then
      none
    else
      operation.getNextOp! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getParent!_detachOpIfAttached {operation : OperationPtr} :
    operation.getParent! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    if operation = op' then none else (operation.getParent! ctx) := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_detachOpIfAttached {operation : OperationPtr} :
    operation.getOpType! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_detachOpIfAttached {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_detachOpIfAttached {operation : OperationPtr} :
    operation.getProperties! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_detachOpIfAttached {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OpResultPtr.get!_detachOpIfAttached {opResult : OpResultPtr} :
    opResult.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    opResult.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_detachOpIfAttached {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_detachOpIfAttached {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_detachOpIfAttached {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_detachOpIfAttached {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_detachOpIfAttached {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) = operation.getNumOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OpOperandPtr.get!_detachOpIfAttached {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) = opOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_detachOpIfAttached {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_detachOpIfAttached {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_detachOpIfAttached {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_detachOpIfAttached {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_detachOpIfAttached {operation : OperationPtr} :
    operation.getOperands! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) = operation.getOperands! ctx := by
  simp only [Rewriter.detachOpIfAttached]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_detachOpIfAttached {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem BlockOperandPtr.get!_detachOpIfAttached {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_detachOpIfAttached {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_detachOpIfAttached {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_detachOpIfAttached {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_detachOpIfAttached {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_detachOpIfAttached {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_detachOpIfAttached {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_detachOpIfAttached {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_detachOpIfAttached {operation : OperationPtr} :
    operation.getRegion! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    operation.getRegion! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem BlockOperandPtrPtr.get!_detachOpIfAttached {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_detachOpIfAttached {block : BlockPtr} :
    block.getNumArguments! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem BlockArgumentPtr.get!_detachOpIfAttached {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    blockArg.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_detachOpIfAttached {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_detachOpIfAttached {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_detachOpIfAttached {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getLoc!_detachOpIfAttached {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_detachOpIfAttached {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
private theorem RegionPtr.get!_detachOpIfAttached {region : RegionPtr} :
    region.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    region.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_detachOpIfAttached {region : RegionPtr} :
    region.getParent! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_detachOpIfAttached {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_detachOpIfAttached {region : RegionPtr} :
    region.getLastBlock! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getFirstUse!_detachOpIfAttached {value : ValuePtr} :
    value.getFirstUse! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getType!_detachOpIfAttached {value : ValuePtr} :
    value.getType! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) =
    value.getType! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OpOperandPtrPtr.get!_detachOpIfAttached {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.detachOpIfAttached ctx op' hCtx hOp) = opOperandPtr.get! ctx := by
  grind

end Rewriter.detachOpIfAttached
section Rewriter.eraseOp

variable {op : OperationPtr}

attribute [local grind] Rewriter.eraseOp

-- The theorem `BlockPtr.firstUse!_detachBlockOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_eraseOp {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.eraseOp ctx op hCtx hOp) = block.getPrevBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_eraseOp {block : BlockPtr} :
    block.getNextBlock! (Rewriter.eraseOp ctx op hCtx hOp) = block.getNextBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_eraseOp {block : BlockPtr} :
    block.getParent! (Rewriter.eraseOp ctx op hCtx hOp) = block.getParent! ctx := by
  grind

@[grind =, simp_getset]
theorem BlockPtr.getFirstOp!_eraseOp {block : BlockPtr} :
    block.getFirstOp! (Rewriter.eraseOp ctx op hCtx hOp) =
    if op.getPrevOp! ctx = none ∧ block = op.getParent! ctx then
      op.getNextOp! ctx
    else
      block.getFirstOp! ctx := by
  grind

@[grind =, simp_getset]
theorem BlockPtr.getLastOp!_eraseOp {block : BlockPtr} :
    block.getLastOp! (Rewriter.eraseOp ctx op hCtx hOp) =
    if op.getNextOp! ctx = none ∧ block = op.getParent! ctx then
      op.getPrevOp! ctx
    else
      block.getLastOp! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getPrevOp!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getPrevOp! (Rewriter.eraseOp ctx op hCtx hOp) =
    if op.getParent! ctx ≠ none ∧ operation = op.getNextOp! ctx then
      op.getPrevOp! ctx
    else if op.getParent! ctx ≠ none ∧ operation = op then
      none
    else
      operation.getPrevOp! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getNextOp!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getNextOp! (Rewriter.eraseOp ctx op hCtx hOp) =
    if op.getParent! ctx ≠ none ∧ operation = op.getPrevOp! ctx then
      op.getNextOp! ctx
    else if op.getParent! ctx ≠ none ∧ operation = op then
      none
    else
      operation.getNextOp! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getParent!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getParent! (Rewriter.eraseOp ctx op hCtx hOp) =
    if operation = op then none else (operation.getParent! ctx) := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getOpType! (Rewriter.eraseOp ctx op hCtx hOp) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getAttributes! (Rewriter.eraseOp ctx op hCtx hOp) =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getProperties! (Rewriter.eraseOp ctx op hCtx hOp) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getNumResults! (Rewriter.eraseOp ctx op hCtx hOp) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =, simp_getset]
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

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getOperands! (Rewriter.eraseOp ctx op hCtx hOp) = operation.getOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getNumSuccessors! (Rewriter.eraseOp ctx op hCtx hOp) =
    operation.getNumSuccessors! ctx := by
  grind

-- The theorem `BlockOperandPtr.get!_eraseOp` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getSuccessor! (Rewriter.eraseOp ctx op hCtx hOp) index =
    operation.getSuccessor! ctx index := by
  grind [_=_ OperationPtr.getSuccessor!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getSuccessors! (Rewriter.eraseOp ctx op hCtx hOp) =
    operation.getSuccessors! ctx := by
  grind [_=_ OperationPtr.getSuccessors!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getNumRegions! (Rewriter.eraseOp ctx op hCtx hOp) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_eraseOp {operation : OperationPtr} :
    operation.InBounds (Rewriter.eraseOp ctx op hCtx hOp) →
    operation.getRegion! (Rewriter.eraseOp ctx op hCtx hOp) idx =
    operation.getRegion! ctx idx := by
  grind

-- The theorem `BlockOperandPtrPtr.get!_eraseOp` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_eraseOp {block : BlockPtr} :
    block.getNumArguments! (Rewriter.eraseOp ctx op hCtx hOp) =
    block.getNumArguments! ctx := by
  grind

-- The theorem `BlockArgumentPtr.get!_eraseOp` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_eraseOp {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.eraseOp ctx op hCtx hOp) =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_eraseOp {region : RegionPtr} :
    region.getLastBlock! (Rewriter.eraseOp ctx op hCtx hOp) =
    region.getLastBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_eraseOp {region : RegionPtr} :
    region.getParent! (Rewriter.eraseOp ctx op hCtx hOp) =
    region.getParent! ctx := by
  grind

-- The theorem `ValuePtr.getFirstUse!_eraseOp` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =, simp_getset]
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
