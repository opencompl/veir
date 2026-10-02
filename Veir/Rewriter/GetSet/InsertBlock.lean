module

public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic
import Veir.Rewriter.WfRewriter.GetSetTactic

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
 -   * OperationPtr.getOpType!
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

fold_field_getters_in_grind

variable {OpInfo} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}
section Rewriter.insertBlock

unseal Rewriter.insertBlock

attribute [local grind] Rewriter.insertBlock

@[simp, simp_getset]
theorem BlockPtr.getFirstUse!_insertBlock {block : BlockPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → block.getFirstUse! newCtx = block.getFirstUse! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockPtr.getFirstUse!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, (block.getFirstUse! newCtx)

@[simp_getset]
theorem BlockPtr.getPrevBlock!_insertBlock {block : BlockPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → block.getPrevBlock! newCtx = if block = ip.next then some newBlock else if block = newBlock then ip.prev! ctx else block.getPrevBlock! ctx := by
  simp only [Rewriter.insertBlock]
  grind [cases BlockInsertPoint]

grind_pattern BlockPtr.getPrevBlock!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, (block.getPrevBlock! newCtx)

@[simp_getset]
theorem BlockPtr.getNextBlock!_insertBlock {block : BlockPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → block.getNextBlock! newCtx = if block = ip.prev! ctx then some newBlock else if block = newBlock then ip.next else block.getNextBlock! ctx := by
  simp only [Rewriter.insertBlock]
  grind [cases BlockInsertPoint]

grind_pattern BlockPtr.getNextBlock!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, (block.getNextBlock! newCtx)

@[simp_getset]
theorem BlockPtr.getParent!_insertBlock {block : BlockPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → block.getParent! newCtx = if block = newBlock then ip.region! ctx else block.getParent! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockPtr.getParent!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, (block.getParent! newCtx)

@[simp, simp_getset]
theorem BlockPtr.getFirstOp!_insertBlock {block : BlockPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → block.getFirstOp! newCtx = block.getFirstOp! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockPtr.getFirstOp!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, (block.getFirstOp! newCtx)

@[simp, simp_getset]
theorem BlockPtr.getLastOp!_insertBlock {block : BlockPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → block.getLastOp! newCtx = block.getLastOp! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockPtr.getLastOp!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, (block.getLastOp! newCtx)

@[simp, simp_getset]
theorem OperationPtr.getRegions!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → operation.getRegions! newCtx = operation.getRegions! ctx := by
  simp only [OperationPtr.getRegions!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getRegions!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getRegions! newCtx

@[simp, simp_getset]
theorem OperationPtr.getAttributes!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → operation.getAttributes! newCtx = operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getAttributes!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getAttributes! newCtx

@[simp, simp_getset]
theorem OperationPtr.getParent!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → operation.getParent! newCtx = operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getParent!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getParent! newCtx

@[simp, simp_getset]
theorem OperationPtr.getPrevOp!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → operation.getPrevOp! newCtx = operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getPrevOp!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getPrevOp! newCtx

@[simp, simp_getset]
theorem OperationPtr.getNextOp!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → operation.getNextOp! newCtx = operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getNextOp!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getNextOp! newCtx

@[simp, simp_getset]
theorem OperationPtr.getOpType!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getOpType! newCtx = operation.getOpType! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getOpType!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getOpType! newCtx

@[simp, simp_getset]
theorem OperationPtr.getNumResults!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getNumResults! newCtx = operation.getNumResults! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getNumResults!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getNumResults! newCtx

@[simp, simp_getset]
theorem OpResultPtr.getOwner!_insertBlock {opResult : OpResultPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → opResult.getOwner! newCtx = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OpResultPtr.getOwner!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, opResult.getOwner! newCtx

@[simp, simp_getset]
theorem OpResultPtr.getIndex!_insertBlock {opResult : OpResultPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → opResult.getIndex! newCtx = opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OpResultPtr.getIndex!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, opResult.getIndex! newCtx

@[simp, simp_getset]
theorem OpResultPtr.getFirstUse!_insertBlock {opResult : OpResultPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → opResult.getFirstUse! newCtx = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OpResultPtr.getFirstUse!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, opResult.getFirstUse! newCtx

@[simp, simp_getset]
theorem OpResultPtr.getType!_insertBlock {opResult : OpResultPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → opResult.getType! newCtx = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OpResultPtr.getType!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, opResult.getType! newCtx

@[simp, simp_getset]
theorem OperationPtr.getNumOperands!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getNumOperands!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getNumOperands! newCtx

@[simp, simp_getset]
theorem OpOperandPtr.getValue!_insertBlock {operand : OpOperandPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → operand.getValue! newCtx = operand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OpOperandPtr.getValue!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.getValue! newCtx

@[simp, simp_getset]
theorem OpOperandPtr.getOwner!_insertBlock {operand : OpOperandPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → operand.getOwner! newCtx = operand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OpOperandPtr.getOwner!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.getOwner! newCtx

@[simp, simp_getset]
theorem OpOperandPtr.getBack!_insertBlock {operand : OpOperandPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → operand.getBack! newCtx = operand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OpOperandPtr.getBack!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.getBack! newCtx

@[simp, simp_getset]
theorem OpOperandPtr.getNextUse!_insertBlock {operand : OpOperandPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → operand.getNextUse! newCtx = operand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OpOperandPtr.getNextUse!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.getNextUse! newCtx

@[simp, simp_getset]
theorem OperationPtr.getOperands!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getOperands! newCtx = operation.getOperands! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getOperands!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getOperands! newCtx

@[simp, simp_getset]
theorem OperationPtr.getNumSuccessors!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getNumSuccessors! newCtx = operation.getNumSuccessors! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getNumSuccessors!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getNumSuccessors! newCtx

@[simp, simp_getset]
theorem BlockOperandPtr.getValue!_insertBlock {operand : BlockOperandPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → operand.getValue! newCtx = operand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockOperandPtr.getValue!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.getValue! newCtx

@[simp, simp_getset]
theorem BlockOperandPtr.getOwner!_insertBlock {operand : BlockOperandPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → operand.getOwner! newCtx = operand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockOperandPtr.getOwner!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.getOwner! newCtx

@[simp, simp_getset]
theorem BlockOperandPtr.getBack!_insertBlock {operand : BlockOperandPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → operand.getBack! newCtx = operand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockOperandPtr.getBack!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.getBack! newCtx

@[simp, simp_getset]
theorem BlockOperandPtr.getNextUse!_insertBlock {operand : BlockOperandPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → operand.getNextUse! newCtx = operand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockOperandPtr.getNextUse!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.getNextUse! newCtx

@[simp, simp_getset]
theorem OperationPtr.getSuccessor!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getSuccessor! newCtx index = operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

grind_pattern OperationPtr.getSuccessor!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getSuccessor! newCtx index

@[simp, simp_getset]
theorem OperationPtr.getSuccessors!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getSuccessors! newCtx = operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

grind_pattern OperationPtr.getSuccessors!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getSuccessors! newCtx

@[simp, simp_getset]
theorem OperationPtr.getNumRegions!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getNumRegions! newCtx = operation.getNumRegions! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getNumRegions!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getNumRegions! newCtx

@[simp, simp_getset]
theorem OperationPtr.getRegion!_insertBlock {operation : OperationPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getRegion! newCtx = operation.getRegion! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OperationPtr.getRegion!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getRegion! newCtx

@[simp, simp_getset]
theorem BlockOperandPtrPtr.get!_insertBlock {operandPtr : BlockOperandPtrPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operandPtr.get! newCtx = operandPtr.get! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockOperandPtrPtr.get!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, operandPtr.get! newCtx

@[simp, simp_getset]
theorem BlockPtr.getNumArguments!_insertBlock {block : BlockPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    block.getNumArguments! newCtx = block.getNumArguments! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockPtr.getNumArguments!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, block.getNumArguments! newCtx

@[simp, simp_getset]
theorem BlockArgumentPtr.getOwner!_insertBlock {blockArg : BlockArgumentPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → blockArg.getOwner! newCtx = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockArgumentPtr.getOwner!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, blockArg.getOwner! newCtx

@[simp, simp_getset]
theorem BlockArgumentPtr.getIndex!_insertBlock {blockArg : BlockArgumentPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → blockArg.getIndex! newCtx = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockArgumentPtr.getIndex!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, blockArg.getIndex! newCtx

@[simp, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_insertBlock {blockArg : BlockArgumentPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → blockArg.getFirstUse! newCtx = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockArgumentPtr.getFirstUse!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, blockArg.getFirstUse! newCtx

@[simp, simp_getset]
theorem BlockArgumentPtr.getType!_insertBlock {blockArg : BlockArgumentPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → blockArg.getType! newCtx = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  simp only [Rewriter.insertBlock]
  grind

grind_pattern BlockArgumentPtr.getType!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, blockArg.getType! newCtx

@[simp_getset]
theorem RegionPtr.getFirstBlock!_insertBlock {region : RegionPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → region.getFirstBlock! newCtx = if ip.region! ctx = region ∧ ip.prev! ctx = none then some newBlock else region.getFirstBlock! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern RegionPtr.getFirstBlock!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, (region.getFirstBlock! newCtx)

@[simp_getset]
theorem RegionPtr.getLastBlock!_insertBlock {region : RegionPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → region.getLastBlock! newCtx = if ip.region! ctx = region ∧ ip.next = none then some newBlock else region.getLastBlock! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern RegionPtr.getLastBlock!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, (region.getLastBlock! newCtx)

@[simp, simp_getset]
theorem RegionPtr.getParent!_insertBlock {region : RegionPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx → region.getParent! newCtx = region.getParent! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern RegionPtr.getParent!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, (region.getParent! newCtx)

@[simp, simp_getset]
theorem ValuePtr.getFirstUse!_insertBlock {value : ValuePtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    value.getFirstUse! newCtx = value.getFirstUse! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern ValuePtr.getFirstUse!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, value.getFirstUse! newCtx

@[simp, simp_getset]
theorem ValuePtr.getType!_insertBlock {value : ValuePtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    value.getType! newCtx = value.getType! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern ValuePtr.getType!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, value.getType! newCtx

@[simp, simp_getset]
theorem OpOperandPtrPtr.get!_insertBlock {opOperandPtr : OpOperandPtrPtr} :
    Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    opOperandPtr.get! newCtx = opOperandPtr.get! ctx := by
  simp only [Rewriter.insertBlock]
  grind

grind_pattern OpOperandPtrPtr.get!_insertBlock =>
  Rewriter.insertBlock ctx newBlock ip h₁ h₂ h₃, some newCtx, opOperandPtr.get! newCtx

end Rewriter.insertBlock

end Veir
