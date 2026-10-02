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
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
variable {opCode : Dialect}

section Rewriter.createRegion

variable {reg : RegionPtr}

attribute [local grind] Rewriter.createRegion

@[simp, grind =>, simp_getset]
theorem BlockPtr.getLastOp!_createRegion {block : BlockPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → block.getLastOp! ctx' = block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getFirstOp!_createRegion {block : BlockPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → block.getFirstOp! ctx' = block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getParent!_createRegion {block : BlockPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → block.getParent! ctx' = block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getNextBlock!_createRegion {block : BlockPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → block.getNextBlock! ctx' = block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getPrevBlock!_createRegion {block : BlockPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → block.getPrevBlock! ctx' = block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getFirstUse!_createRegion {block : BlockPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → block.getFirstUse! ctx' = block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getRegions!_createRegion {operation : OperationPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → operation.getRegions! ctx' = operation.getRegions! ctx := by
  simp only [OperationPtr.getRegions!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getAttributes!_createRegion {operation : OperationPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → operation.getAttributes! ctx' = operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getParent!_createRegion {operation : OperationPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → operation.getParent! ctx' = operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getPrevOp!_createRegion {operation : OperationPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → operation.getPrevOp! ctx' = operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNextOp!_createRegion {operation : OperationPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → operation.getNextOp! ctx' = operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getOpType!_createRegion {operation : OperationPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    operation.getOpType! ctx' = operation.getOpType! ctx := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getProperties!_createRegion {operation : OperationPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    operation.getProperties! ctx' opCode = operation.getProperties! ctx opCode := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumResults!_createRegion {operation : OperationPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    operation.getNumResults! ctx' = operation.getNumResults! ctx := by
  grind

@[simp, grind =>, simp_getset]
theorem OpResultPtr.getOwner!_createRegion {opResult : OpResultPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → opResult.getOwner! ctx' = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OpResultPtr.getIndex!_createRegion {opResult : OpResultPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → opResult.getIndex! ctx' = opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OpResultPtr.getFirstUse!_createRegion {opResult : OpResultPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → opResult.getFirstUse! ctx' = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OpResultPtr.getType!_createRegion {opResult : OpResultPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → opResult.getType! ctx' = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumOperands!_createRegion {operation : OperationPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    operation.getNumOperands! ctx' = operation.getNumOperands! ctx := by
  grind

@[simp, grind =>, simp_getset]
theorem OpOperandPtr.getValue!_createRegion {operand : OpOperandPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → operand.getValue! ctx' = operand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OpOperandPtr.getOwner!_createRegion {operand : OpOperandPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → operand.getOwner! ctx' = operand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OpOperandPtr.getBack!_createRegion {operand : OpOperandPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → operand.getBack! ctx' = operand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OpOperandPtr.getNextUse!_createRegion {operand : OpOperandPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → operand.getNextUse! ctx' = operand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getOperands!_createRegion {operation : OperationPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    operation.getOperands! ctx' = operation.getOperands! ctx := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumSuccessors!_createRegion {operation : OperationPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    operation.getNumSuccessors! ctx' = operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getValue!_createRegion {operand : BlockOperandPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → operand.getValue! ctx' = operand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getOwner!_createRegion {operand : BlockOperandPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → operand.getOwner! ctx' = operand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getBack!_createRegion {operand : BlockOperandPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → operand.getBack! ctx' = operand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getNextUse!_createRegion {operand : BlockOperandPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → operand.getNextUse! ctx' = operand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getSuccessor!_createRegion {operation : OperationPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    operation.getSuccessor! ctx' index = operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =>, simp_getset]
theorem OperationPtr.getSuccessors!_createRegion {operation : OperationPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    operation.getSuccessors! ctx' = operation.getSuccessors! ctx := by
  intro h
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_createRegion h,
    OperationPtr.getNumSuccessors!_createRegion h]

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumRegions!_createRegion {operation : OperationPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    operation.getNumRegions! ctx' = operation.getNumRegions! ctx := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getRegion!_createRegion {operation : OperationPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    operation.getRegion! ctx' idx = operation.getRegion! ctx idx := by
  grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtrPtr.get!_createRegion {operandPtr : BlockOperandPtrPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    operandPtr.get! ctx' = operandPtr.get! ctx := by
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getNumArguments!_createRegion {block : BlockPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    block.getNumArguments! ctx' = block.getNumArguments! ctx := by
  grind

@[simp, grind =>, simp_getset]
theorem BlockArgumentPtr.getOwner!_createRegion {blockArg : BlockArgumentPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → blockArg.getOwner! ctx' = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockArgumentPtr.getIndex!_createRegion {blockArg : BlockArgumentPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → blockArg.getIndex! ctx' = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_createRegion {blockArg : BlockArgumentPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → blockArg.getFirstUse! ctx' = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockArgumentPtr.getType!_createRegion {blockArg : BlockArgumentPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → blockArg.getType! ctx' = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[grind =>, simp_getset]
theorem RegionPtr.getFirstBlock!_createRegion {region : RegionPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → region.getFirstBlock! ctx' = if region = reg then none else region.getFirstBlock! ctx := by
  grind [Region.empty]

@[grind =>, simp_getset]
theorem RegionPtr.getLastBlock!_createRegion {region : RegionPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → region.getLastBlock! ctx' = if region = reg then none else region.getLastBlock! ctx := by
  grind [Region.empty]

@[grind =>, simp_getset]
theorem RegionPtr.getParent!_createRegion {region : RegionPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) → region.getParent! ctx' = if region = reg then none else region.getParent! ctx := by
  grind [Region.empty]

@[simp, grind =>, simp_getset]
theorem ValuePtr.getFirstUse!_createRegion {value : ValuePtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    value.getFirstUse! ctx' = value.getFirstUse! ctx := by
  grind

@[simp, grind =>, simp_getset]
theorem ValuePtr.getType!_createRegion {value : ValuePtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    value.getType! ctx' = value.getType! ctx := by
  grind

@[simp, grind =>, simp_getset]
theorem OpOperandPtrPtr.get!_createRegion {opOperandPtr : OpOperandPtrPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    opOperandPtr.get! ctx' = opOperandPtr.get! ctx := by
  grind

end Rewriter.createRegion
