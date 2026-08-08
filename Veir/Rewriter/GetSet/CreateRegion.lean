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

variable {OpInfo} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
variable {opCode : Dialect}

section Rewriter.createRegion

variable {reg : RegionPtr}

attribute [local grind] Rewriter.createRegion

@[simp, grind =>, simp_getset]
theorem BlockPtr.get!_createRegion {block : BlockPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    block.get! ctx' = block.get! ctx := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.get!_createRegion {operation : OperationPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    operation.get! ctx' = operation.get! ctx := by
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
theorem OpResultPtr.get!_createRegion {opResult : OpResultPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    opResult.get! ctx' = opResult.get! ctx := by
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumOperands!_createRegion {operation : OperationPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    operation.getNumOperands! ctx' = operation.getNumOperands! ctx := by
  grind

@[simp, grind =>, simp_getset]
theorem OpOperandPtr.get!_createRegion {operand : OpOperandPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    operand.get! ctx' = operand.get! ctx := by
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
theorem BlockOperandPtr.get!_createRegion {operand : BlockOperandPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    operand.get! ctx' = operand.get! ctx := by
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
theorem BlockArgumentPtr.get!_createRegion {blockArg : BlockArgumentPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    blockArg.get! ctx' = blockArg.get! ctx := by
  grind

@[grind =>, simp_getset]
theorem RegionPtr.firstBlock!_createRegion {region : RegionPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    (region.get! ctx').firstBlock =
    if region = reg then none else (region.get! ctx).firstBlock := by
  grind [Region.empty]

@[grind =>, simp_getset]
theorem RegionPtr.lastBlock!_createRegion {region : RegionPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    (region.get! ctx').lastBlock =
    if region = reg then none else (region.get! ctx).lastBlock := by
  grind [Region.empty]

@[grind =>, simp_getset]
theorem RegionPtr.parent!_createRegion {region : RegionPtr} :
    Rewriter.createRegion ctx = some (ctx', reg) →
    (region.get! ctx').parent =
    if region = reg then none else (region.get! ctx).parent := by
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
