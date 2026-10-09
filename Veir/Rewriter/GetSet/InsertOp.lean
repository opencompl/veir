module

public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic
import Veir.Rewriter.WfRewriter.GetSetTactic


public section

namespace Veir

variable {OpInfo} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
variable {opCode : Dialect}
section Rewriter.insertOp

unseal Rewriter.insertOp

attribute [local grind] Rewriter.insertOp

@[simp, simp_getset]
theorem BlockPtr.firstUse!_insertOp {block : BlockPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).firstUse = (block.get! ctx).firstUse := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern BlockPtr.firstUse!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).firstUse

@[simp, simp_getset]
theorem BlockPtr.prev!_insertOp {block : BlockPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).prev = (block.get! ctx).prev := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern BlockPtr.prev!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).prev

@[simp, simp_getset]
theorem BlockPtr.next!_insertOp {block : BlockPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).next = (block.get! ctx).next := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern BlockPtr.next!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).next

@[simp, simp_getset]
theorem BlockPtr.parent!_insertOp {block : BlockPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).parent = (block.get! ctx).parent := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern BlockPtr.parent!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).parent

@[simp_getset]
theorem BlockPtr.firstOp!_insertOp {block : BlockPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).firstOp =
    if ip.block! ctx = block ∧ ip.prev! ctx = none then
      some newOp
    else
      (block.get! ctx).firstOp := by
  simp only [Rewriter.insertOp]
  grind [cases InsertPoint]

grind_pattern BlockPtr.firstOp!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).firstOp

@[simp_getset]
theorem BlockPtr.lastOp!_insertOp {block : BlockPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).lastOp =
    if ip.block! ctx = block ∧ ip.next = none then
      some newOp
    else
      (block.get! ctx).lastOp := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern BlockPtr.lastOp!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).lastOp

@[simp_getset]
theorem OperationPtr.prev!_insertOp {operation : OperationPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (operation.get! newCtx).prev =
    if operation = ip.next then
      some newOp
    else if operation = newOp then
      ip.prev! ctx
    else
      (operation.get! ctx).prev := by
  simp only [Rewriter.insertOp]
  grind [cases InsertPoint]

grind_pattern OperationPtr.prev!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, (operation.get! newCtx).prev

@[simp_getset]
theorem OperationPtr.next!_insertOp {operation : OperationPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (operation.get! newCtx).next =
    if operation = ip.prev! ctx then
      some newOp
    else if operation = newOp then
      ip.next
    else
      (operation.get! ctx).next := by
  simp only [Rewriter.insertOp]
  grind [cases InsertPoint]

grind_pattern OperationPtr.next!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, (operation.get! newCtx).next

@[simp_getset]
theorem OperationPtr.parent!_insertOp {operation : OperationPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (operation.get! newCtx).parent =
    if operation = newOp then
      ip.block! ctx
    else
      (operation.get! ctx).parent := by
  simp only [Rewriter.insertOp]
  grind (gen := 10)

grind_pattern OperationPtr.parent!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, (operation.get! newCtx).parent

@[simp, simp_getset]
theorem OperationPtr.getOpType!_insertOp {operation : OperationPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getOpType! newCtx = operation.getOpType! ctx := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern OperationPtr.getOpType!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getOpType! newCtx

@[simp, simp_getset]
theorem OperationPtr.attrs!_insertOp {operation : OperationPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (operation.get! newCtx).attrs = (operation.get! ctx).attrs := by
  grind

grind_pattern OperationPtr.attrs!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, (operation.get! newCtx).attrs

@[simp, simp_getset]
theorem OperationPtr.getProperties!_insertOp {operation : OperationPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getProperties! newCtx opCode = operation.getProperties! ctx opCode := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern OperationPtr.getProperties!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getProperties! newCtx opCode

@[simp, simp_getset]
theorem OperationPtr.getNumResults!_insertOp {operation : OperationPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getNumResults! newCtx = operation.getNumResults! ctx := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern OperationPtr.getNumResults!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getNumResults! newCtx

@[simp, simp_getset]
theorem OpResultPtr.get!_insertOp {opResult : OpResultPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    opResult.get! newCtx = opResult.get! ctx := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern OpResultPtr.get!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, opResult.get! newCtx

@[simp, simp_getset]
theorem OpResultPtr.getIndex!_insertOp {opResult : OpResultPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    opResult.getIndex! newCtx =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

grind_pattern OpResultPtr.getIndex!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, opResult.getIndex! newCtx

@[simp, simp_getset]
theorem OpResultPtr.getType!_insertOp {opResult : OpResultPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    opResult.getType! newCtx =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

grind_pattern OpResultPtr.getType!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, opResult.getType! newCtx

@[simp, simp_getset]
theorem OpResultPtr.getFirstUse!_insertOp {opResult : OpResultPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    opResult.getFirstUse! newCtx =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

grind_pattern OpResultPtr.getFirstUse!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, opResult.getFirstUse! newCtx

@[simp, simp_getset]
theorem OpResultPtr.getOwner!_insertOp {opResult : OpResultPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    opResult.getOwner! newCtx =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

grind_pattern OpResultPtr.getOwner!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, opResult.getOwner! newCtx

@[simp, simp_getset]
theorem OperationPtr.getNumOperands!_insertOp {operation : OperationPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern OperationPtr.getNumOperands!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getNumOperands! newCtx

@[simp, simp_getset]
theorem OpOperandPtr.get!_insertOp {operand : OpOperandPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern OpOperandPtr.get!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operand.get! newCtx

@[simp, simp_getset]
theorem OpOperandPtr.getNextUse!_insertOp {operand : OpOperandPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operand.getNextUse! newCtx =
    operand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

grind_pattern OpOperandPtr.getNextUse!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operand.getNextUse! newCtx

@[simp, simp_getset]
theorem OpOperandPtr.getBack!_insertOp {operand : OpOperandPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operand.getBack! newCtx =
    operand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

grind_pattern OpOperandPtr.getBack!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operand.getBack! newCtx

@[simp, simp_getset]
theorem OpOperandPtr.getOwner!_insertOp {operand : OpOperandPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operand.getOwner! newCtx =
    operand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

grind_pattern OpOperandPtr.getOwner!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operand.getOwner! newCtx

@[simp, simp_getset]
theorem OpOperandPtr.getValue!_insertOp {operand : OpOperandPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operand.getValue! newCtx =
    operand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

grind_pattern OpOperandPtr.getValue!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operand.getValue! newCtx

@[simp, simp_getset]
theorem OperationPtr.getOperands!_insertOp {operation : OperationPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getOperands! newCtx = operation.getOperands! ctx := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern OperationPtr.getOperands!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getOperands! newCtx

@[simp, simp_getset]
theorem OperationPtr.getNumSuccessors!_insertOp {operation : OperationPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getNumSuccessors! newCtx = operation.getNumSuccessors! ctx := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern OperationPtr.getNumSuccessors!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getNumSuccessors! newCtx

@[simp, simp_getset]
theorem BlockOperandPtr.get!_insertOp {operand : BlockOperandPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern BlockOperandPtr.get!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operand.get! newCtx

@[simp, simp_getset]
theorem BlockOperandPtr.getNextUse!_insertOp {operand : BlockOperandPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operand.getNextUse! newCtx =
    operand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

grind_pattern BlockOperandPtr.getNextUse!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operand.getNextUse! newCtx

@[simp, simp_getset]
theorem BlockOperandPtr.getBack!_insertOp {operand : BlockOperandPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operand.getBack! newCtx =
    operand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

grind_pattern BlockOperandPtr.getBack!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operand.getBack! newCtx

@[simp, simp_getset]
theorem BlockOperandPtr.getOwner!_insertOp {operand : BlockOperandPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operand.getOwner! newCtx =
    operand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

grind_pattern BlockOperandPtr.getOwner!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operand.getOwner! newCtx

@[simp, simp_getset]
theorem BlockOperandPtr.getValue!_insertOp {operand : BlockOperandPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operand.getValue! newCtx =
    operand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

grind_pattern BlockOperandPtr.getValue!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operand.getValue! newCtx

@[simp, simp_getset]
theorem OperationPtr.getSuccessor!_insertOp {operation : OperationPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getSuccessor! newCtx index = operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

grind_pattern OperationPtr.getSuccessor!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getSuccessor! newCtx index

@[simp, simp_getset]
theorem OperationPtr.getSuccessors!_insertOp {operation : OperationPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getSuccessors! newCtx = operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

grind_pattern OperationPtr.getSuccessors!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getSuccessors! newCtx

@[simp, simp_getset]
theorem OperationPtr.getNumRegions!_insertOp {operation : OperationPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getNumRegions! newCtx = operation.getNumRegions! ctx := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern OperationPtr.getNumRegions!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getNumRegions! newCtx

@[simp, simp_getset]
theorem OperationPtr.getRegion!_insertOp {operation : OperationPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getRegion! newCtx idx = operation.getRegion! ctx idx := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern OperationPtr.getRegion!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getRegion! newCtx idx

@[simp, simp_getset]
theorem BlockOperandPtrPtr.get!_insertOp {operandPtr : BlockOperandPtrPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operandPtr.get! newCtx = operandPtr.get! ctx := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern BlockOperandPtrPtr.get!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, operandPtr.get! newCtx

@[simp, simp_getset]
theorem BlockPtr.getNumArguments!_insertOp {block : BlockPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    block.getNumArguments! newCtx = block.getNumArguments! ctx := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern BlockPtr.getNumArguments!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, block.getNumArguments! newCtx

@[simp, simp_getset]
theorem BlockArgumentPtr.get!_insertOp {blockArg : BlockArgumentPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    blockArg.get! newCtx = blockArg.get! ctx := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern BlockArgumentPtr.get!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, blockArg.get! newCtx

@[simp, simp_getset]
theorem BlockArgumentPtr.getType!_insertOp {blockArg : BlockArgumentPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    blockArg.getType! newCtx =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

grind_pattern BlockArgumentPtr.getType!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, blockArg.getType! newCtx

@[simp, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_insertOp {blockArg : BlockArgumentPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    blockArg.getFirstUse! newCtx =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

grind_pattern BlockArgumentPtr.getFirstUse!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, blockArg.getFirstUse! newCtx

@[simp, simp_getset]
theorem BlockArgumentPtr.getIndex!_insertOp {blockArg : BlockArgumentPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    blockArg.getIndex! newCtx =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

grind_pattern BlockArgumentPtr.getIndex!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, blockArg.getIndex! newCtx

@[simp, simp_getset]
theorem BlockArgumentPtr.getLoc!_insertOp {blockArg : BlockArgumentPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    blockArg.getLoc! newCtx =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

grind_pattern BlockArgumentPtr.getLoc!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, blockArg.getLoc! newCtx

@[simp, simp_getset]
theorem BlockArgumentPtr.getOwner!_insertOp {blockArg : BlockArgumentPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    blockArg.getOwner! newCtx =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

grind_pattern BlockArgumentPtr.getOwner!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, blockArg.getOwner! newCtx

@[simp, simp_getset]
theorem RegionPtr.get!_insertOp {region : RegionPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    region.get! newCtx = region.get! ctx := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern RegionPtr.get!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, region.get! newCtx

@[simp, simp_getset]
theorem RegionPtr.getParent!_insertOp {region : RegionPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    region.getParent! newCtx =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

grind_pattern RegionPtr.getParent!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, region.getParent! newCtx

@[simp, simp_getset]
theorem RegionPtr.getFirstBlock!_insertOp {region : RegionPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    region.getFirstBlock! newCtx =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

grind_pattern RegionPtr.getFirstBlock!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, region.getFirstBlock! newCtx

@[simp, simp_getset]
theorem RegionPtr.getLastBlock!_insertOp {region : RegionPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    region.getLastBlock! newCtx =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

grind_pattern RegionPtr.getLastBlock!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, region.getLastBlock! newCtx

@[simp, simp_getset]
theorem ValuePtr.getFirstUse!_insertOp {value : ValuePtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    value.getFirstUse! newCtx = value.getFirstUse! ctx := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern ValuePtr.getFirstUse!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, value.getFirstUse! newCtx

@[simp_getset]
theorem ValuePtr.getType!_insertOp {value : ValuePtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    value.getType! newCtx = value.getType! ctx := by
  grind

grind_pattern ValuePtr.getType!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, value.getType! newCtx

@[simp, simp_getset]
theorem OpOperandPtrPtr.get!_insertOp {opOperandPtr : OpOperandPtrPtr} :
    Rewriter.insertOp ctx newOp ip h₁ h₂ h₃ = some newCtx →
    opOperandPtr.get! newCtx = opOperandPtr.get! ctx := by
  simp only [Rewriter.insertOp]
  grind

grind_pattern OpOperandPtrPtr.get!_insertOp =>
  Rewriter.insertOp ctx newOp ip h₁ h₂ h₃, some newCtx, opOperandPtr.get! newCtx

end Rewriter.insertOp

end Veir
