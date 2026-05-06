module

public import Veir.IR.Basic
public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic

import Veir.Rewriter.LinkedList.GetSet
import Veir.ForLean
import Veir.IR.DeallocLemmas

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
section Rewriter.insertOp?

unseal Rewriter.insertOp?

attribute [local grind] Rewriter.insertOp?

@[simp]
theorem BlockPtr.firstUse!_insertOp? {block : BlockPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).firstUse = (block.get! ctx).firstUse := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern BlockPtr.firstUse!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).firstUse

@[simp]
theorem BlockPtr.prev!_insertOp? {block : BlockPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).prev = (block.get! ctx).prev := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern BlockPtr.prev!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).prev

@[simp]
theorem BlockPtr.next!_insertOp? {block : BlockPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).next = (block.get! ctx).next := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern BlockPtr.next!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).next

@[simp]
theorem BlockPtr.parent!_insertOp? {block : BlockPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).parent = (block.get! ctx).parent := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern BlockPtr.parent!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).parent

theorem BlockPtr.firstOp!_insertOp? {block : BlockPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).firstOp =
    if ip.block! ctx = block ∧ ip.prev! ctx = none then
      some newOp
    else
      (block.get! ctx).firstOp := by
  simp only [Rewriter.insertOp?]
  grind [cases InsertPoint]

grind_pattern BlockPtr.firstOp!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).firstOp

theorem BlockPtr.lastOp!_insertOp? {block : BlockPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).lastOp =
    if ip.block! ctx = block ∧ ip.next = none then
      some newOp
    else
      (block.get! ctx).lastOp := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern BlockPtr.lastOp!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).lastOp

theorem OperationPtr.prev!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (operation.get! newCtx).prev =
    if operation = ip.next then
      some newOp
    else if operation = newOp then
      ip.prev! ctx
    else
      (operation.get! ctx).prev := by
  simp only [Rewriter.insertOp?]
  grind [cases InsertPoint]

grind_pattern OperationPtr.prev!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (operation.get! newCtx).prev

theorem OperationPtr.next!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (operation.get! newCtx).next =
    if operation = ip.prev! ctx then
      some newOp
    else if operation = newOp then
      ip.next
    else
      (operation.get! ctx).next := by
  simp only [Rewriter.insertOp?]
  grind [cases InsertPoint]

grind_pattern OperationPtr.next!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (operation.get! newCtx).next

theorem OperationPtr.parent!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (operation.get! newCtx).parent =
    if operation = newOp then
      ip.block! ctx
    else
      (operation.get! ctx).parent := by
  simp only [Rewriter.insertOp?]
  grind (gen := 10)

grind_pattern OperationPtr.parent!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (operation.get! newCtx).parent

@[simp]
theorem OperationPtr.getOpType!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getOpType! newCtx = operation.getOpType! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OperationPtr.getOpType!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getOpType! newCtx

@[simp]
theorem OperationPtr.attrs!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    (operation.get! newCtx).attrs = (operation.get! ctx).attrs := by
  grind

grind_pattern OperationPtr.attrs!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, (operation.get! newCtx).attrs

@[simp]
theorem OperationPtr.getProperties!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getProperties! newCtx opCode = operation.getProperties! ctx opCode := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OperationPtr.getProperties!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getProperties! newCtx opCode

@[simp]
theorem OperationPtr.getNumResults!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getNumResults! newCtx = operation.getNumResults! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OperationPtr.getNumResults!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getNumResults! newCtx

@[simp]
theorem OpResultPtr.get!_insertOp? {opResult : OpResultPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    opResult.get! newCtx = opResult.get! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OpResultPtr.get!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, opResult.get! newCtx

@[simp]
theorem OperationPtr.getNumOperands!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OperationPtr.getNumOperands!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getNumOperands! newCtx

@[simp]
theorem OpOperandPtr.get!_insertOp? {operand : OpOperandPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OpOperandPtr.get!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operand.get! newCtx

@[simp]
theorem OperationPtr.getOperands!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getOperands! newCtx = operation.getOperands! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OperationPtr.getOperands!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getOperands! newCtx

@[simp]
theorem OperationPtr.getNumSuccessors!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getNumSuccessors! newCtx = operation.getNumSuccessors! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OperationPtr.getNumSuccessors!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getNumSuccessors! newCtx

@[simp]
theorem BlockOperandPtr.get!_insertOp? {operand : BlockOperandPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern BlockOperandPtr.get!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operand.get! newCtx

@[simp]
theorem OperationPtr.getSuccessor!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getSuccessor! newCtx index = operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

grind_pattern OperationPtr.getSuccessor!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getSuccessor! newCtx index

@[simp]
theorem OperationPtr.getSuccessors!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getSuccessors! newCtx = operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

grind_pattern OperationPtr.getSuccessors!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getSuccessors! newCtx

@[simp]
theorem OperationPtr.getNumRegions!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getNumRegions! newCtx = operation.getNumRegions! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OperationPtr.getNumRegions!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getNumRegions! newCtx

@[simp]
theorem OperationPtr.getRegion!_insertOp? {operation : OperationPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operation.getRegion! newCtx idx = operation.getRegion! ctx idx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OperationPtr.getRegion!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operation.getRegion! newCtx idx

@[simp]
theorem BlockOperandPtrPtr.get!_insertOp? {operandPtr : BlockOperandPtrPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    operandPtr.get! newCtx = operandPtr.get! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern BlockOperandPtrPtr.get!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, operandPtr.get! newCtx

@[simp]
theorem BlockPtr.getNumArguments!_insertOp? {block : BlockPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    block.getNumArguments! newCtx = block.getNumArguments! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern BlockPtr.getNumArguments!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, block.getNumArguments! newCtx

@[simp]
theorem BlockArgumentPtr.get!_insertOp? {blockArg : BlockArgumentPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    blockArg.get! newCtx = blockArg.get! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern BlockArgumentPtr.get!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, blockArg.get! newCtx

@[simp]
theorem RegionPtr.get!_insertOp? {region : RegionPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    region.get! newCtx = region.get! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern RegionPtr.get!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, region.get! newCtx

@[simp]
theorem ValuePtr.getFirstUse!_insertOp? {value : ValuePtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    value.getFirstUse! newCtx = value.getFirstUse! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern ValuePtr.getFirstUse!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, value.getFirstUse! newCtx

theorem ValuePtr.getType!_insertOp? {value : ValuePtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    value.getType! newCtx = value.getType! ctx := by
  grind

grind_pattern ValuePtr.getType!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, value.getType! newCtx

@[simp]
theorem OpOperandPtrPtr.get!_insertOp? {opOperandPtr : OpOperandPtrPtr} :
    Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx →
    opOperandPtr.get! newCtx = opOperandPtr.get! ctx := by
  simp only [Rewriter.insertOp?]
  grind

grind_pattern OpOperandPtrPtr.get!_insertOp? =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, opOperandPtr.get! newCtx

end Rewriter.insertOp?

end Veir
