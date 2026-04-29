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
section Rewriter.insertBlock?

unseal Rewriter.insertBlock?

attribute [local grind] Rewriter.insertBlock?

@[simp]
theorem BlockPtr.firstUse!_insertBlock? {block : BlockPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).firstUse = (block.get! ctx).firstUse := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern BlockPtr.firstUse!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).firstUse

theorem BlockPtr.prev!_insertBlock? {block : BlockPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).prev =
      if block = ip.next then
        some newBlock
      else if block = newBlock then
        ip.prev! ctx
      else
        (block.get! ctx).prev := by
  simp only [Rewriter.insertBlock?]
  grind [cases BlockInsertPoint]

grind_pattern BlockPtr.prev!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).prev

theorem BlockPtr.next!_insertBlock? {block : BlockPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).next =
      if block = ip.prev! ctx then
        some newBlock
      else if block = newBlock then
        ip.next
      else
        (block.get! ctx).next := by
  simp only [Rewriter.insertBlock?]
  grind [cases BlockInsertPoint]

grind_pattern BlockPtr.next!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).next

theorem BlockPtr.parent!_insertBlock? {block : BlockPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).parent =
      if block = newBlock then
        ip.region! ctx
      else
      (block.get! ctx).parent := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern BlockPtr.parent!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).parent

@[simp]
theorem BlockPtr.firstOp!_insertBlock? {block : BlockPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).firstOp = (block.get! ctx).firstOp := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern BlockPtr.firstOp!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).firstOp

@[simp]
theorem BlockPtr.lastOp!_insertBlock? {block : BlockPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    (block.get! newCtx).lastOp = (block.get! ctx).lastOp := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern BlockPtr.lastOp!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, (block.get! newCtx).lastOp

@[simp]
theorem OperationPtr.get!_insertBlock? {operation : OperationPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.get! newCtx = operation.get! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OperationPtr.get!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.get! newCtx

@[simp]
theorem OperationPtr.getNumResults!_insertBlock? {operation : OperationPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getNumResults! newCtx = operation.getNumResults! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OperationPtr.getNumResults!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getNumResults! newCtx

@[simp]
theorem OpResultPtr.get!_insertBlock? {opResult : OpResultPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    opResult.get! newCtx = opResult.get! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OpResultPtr.get!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, opResult.get! newCtx

@[simp]
theorem OperationPtr.getNumOperands!_insertBlock? {operation : OperationPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OperationPtr.getNumOperands!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getNumOperands! newCtx

@[simp]
theorem OpOperandPtr.get!_insertBlock? {operand : OpOperandPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OpOperandPtr.get!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.get! newCtx

@[simp]
theorem OperationPtr.getOperands!_insertBlock? {operation : OperationPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getOperands! newCtx = operation.getOperands! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OperationPtr.getOperands!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getOperands! newCtx

@[simp]
theorem OperationPtr.getNumSuccessors!_insertBlock? {operation : OperationPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getNumSuccessors! newCtx = operation.getNumSuccessors! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OperationPtr.getNumSuccessors!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getNumSuccessors! newCtx

@[simp]
theorem BlockOperandPtr.get!_insertBlock? {operand : BlockOperandPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern BlockOperandPtr.get!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operand.get! newCtx

@[simp]
theorem OperationPtr.getSuccessor!_insertBlock? {operation : OperationPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getSuccessor! newCtx index = operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

grind_pattern OperationPtr.getSuccessor!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getSuccessor! newCtx index

@[simp]
theorem OperationPtr.getSuccessors!_insertBlock? {operation : OperationPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getSuccessors! newCtx = operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

grind_pattern OperationPtr.getSuccessors!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getSuccessors! newCtx

@[simp]
theorem OperationPtr.getNumRegions!_insertBlock? {operation : OperationPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getNumRegions! newCtx = operation.getNumRegions! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OperationPtr.getNumRegions!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getNumRegions! newCtx

@[simp]
theorem OperationPtr.getRegion!_insertBlock? {operation : OperationPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operation.getRegion! newCtx = operation.getRegion! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OperationPtr.getRegion!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operation.getRegion! newCtx

@[simp]
theorem BlockOperandPtrPtr.get!_insertBlock? {operandPtr : BlockOperandPtrPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    operandPtr.get! newCtx = operandPtr.get! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern BlockOperandPtrPtr.get!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, operandPtr.get! newCtx

@[simp]
theorem BlockPtr.getNumArguments!_insertBlock? {block : BlockPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    block.getNumArguments! newCtx = block.getNumArguments! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern BlockPtr.getNumArguments!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, block.getNumArguments! newCtx

@[simp]
theorem BlockArgumentPtr.get!_insertBlock? {blockArg : BlockArgumentPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    blockArg.get! newCtx = blockArg.get! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern BlockArgumentPtr.get!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, blockArg.get! newCtx

theorem RegionPtr.firstBlock!_insertBlock? {region : RegionPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    (region.get! newCtx).firstBlock =
      if ip.region! ctx = region ∧ ip.prev! ctx = none then
        some newBlock
      else
        (region.get! ctx).firstBlock := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern RegionPtr.firstBlock!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, (region.get! newCtx).firstBlock

theorem RegionPtr.lastBlock!_insertBlock? {region : RegionPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    (region.get! newCtx).lastBlock =
      if ip.region! ctx = region ∧ ip.next = none then
        some newBlock
      else
        (region.get! ctx).lastBlock := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern RegionPtr.lastBlock!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, (region.get! newCtx).lastBlock

@[simp]
theorem RegionPtr.parent!_insertBlock? {region : RegionPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    (region.get! newCtx).parent = (region.get! ctx).parent := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern RegionPtr.parent!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, (region.get! newCtx).parent

@[simp]
theorem ValuePtr.getFirstUse!_insertBlock? {value : ValuePtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    value.getFirstUse! newCtx = value.getFirstUse! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern ValuePtr.getFirstUse!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, value.getFirstUse! newCtx

@[simp]
theorem ValuePtr.getType!_insertBlock? {value : ValuePtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    value.getType! newCtx = value.getType! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern ValuePtr.getType!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, value.getType! newCtx

@[simp]
theorem OpOperandPtrPtr.get!_insertBlock? {opOperandPtr : OpOperandPtrPtr} :
    Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃ = some newCtx →
    opOperandPtr.get! newCtx = opOperandPtr.get! ctx := by
  simp only [Rewriter.insertBlock?]
  grind

grind_pattern OpOperandPtrPtr.get!_insertBlock? =>
  Rewriter.insertBlock? ctx newBlock ip h₁ h₂ h₃, some newCtx, opOperandPtr.get! newCtx

end Rewriter.insertBlock?

end Veir
