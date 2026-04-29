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

/-! ## `Rewriter.pushBlockOperand` -/

section Rewriter.pushBlockOperand

variable {opPtr : OperationPtr} {blockPtr : BlockPtr}

attribute [local grind] Rewriter.pushBlockOperand

@[grind =]
theorem BlockPtr.firstUse!_pushBlockOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).firstUse =
    if block = blockPtr then some (opPtr.nextBlockOperand! ctx) else (block.get! ctx).firstUse := by
  grind [OperationPtr.getBlockOperand_def]

@[simp, grind =]
theorem BlockPtr.prev!_pushBlockOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_pushBlockOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_pushBlockOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_pushBlockOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_pushBlockOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_pushBlockOperand {operation : OperationPtr} :
    operation.getProperties! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_pushBlockOperand {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_pushBlockOperand {opResult : OpResultPtr} :
    opResult.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_pushBlockOperand {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_pushBlockOperand {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_pushBlockOperand {operation : OperationPtr} :
    operation.getOperands! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    operation.getOperands! ctx := by
  grind

@[grind =]
theorem OperationPtr.getNumSuccessors!_pushBlockOperand {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    if operation = opPtr then
      (operation.getNumSuccessors! ctx) + 1
    else
      operation.getNumSuccessors! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.get!_pushBlockOperand {operand : BlockOperandPtr} :
    operand.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    if operand = opPtr.nextBlockOperand ctx then
      {
        value := blockPtr,
        owner := opPtr,
        back := .blockFirstUse blockPtr,
        nextUse := (blockPtr.get! ctx).firstUse
      }
    else
      {
        operand.get! ctx with
        back :=
          if (blockPtr.get! ctx).firstUse = some operand then
            .blockOperandNextUse (opPtr.nextBlockOperand ctx)
          else (operand.get! ctx).back
      } := by
  have : (blockPtr.get! ctx).firstUse.maybe InBounds ctx := by grind
  have : ¬ (opPtr.nextBlockOperand ctx).InBounds ctx := by grind
  split <;> grind [OperationPtr.getBlockOperand_def]

theorem BlockOperandPtr.get!_pushBlockOperand' {operandPtr : BlockOperandPtr} :
    operandPtr.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr opPtrInBounds blockPtrInBounds ctxInBounds) =
      if operandPtr = opPtr.nextBlockOperand ctx then
        { value := blockPtr,
          owner := opPtr,
          back := BlockOperandPtrPtr.blockFirstUse blockPtr,
          nextUse := (blockPtr.get! ctx).firstUse : BlockOperand}
      else if (blockPtr.get! ctx).firstUse = some operandPtr then
       { operandPtr.get! ctx with back := BlockOperandPtrPtr.blockOperandNextUse (opPtr.nextBlockOperand ctx) }
      else
        operandPtr.get! ctx := by
  apply BlockOperand.ext <;> grind

@[grind =]
theorem OperationPtr.getSuccessor!_pushBlockOperand {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) index =
    if operation = opPtr ∧ index = operation.getNumSuccessors! ctx then blockPtr
    else operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def, OperationPtr.getBlockOperand_def]

@[grind =]
theorem OperationPtr.getSuccessors!_pushBlockOperand {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    if operation = opPtr then (operation.getSuccessors! ctx).push blockPtr
    else operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessor!_def, OperationPtr.getBlockOperand_def]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_pushBlockOperand {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_pushBlockOperand {operation : OperationPtr} :
    operation.getRegion! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) idx =
    operation.getRegion! ctx idx := by
  grind

/--
BlockOperandPtrPtr.get!_pushBlockOperand should not be needed
in practice, as we should reason at a higher-level abstraction at this point.
-/

@[simp, grind =]
theorem BlockPtr.getNumArguments!_pushBlockOperand {block : BlockPtr} :
    block.getNumArguments! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.firstBlock!_pushBlockOperand {region : RegionPtr} :
    (region.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).firstBlock =
    (region.get! ctx).firstBlock := by
  grind

@[simp, grind =]
theorem RegionPtr.lastBlock!_pushBlockOperand {region : RegionPtr} :
    (region.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).lastBlock =
    (region.get! ctx).lastBlock := by
  grind

@[simp, grind =]
theorem RegionPtr.parent!_pushBlockOperand {region : RegionPtr} :
    (region.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).parent =
    (region.get! ctx).parent := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_pushBlockOperand {value : ValuePtr} :
    value.getFirstUse! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_pushBlockOperand {value : ValuePtr} :
    value.getType! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_pushBlockOperand {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    opOperandPtr.get! ctx := by
  grind

end Rewriter.pushBlockOperand
/-! ## `Rewriter.initBlockOperands` -/

section Rewriter.initBlockOperands

variable {op : OperationPtr}

attribute [local grind] Rewriter.initBlockOperands

@[simp, grind =]
theorem BlockPtr.prev!_initBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).prev =
    (block.get! ctx).prev := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem BlockPtr.next!_initBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).next =
    (block.get! ctx).next := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem BlockPtr.parent!_initBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).parent =
    (block.get! ctx).parent := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem BlockPtr.firstOp!_initBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).firstOp =
    (block.get! ctx).firstOp := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem BlockPtr.lastOp!_initBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).lastOp =
    (block.get! ctx).lastOp := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem OperationPtr.prev!_initBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).prev =
    (operation.get! ctx).prev := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem OperationPtr.next!_initBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).next =
    (operation.get! ctx).next := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem OperationPtr.parent!_initBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).parent =
    (operation.get! ctx).parent := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem OperationPtr.opType!_initBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).opType =
    (operation.get! ctx).opType := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem OperationPtr.attrs!_initBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).attrs =
    (operation.get! ctx).attrs := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem OperationPtr.getProperties!_initBlockOperands {operation : OperationPtr} :
    operation.getProperties! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) opCode =
    operation.getProperties! ctx opCode := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_initBlockOperands {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    operation.getNumResults! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem OpResultPtr.get!_initBlockOperands {opResult : OpResultPtr} :
    opResult.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    opResult.get! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_initBlockOperands {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    operation.getNumOperands! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem OpOperandPtr.get!_initBlockOperands {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    opOperand.get! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem OperationPtr.getOperands!_initBlockOperands {operation : OperationPtr} :
    operation.getOperands! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    operation.getOperands! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_initBlockOperands {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    operation.getNumRegions! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem OperationPtr.getRegion!_initBlockOperands {operation : OperationPtr} :
    operation.getRegion! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) idx =
    operation.getRegion! ctx idx := by
  fun_induction Rewriter.initBlockOperands <;> grind

/--
BlockOperandPtrPtr.get!_initBlockOperands is too complex to be expressed, and should not
be needed in practice, as we should reason at a higher-level abstraction at this point.
-/

@[grind =]
theorem OperationPtr.getSuccessor!_initBlockOperands {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) index =
    if operation = op ∧ index ≥ operation.getNumSuccessors! ctx then
      operands[index - operation.getNumSuccessors! ctx + operands.size - n]!
    else
      operation.getSuccessor! ctx index := by
  simp only [← OperationPtr.getSuccessors!.getElem!_eq_getSuccessor!]
  fun_induction Rewriter.initBlockOperands <;> grind

@[grind =]
theorem OperationPtr.getNumSuccessors!_initBlockOperands {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    if operation = op then
      (operation.getNumSuccessors! ctx) + n
    else
      operation.getNumSuccessors! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[grind =]
theorem OperationPtr.getSuccessors!_initBlockOperands {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    if operation = op then
      (operation.getSuccessors! ctx) ++ operands.extract (operands.size - n) operands.size
    else
      operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_initBlockOperands {block : BlockPtr} :
    block.getNumArguments! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    block.getNumArguments! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_initBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    blockArg.get! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem RegionPtr.firstBlock!_initBlockOperands {region : RegionPtr} :
    (region.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).firstBlock =
    (region.get! ctx).firstBlock := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem RegionPtr.lastBlock!_initBlockOperands {region : RegionPtr} :
    (region.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).lastBlock =
    (region.get! ctx).lastBlock := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem RegionPtr.parent!_initBlockOperands {region : RegionPtr} :
    (region.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).parent =
    (region.get! ctx).parent := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_initBlockOperands {value : ValuePtr} :
    value.getFirstUse! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    value.getFirstUse! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem ValuePtr.getType!_initBlockOperands {value : ValuePtr} :
    value.getType! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    value.getType! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_initBlockOperands {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    opOperandPtr.get! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

end Rewriter.initBlockOperands

end Veir
