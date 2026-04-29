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
/-! ## `Rewriter.pushOperand` -/

section Rewriter.pushOperand

variable {opPtr : OperationPtr} {valuePtr : ValuePtr}

attribute [local grind] Rewriter.pushOperand

@[simp, grind =]
theorem BlockPtr.firstUse!_pushOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_pushOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_pushOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_pushOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_pushOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_pushOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_pushOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_pushOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_pushOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_pushOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_pushOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_pushOperand {operation : OperationPtr} :
    operation.getProperties! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_pushOperand {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    operation.getNumResults! ctx := by
  grind

@[grind =]
theorem OpResultPtr.get!_pushOperand {opResult : OpResultPtr} :
    opResult.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    if valuePtr = opResult then
      { opResult.get! ctx with firstUse := some (opPtr.nextOperand! ctx) }
    else
      opResult.get! ctx := by
  grind [OperationPtr.getOpOperand_def]

@[simp, grind =]
theorem OperationPtr.getNumOperands!_pushOperand {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    if operation = opPtr then
      (operation.getNumOperands! ctx) + 1
    else
      operation.getNumOperands! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.get!_pushOperand {operand : OpOperandPtr} :
    operand.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    if operand = opPtr.nextOperand ctx then
      {
        value := valuePtr,
        owner := opPtr,
        back := .valueFirstUse valuePtr,
        nextUse := valuePtr.getFirstUse! ctx
      }
    else
      {
        operand.get! ctx with
        back :=
          if valuePtr.getFirstUse! ctx = some operand then
            .operandNextUse (opPtr.nextOperand ctx)
          else (operand.get! ctx).back
      } := by
  have : (valuePtr.getFirstUse! ctx).maybe InBounds ctx := by grind
  have : ¬ (opPtr.nextOperand ctx).InBounds ctx := by grind
  split <;> grind [OperationPtr.getOpOperand_def]

/-
This version of the theorem has if/else branches that are sometimes more convenient for reasonning.
-/
theorem OpOperandPtr.get!_pushOperand'
    (valuePtr : ValuePtr) valuePtrInBounds (operandPtr : OpOperandPtr) :
    operandPtr.get! (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) =
      if operandPtr = opPtr.nextOperand ctx then
        { value := valuePtr,
          owner := opPtr,
          back := OpOperandPtrPtr.valueFirstUse valuePtr,
          nextUse := (valuePtr.getFirstUse! ctx) : OpOperand}
      else if valuePtr.getFirstUse! ctx = some operandPtr then
       { operandPtr.get! ctx with back := OpOperandPtrPtr.operandNextUse (opPtr.nextOperand ctx) }
      else
        operandPtr.get! ctx := by
  apply OpOperand.ext <;> grind

@[simp, grind =]
theorem OperationPtr.getOperands!_pushOperand {operation : OperationPtr} :
    operation.getOperands! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    if operation = opPtr then
      (operation.getOperands! ctx).push valuePtr
    else
      operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_pushOperand {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_pushOperand {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_pushOperand {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_pushOperand {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_pushOperand,
    OperationPtr.getNumSuccessors!_pushOperand]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_pushOperand {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_pushOperand {operation : OperationPtr} :
    operation.getRegion! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) idx =
    operation.getRegion! ctx idx := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_pushOperand {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_pushOperand {block : BlockPtr} :
    block.getNumArguments! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_pushOperand {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    if valuePtr = blockArg then
      { blockArg.get! ctx with firstUse := some (opPtr.nextOperand! ctx) }
    else
      blockArg.get! ctx := by
  grind [OperationPtr.getOpOperand_def]

@[simp, grind =]
theorem RegionPtr.firstBlock!_pushOperand {region : RegionPtr} :
    (region.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).firstBlock =
    (region.get! ctx).firstBlock := by
  grind

@[simp, grind =]
theorem RegionPtr.lastBlock!_pushOperand {region : RegionPtr} :
    (region.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).lastBlock =
    (region.get! ctx).lastBlock := by
  grind

@[simp, grind =]
theorem RegionPtr.parent!_pushOperand {region : RegionPtr} :
    (region.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).parent =
    (region.get! ctx).parent := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_pushOperand {value : ValuePtr} :
    value.getType! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_pushOperand {value : ValuePtr} :
    value.getFirstUse! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    if value = valuePtr then some (opPtr.nextOperand! ctx) else value.getFirstUse! ctx := by
  grind [OperationPtr.getOpOperand_def]

@[simp, grind =]
theorem OpOperandPtrPtr.get!_pushOperand {operandPtr : OpOperandPtrPtr} :
    operandPtr.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    if operandPtr = .operandNextUse (opPtr.nextOperand ctx) then
      valuePtr.getFirstUse! ctx
    else if operandPtr = .valueFirstUse valuePtr then
      some (opPtr.nextOperand! ctx)
    else
      operandPtr.get! ctx := by
  grind

end Rewriter.pushOperand
/-! ## `Rewriter.initOpOperands` -/

section Rewriter.initOpOperands

variable {op : OperationPtr}

attribute [local grind] Rewriter.initOpOperands

@[simp, grind =]
theorem BlockPtr.firstUse!_initOpOperands {block : BlockPtr} :
    (block.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).firstUse =
    (block.get! ctx).firstUse := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem BlockPtr.prev!_initOpOperands {block : BlockPtr} :
    (block.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).prev =
    (block.get! ctx).prev := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem BlockPtr.next!_initOpOperands {block : BlockPtr} :
    (block.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).next =
    (block.get! ctx).next := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem BlockPtr.parent!_initOpOperands {block : BlockPtr} :
    (block.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).parent =
    (block.get! ctx).parent := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem BlockPtr.firstOp!_initOpOperands {block : BlockPtr} :
    (block.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).firstOp =
    (block.get! ctx).firstOp := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem BlockPtr.lastOp!_initOpOperands {block : BlockPtr} :
    (block.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).lastOp =
    (block.get! ctx).lastOp := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem OperationPtr.prev!_initOpOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).prev =
    (operation.get! ctx).prev := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem OperationPtr.next!_initOpOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).next =
    (operation.get! ctx).next := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem OperationPtr.parent!_initOpOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).parent =
    (operation.get! ctx).parent := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem OperationPtr.opType!_initOpOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).opType =
    (operation.get! ctx).opType := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem OperationPtr.attrs!_initOpOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).attrs =
    (operation.get! ctx).attrs := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem OperationPtr.getProperties!_initOpOperands {operation : OperationPtr} :
    operation.getProperties! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) opCode =
    operation.getProperties! ctx opCode := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_initOpOperands {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    operation.getNumResults! ctx := by
  fun_induction Rewriter.initOpOperands <;> grind

/--
OpResultPtr.get!_initOpOperands is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_initOpOperands {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    operation.getNumSuccessors! ctx := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem BlockOperandPtr.get!_initOpOperands {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    blockOperand.get! ctx := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_initOpOperands {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) i =
    operation.getSuccessor! ctx i := by
  fun_induction Rewriter.initOpOperands <;> grind [OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_initOpOperands {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_initOpOperands,
    OperationPtr.getNumSuccessors!_initOpOperands]

@[grind =>]
theorem OperationPtr.getNumOperands!_initOpOperands {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    if operation = op then
      operation.getNumOperands! ctx + n
    else
      operation.getNumOperands! ctx := by
  fun_induction Rewriter.initOpOperands <;> grind

/-
OpOperandPtr.get!_initOpOperands is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

@[grind =>]
theorem OperationPtr.getOperands!_initOpOperands {operation : OperationPtr} :
    operation.getOperands! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    if operation = op then
      (operation.getOperands! ctx) ++ operands.extract (operands.size - n) operands.size
    else
      operation.getOperands! ctx := by
  fun_induction Rewriter.initOpOperands <;>
    grind [Array.singleton_getElem_append_extract_succ_eq]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_initOpOperands {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    operation.getNumRegions! ctx := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem OperationPtr.getRegion!_initOpOperands {operation : OperationPtr} :
    operation.getRegion! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) idx =
    operation.getRegion! ctx idx := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_initOpOperands {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    blockOperandPtr.get! ctx := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_initOpOperands {block : BlockPtr} :
    block.getNumArguments! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    block.getNumArguments! ctx := by
  fun_induction Rewriter.initOpOperands <;> grind

/-
BlockArgumentPtr.get!_initOpOperands is too complex to be expressed, and should not be needed
in practice, as we should reason at a higher-level abstraction at this point.
-/

@[simp, grind =]
theorem RegionPtr.firstBlock!_initOpOperands {region : RegionPtr} :
    (region.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).firstBlock =
    (region.get! ctx).firstBlock := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem RegionPtr.lastBlock!_initOpOperands {region : RegionPtr} :
    (region.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).lastBlock =
    (region.get! ctx).lastBlock := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =]
theorem RegionPtr.parent!_initOpOperands {region : RegionPtr} :
    (region.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).parent =
    (region.get! ctx).parent := by
  fun_induction Rewriter.initOpOperands <;> grind

/-
ValuePtr.getFirstUse!_initOpOperands is too complex to be expressed, and should not be needed
in practice, as we should reason at a higher-level abstraction at this point.
-/

@[simp, grind =]
theorem ValuePtr.getType!_initOpOperands {value : ValuePtr} :
    value.getType! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    value.getType! ctx := by
  fun_induction Rewriter.initOpOperands <;> grind

/-
OpOperandPtrPtr.get!_initOpOperands is too complex to be expressed, and should not be needed
in practice, as we should reason at a higher-level abstraction at this point.
-/

end Rewriter.initOpOperands

end Veir
