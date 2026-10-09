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

/-! ## `Rewriter.pushBlockOperand` -/

section Rewriter.pushBlockOperand

variable {opPtr : OperationPtr} {blockPtr : BlockPtr}

attribute [local grind] Rewriter.pushBlockOperand

@[grind =, simp_getset]
theorem BlockPtr.firstUse!_pushBlockOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).firstUse =
    if block = blockPtr then some (opPtr.nextBlockOperand! ctx) else (block.get! ctx).firstUse := by
  grind [OperationPtr.getBlockOperand_def]

@[simp, grind =, simp_getset]
theorem BlockPtr.prev!_pushBlockOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.next!_pushBlockOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.parent!_pushBlockOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.firstOp!_pushBlockOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.lastOp!_pushBlockOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.prev!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.next!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.parent!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_pushBlockOperand {operation : OperationPtr} :
    operation.getOpType! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.attrs!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_pushBlockOperand {operation : OperationPtr} :
    operation.getProperties! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_pushBlockOperand {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.get!_pushBlockOperand {opResult : OpResultPtr} :
    opResult.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    opResult.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_pushBlockOperand {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_pushBlockOperand {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_pushBlockOperand {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_pushBlockOperand {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_pushBlockOperand {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.get!_pushBlockOperand {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    opOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_pushBlockOperand {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_pushBlockOperand {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_pushBlockOperand {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_pushBlockOperand {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_pushBlockOperand {operation : OperationPtr} :
    operation.getOperands! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    operation.getOperands! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_pushBlockOperand {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    if operation = opPtr then
      (operation.getNumSuccessors! ctx) + 1
    else
      operation.getNumSuccessors! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getBlockOperands!_pushBlockOperand {operation : OperationPtr} :
    operation.getBlockOperands! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    if operation = opPtr then Array.map operation.getBlockOperand (Array.range (operation.getNumSuccessors! ctx + 1))
    else operation.getBlockOperands! ctx := by
  simp only [OperationPtr.getBlockOperands!_def]
  grind

@[grind =, simp_getset]
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

@[grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_pushBlockOperand {operand : BlockOperandPtr} :
    operand.getNextUse! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    if operand = opPtr.nextBlockOperand ctx then
      blockPtr.getFirstUse! ctx
    else operand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def, BlockPtr.getFirstUse!_def]
  grind

@[grind =, simp_getset]
theorem BlockOperandPtr.getBack!_pushBlockOperand {operand : BlockOperandPtr} :
    operand.getBack! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    if operand = opPtr.nextBlockOperand ctx then
      BlockOperandPtrPtr.blockFirstUse blockPtr
    else
      if blockPtr.getFirstUse! ctx = some operand then
        BlockOperandPtrPtr.blockOperandNextUse
          (opPtr.nextBlockOperand ctx)
      else operand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def, BlockPtr.getFirstUse!_def]
  grind

@[grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_pushBlockOperand {operand : BlockOperandPtr} :
    operand.getOwner! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    if operand = opPtr.nextBlockOperand ctx then opPtr
    else operand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[grind =, simp_getset]
theorem BlockOperandPtr.getValue!_pushBlockOperand {operand : BlockOperandPtr} :
    operand.getValue! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    if operand = opPtr.nextBlockOperand ctx then blockPtr
    else operand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

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

theorem BlockOperandPtr.getNextUse!_pushBlockOperand' {operandPtr : BlockOperandPtr} :
    operandPtr.getNextUse! (Rewriter.pushBlockOperand ctx opPtr blockPtr opPtrInBounds blockPtrInBounds ctxInBounds) =
    if operandPtr = opPtr.nextBlockOperand ctx then
      blockPtr.getFirstUse! ctx
    else operandPtr.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def, BlockPtr.getFirstUse!_def]
  grind

theorem BlockOperandPtr.getBack!_pushBlockOperand' {operandPtr : BlockOperandPtr} :
    operandPtr.getBack! (Rewriter.pushBlockOperand ctx opPtr blockPtr opPtrInBounds blockPtrInBounds ctxInBounds) =
    if operandPtr = opPtr.nextBlockOperand ctx then
      BlockOperandPtrPtr.blockFirstUse blockPtr
    else
      if (blockPtr.get! ctx).firstUse = some operandPtr then
        BlockOperandPtrPtr.blockOperandNextUse
          (opPtr.nextBlockOperand ctx)
      else operandPtr.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

theorem BlockOperandPtr.getOwner!_pushBlockOperand' {operandPtr : BlockOperandPtr} :
    operandPtr.getOwner! (Rewriter.pushBlockOperand ctx opPtr blockPtr opPtrInBounds blockPtrInBounds ctxInBounds) =
    if operandPtr = opPtr.nextBlockOperand ctx then opPtr
    else operandPtr.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

theorem BlockOperandPtr.getValue!_pushBlockOperand' {operandPtr : BlockOperandPtr} :
    operandPtr.getValue! (Rewriter.pushBlockOperand ctx opPtr blockPtr opPtrInBounds blockPtrInBounds ctxInBounds) =
    if operandPtr = opPtr.nextBlockOperand ctx then blockPtr
    else operandPtr.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[grind =, simp_getset]
theorem OperationPtr.getSuccessor!_pushBlockOperand {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) index =
    if operation = opPtr ∧ index = operation.getNumSuccessors! ctx then blockPtr
    else operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def, OperationPtr.getBlockOperand_def]

@[grind =, simp_getset]
theorem OperationPtr.getSuccessors!_pushBlockOperand {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    if operation = opPtr then (operation.getSuccessors! ctx).push blockPtr
    else operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessor!_def, OperationPtr.getBlockOperand_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_pushBlockOperand {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_pushBlockOperand {operation : OperationPtr} :
    operation.getRegion! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) idx =
    operation.getRegion! ctx idx := by
  grind

/--
BlockOperandPtrPtr.get!_pushBlockOperand should not be needed
in practice, as we should reason at a higher-level abstraction at this point.
-/

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_pushBlockOperand {block : BlockPtr} :
    block.getNumArguments! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getBlockArguments!_pushBlockOperand {block : BlockPtr} :
    block.getBlockArguments! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    block.getBlockArguments! ctx := by
  simp only [BlockPtr.getBlockArguments!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.get!_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    blockArg.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getLoc!_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.firstBlock!_pushBlockOperand {region : RegionPtr} :
    (region.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).firstBlock =
    (region.get! ctx).firstBlock := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.lastBlock!_pushBlockOperand {region : RegionPtr} :
    (region.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).lastBlock =
    (region.get! ctx).lastBlock := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.parent!_pushBlockOperand {region : RegionPtr} :
    (region.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).parent =
    (region.get! ctx).parent := by
  grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getFirstUse!_pushBlockOperand {value : ValuePtr} :
    value.getFirstUse! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getType!_pushBlockOperand {value : ValuePtr} :
    value.getType! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    value.getType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtrPtr.get!_pushBlockOperand {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    opOperandPtr.get! ctx := by
  grind

end Rewriter.pushBlockOperand
/-! ## `Rewriter.initBlockOperands` -/

section Rewriter.initBlockOperands

variable {op : OperationPtr}

attribute [local grind] Rewriter.initBlockOperands

@[simp, grind =, simp_getset]
theorem BlockPtr.prev!_initBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).prev =
    (block.get! ctx).prev := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.next!_initBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).next =
    (block.get! ctx).next := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.parent!_initBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).parent =
    (block.get! ctx).parent := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.firstOp!_initBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).firstOp =
    (block.get! ctx).firstOp := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.lastOp!_initBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).lastOp =
    (block.get! ctx).lastOp := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.prev!_initBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).prev =
    (operation.get! ctx).prev := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.next!_initBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).next =
    (operation.get! ctx).next := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.parent!_initBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).parent =
    (operation.get! ctx).parent := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_initBlockOperands {operation : OperationPtr} :
    operation.getOpType! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    operation.getOpType! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.attrs!_initBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).attrs =
    (operation.get! ctx).attrs := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_initBlockOperands {operation : OperationPtr} :
    operation.getProperties! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) opCode =
    operation.getProperties! ctx opCode := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_initBlockOperands {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    operation.getNumResults! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.get!_initBlockOperands {opResult : OpResultPtr} :
    opResult.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    opResult.get! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_initBlockOperands {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_initBlockOperands {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_initBlockOperands {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_initBlockOperands {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_initBlockOperands {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    operation.getNumOperands! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.get!_initBlockOperands {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    opOperand.get! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_initBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_initBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_initBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_initBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_initBlockOperands {operation : OperationPtr} :
    operation.getOperands! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    operation.getOperands! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_initBlockOperands {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    operation.getNumRegions! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_initBlockOperands {operation : OperationPtr} :
    operation.getRegion! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) idx =
    operation.getRegion! ctx idx := by
  fun_induction Rewriter.initBlockOperands <;> grind

/--
BlockOperandPtrPtr.get!_initBlockOperands is too complex to be expressed, and should not
be needed in practice, as we should reason at a higher-level abstraction at this point.
-/

@[grind =, simp_getset]
theorem OperationPtr.getSuccessor!_initBlockOperands {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) index =
    if operation = op ∧ index ≥ operation.getNumSuccessors! ctx then
      operands[index - operation.getNumSuccessors! ctx + operands.size - n]!
    else
      operation.getSuccessor! ctx index := by
  simp only [← OperationPtr.getSuccessors!.getElem!_eq_getSuccessor!]
  fun_induction Rewriter.initBlockOperands <;> grind

@[grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_initBlockOperands {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    if operation = op then
      (operation.getNumSuccessors! ctx) + n
    else
      operation.getNumSuccessors! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[grind =, simp_getset]
theorem OperationPtr.getBlockOperands!_initBlockOperands {operation : OperationPtr} :
    operation.getBlockOperands! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    if operation = op then Array.map operation.getBlockOperand (Array.range (operation.getNumSuccessors! ctx + n))
    else operation.getBlockOperands! ctx := by
  simp only [OperationPtr.getBlockOperands!_def]
  grind

@[grind =, simp_getset]
theorem OperationPtr.getSuccessors!_initBlockOperands {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    if operation = op then
      (operation.getSuccessors! ctx) ++ operands.extract (operands.size - n) operands.size
    else
      operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def]
  /- We need to remove some grind patterns from the default grind set, as they make the search
  space explode. See https://github.com/leanprover/lean4/issues/15183 -/
  grind [-Array.range'_append, -Array.range'_append_1]

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_initBlockOperands {block : BlockPtr} :
    block.getNumArguments! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    block.getNumArguments! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getBlockArguments!_initBlockOperands {block : BlockPtr} :
    block.getBlockArguments! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    block.getBlockArguments! ctx := by
  simp only [BlockPtr.getBlockArguments!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.get!_initBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    blockArg.get! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_initBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_initBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_initBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getLoc!_initBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_initBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.firstBlock!_initBlockOperands {region : RegionPtr} :
    (region.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).firstBlock =
    (region.get! ctx).firstBlock := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem RegionPtr.lastBlock!_initBlockOperands {region : RegionPtr} :
    (region.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).lastBlock =
    (region.get! ctx).lastBlock := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem RegionPtr.parent!_initBlockOperands {region : RegionPtr} :
    (region.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).parent =
    (region.get! ctx).parent := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getFirstUse!_initBlockOperands {value : ValuePtr} :
    value.getFirstUse! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    value.getFirstUse! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getType!_initBlockOperands {value : ValuePtr} :
    value.getType! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    value.getType! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem OpOperandPtrPtr.get!_initBlockOperands {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    opOperandPtr.get! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[grind =, simp_getset]
theorem Rewriter.initBlockOperands_inBounds (ptr : GenericPtr) :
    ptr.InBounds (initBlockOperands ctx op operands n h₁ h₂ h₃ hn) ↔
    match ptr with
    | .blockOperand operandPtr
    | .blockOperandPtr (.blockOperandNextUse operandPtr) =>
      if operandPtr.op = op then
        operandPtr.index < op.getNumSuccessors! ctx + n
      else
        ptr.InBounds ctx
    | _ => ptr.InBounds ctx := by
  fun_induction Rewriter.initBlockOperands <;>
    grind [BlockOperandPtr.inBounds_def]

end Rewriter.initBlockOperands

end Veir
