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

/-! ## `Rewriter.pushBlockOperand` -/

section Rewriter.pushBlockOperand

variable {opPtr : OperationPtr} {blockPtr : BlockPtr}

attribute [local grind] Rewriter.pushBlockOperand

@[grind =, simp_getset]
theorem BlockPtr.firstUse!_pushBlockOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).firstUse =
    if block = blockPtr then some (opPtr.nextBlockOperand! ctx) else (block.get! ctx).firstUse := by
  grind [OperationPtr.getBlockOperand_def]

@[grind =, simp_getset]
theorem BlockPtr.getFirstUse!_pushBlockOperand {block : BlockPtr} :
    block.getFirstUse! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = if block = blockPtr then some (opPtr.nextBlockOperand! ctx) else block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  first
  | exact BlockPtr.firstUse!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.prev!_pushBlockOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_pushBlockOperand {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  first
  | exact BlockPtr.prev!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.next!_pushBlockOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_pushBlockOperand {block : BlockPtr} :
    block.getNextBlock! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  first
  | exact BlockPtr.next!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.parent!_pushBlockOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_pushBlockOperand {block : BlockPtr} :
    block.getParent! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.parent!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.firstOp!_pushBlockOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_pushBlockOperand {block : BlockPtr} :
    block.getFirstOp! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  first
  | exact BlockPtr.firstOp!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.lastOp!_pushBlockOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_pushBlockOperand {block : BlockPtr} :
    block.getLastOp! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  first
  | exact BlockPtr.lastOp!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.prev!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_pushBlockOperand {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  first
  | exact OperationPtr.prev!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.next!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_pushBlockOperand {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  first
  | exact OperationPtr.next!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.parent!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_pushBlockOperand {operation : OperationPtr} :
    operation.getParent! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.parent!_pushBlockOperand
  | grind

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
theorem OperationPtr.getAttributes!_pushBlockOperand {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  first
  | exact OperationPtr.attrs!_pushBlockOperand
  | grind

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
theorem OpResultPtr.getOwner!_pushBlockOperand {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  first
  | exact OpResultPtr.get!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_pushBlockOperand {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  first
  | exact OpResultPtr.get!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_pushBlockOperand {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  first
  | exact OpResultPtr.get!_pushBlockOperand
  | grind

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
theorem OpOperandPtr.getValue!_pushBlockOperand {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  first
  | exact OpOperandPtr.get!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_pushBlockOperand {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  first
  | exact OpOperandPtr.get!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_pushBlockOperand {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  first
  | exact OpOperandPtr.get!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_pushBlockOperand {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  first
  | exact OpOperandPtr.get!_pushBlockOperand
  | grind

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
theorem BlockOperandPtr.getValue!_pushBlockOperand {operand : BlockOperandPtr} :
    operand.getValue! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = if operand = opPtr.nextBlockOperand ctx then blockPtr else operand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  first
  | exact BlockOperandPtr.get!_pushBlockOperand
  | grind

@[grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_pushBlockOperand {operand : BlockOperandPtr} :
    operand.getOwner! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = if operand = opPtr.nextBlockOperand ctx then opPtr else operand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  first
  | exact BlockOperandPtr.get!_pushBlockOperand
  | grind

@[grind =, simp_getset]
theorem BlockOperandPtr.getBack!_pushBlockOperand {operand : BlockOperandPtr} :
    operand.getBack! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = if operand = opPtr.nextBlockOperand ctx then (.blockFirstUse blockPtr) else (if (blockPtr.get! ctx).firstUse = some operand then .blockOperandNextUse (opPtr.nextBlockOperand ctx) else operand.getBack! ctx) := by
  simp only [BlockOperandPtr.getBack!_def]
  first
  | exact BlockOperandPtr.get!_pushBlockOperand
  | grind

@[grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_pushBlockOperand {operand : BlockOperandPtr} :
    operand.getNextUse! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = if operand = opPtr.nextBlockOperand ctx then ((blockPtr.get! ctx).firstUse) else operand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  first
  | exact BlockOperandPtr.get!_pushBlockOperand
  | grind

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

theorem BlockOperandPtr.getValue!_pushBlockOperand' {operandPtr : BlockOperandPtr} :
    operandPtr.getValue! (Rewriter.pushBlockOperand ctx opPtr blockPtr opPtrInBounds blockPtrInBounds ctxInBounds) = if operandPtr = opPtr.nextBlockOperand ctx then blockPtr else operandPtr.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  first
  | exact BlockOperandPtr.get!_pushBlockOperand'
  | grind [BlockOperandPtr.get!_pushBlockOperand']

theorem BlockOperandPtr.getOwner!_pushBlockOperand' {operandPtr : BlockOperandPtr} :
    operandPtr.getOwner! (Rewriter.pushBlockOperand ctx opPtr blockPtr opPtrInBounds blockPtrInBounds ctxInBounds) = if operandPtr = opPtr.nextBlockOperand ctx then opPtr else operandPtr.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  first
  | exact BlockOperandPtr.get!_pushBlockOperand'
  | grind [BlockOperandPtr.get!_pushBlockOperand']

theorem BlockOperandPtr.getBack!_pushBlockOperand' {operandPtr : BlockOperandPtr} :
    operandPtr.getBack! (Rewriter.pushBlockOperand ctx opPtr blockPtr opPtrInBounds blockPtrInBounds ctxInBounds) = if operandPtr = opPtr.nextBlockOperand ctx then (BlockOperandPtrPtr.blockFirstUse blockPtr) else if (blockPtr.get! ctx).firstUse = some operandPtr then (BlockOperandPtrPtr.blockOperandNextUse (opPtr.nextBlockOperand ctx)) else operandPtr.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  first
  | exact BlockOperandPtr.get!_pushBlockOperand'
  | grind [BlockOperandPtr.get!_pushBlockOperand']

theorem BlockOperandPtr.getNextUse!_pushBlockOperand' {operandPtr : BlockOperandPtr} :
    operandPtr.getNextUse! (Rewriter.pushBlockOperand ctx opPtr blockPtr opPtrInBounds blockPtrInBounds ctxInBounds) = if operandPtr = opPtr.nextBlockOperand ctx then ((blockPtr.get! ctx).firstUse) else operandPtr.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  first
  | exact BlockOperandPtr.get!_pushBlockOperand'
  | grind [BlockOperandPtr.get!_pushBlockOperand']

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
theorem BlockArgumentPtr.get!_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) =
    blockArg.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  first
  | exact BlockArgumentPtr.get!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  first
  | exact BlockArgumentPtr.get!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  first
  | exact BlockArgumentPtr.get!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  first
  | exact BlockArgumentPtr.get!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem RegionPtr.firstBlock!_pushBlockOperand {region : RegionPtr} :
    (region.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).firstBlock =
    (region.get! ctx).firstBlock := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_pushBlockOperand {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  first
  | exact RegionPtr.firstBlock!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem RegionPtr.lastBlock!_pushBlockOperand {region : RegionPtr} :
    (region.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).lastBlock =
    (region.get! ctx).lastBlock := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_pushBlockOperand {region : RegionPtr} :
    region.getLastBlock! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  first
  | exact RegionPtr.lastBlock!_pushBlockOperand
  | grind

@[simp, grind =, simp_getset]
theorem RegionPtr.parent!_pushBlockOperand {region : RegionPtr} :
    (region.get! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃)).parent =
    (region.get! ctx).parent := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_pushBlockOperand {region : RegionPtr} :
    region.getParent! (Rewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂ h₃) = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  first
  | exact RegionPtr.parent!_pushBlockOperand
  | grind

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
theorem BlockPtr.getPrevBlock!_initBlockOperands {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  first
  | exact BlockPtr.prev!_initBlockOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.next!_initBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).next =
    (block.get! ctx).next := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_initBlockOperands {block : BlockPtr} :
    block.getNextBlock! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  first
  | exact BlockPtr.next!_initBlockOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.parent!_initBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).parent =
    (block.get! ctx).parent := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_initBlockOperands {block : BlockPtr} :
    block.getParent! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.parent!_initBlockOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.firstOp!_initBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).firstOp =
    (block.get! ctx).firstOp := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_initBlockOperands {block : BlockPtr} :
    block.getFirstOp! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  first
  | exact BlockPtr.firstOp!_initBlockOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.lastOp!_initBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).lastOp =
    (block.get! ctx).lastOp := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_initBlockOperands {block : BlockPtr} :
    block.getLastOp! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  first
  | exact BlockPtr.lastOp!_initBlockOperands
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.prev!_initBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).prev =
    (operation.get! ctx).prev := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_initBlockOperands {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  first
  | exact OperationPtr.prev!_initBlockOperands
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.next!_initBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).next =
    (operation.get! ctx).next := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_initBlockOperands {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  first
  | exact OperationPtr.next!_initBlockOperands
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.parent!_initBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).parent =
    (operation.get! ctx).parent := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_initBlockOperands {operation : OperationPtr} :
    operation.getParent! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.parent!_initBlockOperands
  | grind

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
theorem OperationPtr.getAttributes!_initBlockOperands {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  first
  | exact OperationPtr.attrs!_initBlockOperands
  | grind

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
theorem OpResultPtr.getOwner!_initBlockOperands {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  first
  | exact OpResultPtr.get!_initBlockOperands
  | grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_initBlockOperands {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  first
  | exact OpResultPtr.get!_initBlockOperands
  | grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_initBlockOperands {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  first
  | exact OpResultPtr.get!_initBlockOperands
  | grind

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
theorem OpOperandPtr.getValue!_initBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  first
  | exact OpOperandPtr.get!_initBlockOperands
  | grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_initBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  first
  | exact OpOperandPtr.get!_initBlockOperands
  | grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_initBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  first
  | exact OpOperandPtr.get!_initBlockOperands
  | grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_initBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  first
  | exact OpOperandPtr.get!_initBlockOperands
  | grind

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
theorem BlockArgumentPtr.get!_initBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) =
    blockArg.get! ctx := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_initBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  first
  | exact BlockArgumentPtr.get!_initBlockOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_initBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  first
  | exact BlockArgumentPtr.get!_initBlockOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_initBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  first
  | exact BlockArgumentPtr.get!_initBlockOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_initBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  first
  | exact BlockArgumentPtr.get!_initBlockOperands
  | grind

@[simp, grind =, simp_getset]
theorem RegionPtr.firstBlock!_initBlockOperands {region : RegionPtr} :
    (region.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).firstBlock =
    (region.get! ctx).firstBlock := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_initBlockOperands {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  first
  | exact RegionPtr.firstBlock!_initBlockOperands
  | grind

@[simp, grind =, simp_getset]
theorem RegionPtr.lastBlock!_initBlockOperands {region : RegionPtr} :
    (region.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).lastBlock =
    (region.get! ctx).lastBlock := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_initBlockOperands {region : RegionPtr} :
    region.getLastBlock! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  first
  | exact RegionPtr.lastBlock!_initBlockOperands
  | grind

@[simp, grind =, simp_getset]
theorem RegionPtr.parent!_initBlockOperands {region : RegionPtr} :
    (region.get! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn)).parent =
    (region.get! ctx).parent := by
  fun_induction Rewriter.initBlockOperands <;> grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_initBlockOperands {region : RegionPtr} :
    region.getParent! (Rewriter.initBlockOperands ctx op operands n h₁ h₂ h₃ hn) = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  first
  | exact RegionPtr.parent!_initBlockOperands
  | grind

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
