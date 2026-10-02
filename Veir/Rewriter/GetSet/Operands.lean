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
/-! ## `Rewriter.pushOperand` -/

section Rewriter.pushOperand

variable {opPtr : OperationPtr} {valuePtr : ValuePtr}

attribute [local grind] Rewriter.pushOperand

@[simp, grind =, simp_getset]
theorem BlockPtr.firstUse!_pushOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_pushOperand {block : BlockPtr} :
    block.getFirstUse! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  first
  | exact BlockPtr.firstUse!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.prev!_pushOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_pushOperand {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  first
  | exact BlockPtr.prev!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.next!_pushOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_pushOperand {block : BlockPtr} :
    block.getNextBlock! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  first
  | exact BlockPtr.next!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.parent!_pushOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_pushOperand {block : BlockPtr} :
    block.getParent! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.parent!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.firstOp!_pushOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_pushOperand {block : BlockPtr} :
    block.getFirstOp! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  first
  | exact BlockPtr.firstOp!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.lastOp!_pushOperand {block : BlockPtr} :
    (block.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_pushOperand {block : BlockPtr} :
    block.getLastOp! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  first
  | exact BlockPtr.lastOp!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.prev!_pushOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_pushOperand {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  first
  | exact OperationPtr.prev!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.next!_pushOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_pushOperand {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  first
  | exact OperationPtr.next!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.parent!_pushOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_pushOperand {operation : OperationPtr} :
    operation.getParent! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.parent!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_pushOperand {operation : OperationPtr} :
    operation.getOpType! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.attrs!_pushOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_pushOperand {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  first
  | exact OperationPtr.attrs!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_pushOperand {operation : OperationPtr} :
    operation.getProperties! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_pushOperand {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    operation.getNumResults! ctx := by
  grind

@[grind =, simp_getset]
theorem OpResultPtr.get!_pushOperand {opResult : OpResultPtr} :
    opResult.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    if valuePtr = opResult then
      { opResult.get! ctx with firstUse := some (opPtr.nextOperand! ctx) }
    else
      opResult.get! ctx := by
  grind [OperationPtr.getOpOperand_def]

@[grind =, simp_getset]
theorem OpResultPtr.getOwner!_pushOperand {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  first
  | exact OpResultPtr.get!_pushOperand
  | grind

@[grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_pushOperand {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = if valuePtr = opResult then (some (opPtr.nextOperand! ctx)) else opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  first
  | exact OpResultPtr.get!_pushOperand
  | grind

@[grind =, simp_getset]
theorem OpResultPtr.getType!_pushOperand {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  first
  | exact OpResultPtr.get!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_pushOperand {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    if operation = opPtr then
      (operation.getNumOperands! ctx) + 1
    else
      operation.getNumOperands! ctx := by
  grind

@[grind =, simp_getset]
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

@[grind =, simp_getset]
theorem OpOperandPtr.getValue!_pushOperand {operand : OpOperandPtr} :
    operand.getValue! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = if operand = opPtr.nextOperand ctx then valuePtr else operand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  first
  | exact OpOperandPtr.get!_pushOperand
  | grind

@[grind =, simp_getset]
theorem OpOperandPtr.getOwner!_pushOperand {operand : OpOperandPtr} :
    operand.getOwner! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = if operand = opPtr.nextOperand ctx then opPtr else operand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  first
  | exact OpOperandPtr.get!_pushOperand
  | grind

@[grind =, simp_getset]
theorem OpOperandPtr.getBack!_pushOperand {operand : OpOperandPtr} :
    operand.getBack! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = if operand = opPtr.nextOperand ctx then (.valueFirstUse valuePtr) else (if valuePtr.getFirstUse! ctx = some operand then .operandNextUse (opPtr.nextOperand ctx) else operand.getBack! ctx) := by
  simp only [OpOperandPtr.getBack!_def]
  first
  | exact OpOperandPtr.get!_pushOperand
  | grind

@[grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_pushOperand {operand : OpOperandPtr} :
    operand.getNextUse! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = if operand = opPtr.nextOperand ctx then (valuePtr.getFirstUse! ctx) else operand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  first
  | exact OpOperandPtr.get!_pushOperand
  | grind

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

theorem OpOperandPtr.getValue!_pushOperand' (valuePtr : ValuePtr) valuePtrInBounds (operandPtr : OpOperandPtr) :
    operandPtr.getValue! (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) = if operandPtr = opPtr.nextOperand ctx then valuePtr else operandPtr.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  first
  | exact OpOperandPtr.get!_pushOperand'
  | grind [OpOperandPtr.get!_pushOperand']

theorem OpOperandPtr.getOwner!_pushOperand' (valuePtr : ValuePtr) valuePtrInBounds (operandPtr : OpOperandPtr) :
    operandPtr.getOwner! (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) = if operandPtr = opPtr.nextOperand ctx then opPtr else operandPtr.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  first
  | exact OpOperandPtr.get!_pushOperand'
  | grind [OpOperandPtr.get!_pushOperand']

theorem OpOperandPtr.getBack!_pushOperand' (valuePtr : ValuePtr) valuePtrInBounds (operandPtr : OpOperandPtr) :
    operandPtr.getBack! (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) = if operandPtr = opPtr.nextOperand ctx then (OpOperandPtrPtr.valueFirstUse valuePtr) else if valuePtr.getFirstUse! ctx = some operandPtr then (OpOperandPtrPtr.operandNextUse (opPtr.nextOperand ctx)) else operandPtr.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  first
  | exact OpOperandPtr.get!_pushOperand'
  | grind [OpOperandPtr.get!_pushOperand']

theorem OpOperandPtr.getNextUse!_pushOperand' (valuePtr : ValuePtr) valuePtrInBounds (operandPtr : OpOperandPtr) :
    operandPtr.getNextUse! (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) = if operandPtr = opPtr.nextOperand ctx then (valuePtr.getFirstUse! ctx) else operandPtr.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  first
  | exact OpOperandPtr.get!_pushOperand'
  | grind [OpOperandPtr.get!_pushOperand']

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_pushOperand {operation : OperationPtr} :
    operation.getOperands! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    if operation = opPtr then
      (operation.getOperands! ctx).push valuePtr
    else
      operation.getOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_pushOperand {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.get!_pushOperand {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_pushOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  first
  | exact BlockOperandPtr.get!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_pushOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  first
  | exact BlockOperandPtr.get!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_pushOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  first
  | exact BlockOperandPtr.get!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_pushOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  first
  | exact BlockOperandPtr.get!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_pushOperand {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_pushOperand {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_pushOperand,
    OperationPtr.getNumSuccessors!_pushOperand]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_pushOperand {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_pushOperand {operation : OperationPtr} :
    operation.getRegion! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) idx =
    operation.getRegion! ctx idx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtrPtr.get!_pushOperand {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_pushOperand {block : BlockPtr} :
    block.getNumArguments! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.get!_pushOperand {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    if valuePtr = blockArg then
      { blockArg.get! ctx with firstUse := some (opPtr.nextOperand! ctx) }
    else
      blockArg.get! ctx := by
  grind [OperationPtr.getOpOperand_def]

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_pushOperand {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  first
  | exact BlockArgumentPtr.get!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_pushOperand {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  first
  | exact BlockArgumentPtr.get!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_pushOperand {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = if valuePtr = blockArg then (some (opPtr.nextOperand! ctx)) else blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  first
  | exact BlockArgumentPtr.get!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_pushOperand {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  first
  | exact BlockArgumentPtr.get!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem RegionPtr.firstBlock!_pushOperand {region : RegionPtr} :
    (region.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).firstBlock =
    (region.get! ctx).firstBlock := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_pushOperand {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  first
  | exact RegionPtr.firstBlock!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem RegionPtr.lastBlock!_pushOperand {region : RegionPtr} :
    (region.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).lastBlock =
    (region.get! ctx).lastBlock := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_pushOperand {region : RegionPtr} :
    region.getLastBlock! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  first
  | exact RegionPtr.lastBlock!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem RegionPtr.parent!_pushOperand {region : RegionPtr} :
    (region.get! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃)).parent =
    (region.get! ctx).parent := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_pushOperand {region : RegionPtr} :
    region.getParent! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  first
  | exact RegionPtr.parent!_pushOperand
  | grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getType!_pushOperand {value : ValuePtr} :
    value.getType! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    value.getType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getFirstUse!_pushOperand {value : ValuePtr} :
    value.getFirstUse! (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) =
    if value = valuePtr then some (opPtr.nextOperand! ctx) else value.getFirstUse! ctx := by
  grind [OperationPtr.getOpOperand_def]

@[simp, grind =, simp_getset]
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

@[simp, grind =, simp_getset]
theorem BlockPtr.firstUse!_initOpOperands {block : BlockPtr} :
    (block.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).firstUse =
    (block.get! ctx).firstUse := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_initOpOperands {block : BlockPtr} :
    block.getFirstUse! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) = block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  first
  | exact BlockPtr.firstUse!_initOpOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.prev!_initOpOperands {block : BlockPtr} :
    (block.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).prev =
    (block.get! ctx).prev := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_initOpOperands {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) = block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  first
  | exact BlockPtr.prev!_initOpOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.next!_initOpOperands {block : BlockPtr} :
    (block.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).next =
    (block.get! ctx).next := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_initOpOperands {block : BlockPtr} :
    block.getNextBlock! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) = block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  first
  | exact BlockPtr.next!_initOpOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.parent!_initOpOperands {block : BlockPtr} :
    (block.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).parent =
    (block.get! ctx).parent := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_initOpOperands {block : BlockPtr} :
    block.getParent! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) = block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.parent!_initOpOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.firstOp!_initOpOperands {block : BlockPtr} :
    (block.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).firstOp =
    (block.get! ctx).firstOp := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_initOpOperands {block : BlockPtr} :
    block.getFirstOp! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) = block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  first
  | exact BlockPtr.firstOp!_initOpOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockPtr.lastOp!_initOpOperands {block : BlockPtr} :
    (block.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).lastOp =
    (block.get! ctx).lastOp := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_initOpOperands {block : BlockPtr} :
    block.getLastOp! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) = block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  first
  | exact BlockPtr.lastOp!_initOpOperands
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.prev!_initOpOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).prev =
    (operation.get! ctx).prev := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_initOpOperands {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) = operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  first
  | exact OperationPtr.prev!_initOpOperands
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.next!_initOpOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).next =
    (operation.get! ctx).next := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_initOpOperands {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) = operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  first
  | exact OperationPtr.next!_initOpOperands
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.parent!_initOpOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).parent =
    (operation.get! ctx).parent := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_initOpOperands {operation : OperationPtr} :
    operation.getParent! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) = operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.parent!_initOpOperands
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_initOpOperands {operation : OperationPtr} :
    operation.getOpType! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    operation.getOpType! ctx := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.attrs!_initOpOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).attrs =
    (operation.get! ctx).attrs := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_initOpOperands {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) = operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  first
  | exact OperationPtr.attrs!_initOpOperands
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_initOpOperands {operation : OperationPtr} :
    operation.getProperties! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) opCode =
    operation.getProperties! ctx opCode := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_initOpOperands {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    operation.getNumResults! ctx := by
  fun_induction Rewriter.initOpOperands <;> grind

/--
OpResultPtr.get!_initOpOperands is too complex to be expressed, and should not be needed in practice,
as we should reason at a higher-level abstraction at this point.
-/

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_initOpOperands {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    operation.getNumSuccessors! ctx := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.get!_initOpOperands {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    blockOperand.get! ctx := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_initOpOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) = blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  first
  | exact BlockOperandPtr.get!_initOpOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_initOpOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) = blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  first
  | exact BlockOperandPtr.get!_initOpOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_initOpOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) = blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  first
  | exact BlockOperandPtr.get!_initOpOperands
  | grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_initOpOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) = blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  first
  | exact BlockOperandPtr.get!_initOpOperands
  | grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_initOpOperands {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) i =
    operation.getSuccessor! ctx i := by
  fun_induction Rewriter.initOpOperands <;> grind [OperationPtr.getSuccessor!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_initOpOperands {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_initOpOperands,
    OperationPtr.getNumSuccessors!_initOpOperands]

@[grind =>, simp_getset]
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
@[grind =>, simp_getset]
theorem OperationPtr.getOperands!_initOpOperands {operation : OperationPtr} :
    operation.getOperands! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    if operation = op then
      (operation.getOperands! ctx) ++ operands.extract (operands.size - n) operands.size
    else
      operation.getOperands! ctx := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_initOpOperands {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    operation.getNumRegions! ctx := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_initOpOperands {operation : OperationPtr} :
    operation.getRegion! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) idx =
    operation.getRegion! ctx idx := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtrPtr.get!_initOpOperands {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    blockOperandPtr.get! ctx := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_initOpOperands {block : BlockPtr} :
    block.getNumArguments! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    block.getNumArguments! ctx := by
  fun_induction Rewriter.initOpOperands <;> grind

/-
BlockArgumentPtr.get!_initOpOperands is too complex to be expressed, and should not be needed
in practice, as we should reason at a higher-level abstraction at this point.
-/

@[simp, grind =, simp_getset]
theorem RegionPtr.firstBlock!_initOpOperands {region : RegionPtr} :
    (region.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).firstBlock =
    (region.get! ctx).firstBlock := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_initOpOperands {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  first
  | exact RegionPtr.firstBlock!_initOpOperands
  | grind

@[simp, grind =, simp_getset]
theorem RegionPtr.lastBlock!_initOpOperands {region : RegionPtr} :
    (region.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).lastBlock =
    (region.get! ctx).lastBlock := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_initOpOperands {region : RegionPtr} :
    region.getLastBlock! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  first
  | exact RegionPtr.lastBlock!_initOpOperands
  | grind

@[simp, grind =, simp_getset]
theorem RegionPtr.parent!_initOpOperands {region : RegionPtr} :
    (region.get! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn)).parent =
    (region.get! ctx).parent := by
  fun_induction Rewriter.initOpOperands <;> grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_initOpOperands {region : RegionPtr} :
    region.getParent! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  first
  | exact RegionPtr.parent!_initOpOperands
  | grind

/-
ValuePtr.getFirstUse!_initOpOperands is too complex to be expressed, and should not be needed
in practice, as we should reason at a higher-level abstraction at this point.
-/

@[simp, grind =, simp_getset]
theorem ValuePtr.getType!_initOpOperands {value : ValuePtr} :
    value.getType! (Rewriter.initOpOperands ctx op h₁ operands h₂ h₃ n hn) =
    value.getType! ctx := by
  fun_induction Rewriter.initOpOperands <;> grind

/-
OpOperandPtrPtr.get!_initOpOperands is too complex to be expressed, and should not be needed
in practice, as we should reason at a higher-level abstraction at this point.
-/

@[grind =, simp_getset]
theorem Rewriter.initOpOperands_inBounds (ptr : GenericPtr) :
    ptr.InBounds (initOpOperands ctx op h₁ operands h₂ h₃ n hn) ↔
    match ptr with
    | .opOperand operandPtr
    | .opOperandPtr (.operandNextUse operandPtr) =>
      if operandPtr.op = op then
        operandPtr.index < op.getNumOperands! ctx + n
      else
        ptr.InBounds ctx
    | _ => ptr.InBounds ctx := by
  fun_induction Rewriter.initOpOperands <;>
    grind [OpOperandPtr.inBounds_def]

end Rewriter.initOpOperands

end Veir
