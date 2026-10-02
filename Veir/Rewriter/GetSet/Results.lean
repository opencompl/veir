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
/-! ## `Rewriter.pushResult` -/

section Rewriter.pushResult

variable {op : OperationPtr}

attribute [local grind] Rewriter.pushResult

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_pushResult {block : BlockPtr} :
    block.getLastOp! (Rewriter.pushResult ctx op type hop) = block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_pushResult {block : BlockPtr} :
    block.getFirstOp! (Rewriter.pushResult ctx op type hop) = block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_pushResult {block : BlockPtr} :
    block.getParent! (Rewriter.pushResult ctx op type hop) = block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_pushResult {block : BlockPtr} :
    block.getNextBlock! (Rewriter.pushResult ctx op type hop) = block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_pushResult {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.pushResult ctx op type hop) = block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_pushResult {block : BlockPtr} :
    block.getFirstUse! (Rewriter.pushResult ctx op type hop) = block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_pushResult {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.pushResult ctx op type hop) = operation.getPrevOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_pushResult {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.pushResult ctx op type hop) = operation.getNextOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_pushResult {operation : OperationPtr} :
    operation.getParent! (Rewriter.pushResult ctx op type hop) = operation.getParent! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_pushResult {operation : OperationPtr} :
    operation.getOpType! (Rewriter.pushResult ctx op type hop) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_pushResult {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.pushResult ctx op type hop) = operation.getAttributes! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_pushResult {operation : OperationPtr} :
    operation.getProperties! (Rewriter.pushResult ctx op type hop) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getNumResults!_pushResult {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.pushResult ctx op type hop) =
    if operation = op then operation.getNumResults! ctx + 1
    else operation.getNumResults! ctx := by
  grind

@[grind =, simp_getset]
theorem OpResultPtr.getOwner!_pushResult {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.pushResult ctx op type hop) = if opResult = op.nextResult ctx then op else opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[grind =, simp_getset]
theorem OpResultPtr.getIndex!_pushResult {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.pushResult ctx op type hop) = if opResult = op.nextResult ctx then op.getNumResults! ctx else opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_pushResult {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.pushResult ctx op type hop) = if opResult = op.nextResult ctx then none else opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[grind =, simp_getset]
theorem OpResultPtr.getType!_pushResult {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.pushResult ctx op type hop) = if opResult = op.nextResult ctx then type else opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_pushResult {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.pushResult ctx op type hop) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_pushResult {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.pushResult ctx op type hop) = opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_pushResult {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.pushResult ctx op type hop) = opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_pushResult {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.pushResult ctx op type hop) = opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_pushResult {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.pushResult ctx op type hop) = opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_pushResult {operation : OperationPtr} :
    operation.getOperands! (Rewriter.pushResult ctx op type hop) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_pushResult {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.pushResult ctx op type hop) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_pushResult {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (Rewriter.pushResult ctx op type hop) = blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_pushResult {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (Rewriter.pushResult ctx op type hop) = blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_pushResult {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (Rewriter.pushResult ctx op type hop) = blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_pushResult {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (Rewriter.pushResult ctx op type hop) = blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_pushResult {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.pushResult ctx op type hop) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_pushResult {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.pushResult ctx op type hop) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_pushResult {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.pushResult ctx op type hop) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_pushResult {operation : OperationPtr} :
    operation.getRegion! (Rewriter.pushResult ctx op type hop) idx =
    operation.getRegion! ctx idx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtrPtr.get!_pushResult {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.pushResult ctx op type hop) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_pushResult {block : BlockPtr} :
    block.getNumArguments! (Rewriter.pushResult ctx op type hop) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_pushResult {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.pushResult ctx op type hop) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_pushResult {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.pushResult ctx op type hop) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_pushResult {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.pushResult ctx op type hop) = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_pushResult {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.pushResult ctx op type hop) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_pushResult {region : RegionPtr} :
    region.getLastBlock! (Rewriter.pushResult ctx op type hop) = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_pushResult {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.pushResult ctx op type hop) = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_pushResult {region : RegionPtr} :
    region.getParent! (Rewriter.pushResult ctx op type hop) = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[grind =, simp_getset]
theorem ValuePtr.getFirstUse!_pushResult {value : ValuePtr} :
    value.getFirstUse! (Rewriter.pushResult ctx op type hop) =
    if value = op.nextResult ctx then
      none
    else
      value.getFirstUse! ctx := by
  grind

@[grind =, simp_getset]
theorem ValuePtr.getType!_pushResult {value : ValuePtr} :
    value.getType! (Rewriter.pushResult ctx op type hop) =
    if value = op.nextResult ctx then
      type
    else
      value.getType! ctx := by
  grind

@[grind =, simp_getset]
theorem OpOperandPtrPtr.get!_pushResult {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.pushResult ctx op type hop) =
    if opOperandPtr = OpOperandPtrPtr.valueFirstUse (op.nextResult ctx) then
      none
    else
      opOperandPtr.get! ctx := by
  grind

end Rewriter.pushResult
/-! ## `Rewriter.initOpResults` -/

section Rewriter.initOpResults

variable {op : OperationPtr}

attribute [local grind] Rewriter.initOpResults

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_initOpResults {block : BlockPtr} :
    block.getLastOp! (Rewriter.initOpResults ctx op types index hop hidx) = block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_initOpResults {block : BlockPtr} :
    block.getFirstOp! (Rewriter.initOpResults ctx op types index hop hidx) = block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_initOpResults {block : BlockPtr} :
    block.getParent! (Rewriter.initOpResults ctx op types index hop hidx) = block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_initOpResults {block : BlockPtr} :
    block.getNextBlock! (Rewriter.initOpResults ctx op types index hop hidx) = block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_initOpResults {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.initOpResults ctx op types index hop hidx) = block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_initOpResults {block : BlockPtr} :
    block.getFirstUse! (Rewriter.initOpResults ctx op types index hop hidx) = block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_initOpResults {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.initOpResults ctx op types index hop hidx) = operation.getPrevOp! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_initOpResults {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.initOpResults ctx op types index hop hidx) = operation.getNextOp! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_initOpResults {operation : OperationPtr} :
    operation.getParent! (Rewriter.initOpResults ctx op types index hop hidx) = operation.getParent! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_initOpResults {operation : OperationPtr} :
    operation.getOpType! (Rewriter.initOpResults ctx op types index hop hidx) =
    operation.getOpType! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_initOpResults {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.initOpResults ctx op types index hop hidx) = operation.getAttributes! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_initOpResults {operation : OperationPtr} :
    operation.getProperties! (Rewriter.initOpResults ctx op types index hop hidx) opCode =
    operation.getProperties! ctx opCode := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_initOpResults {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.initOpResults ctx op types index hop hidx) =
    if operation = op then op.getNumResults! ctx + (types.size - index) else operation.getNumResults! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[grind =, simp_getset]
theorem OpResultPtr.getType!_initOpResults {opResult : OpResultPtr} {index : Nat} {hidx} :
    opResult.getType! (Rewriter.initOpResults ctx op types index hop hidx) = if h : opResult.op = op ∧ opResult.index < types.size ∧ op.getNumResults! ctx ≤ opResult.index then types[opResult.index] else opResult.getType! ctx := by
  fun_induction Rewriter.initOpResults <;> grind [cases OpResultPtr]

@[grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_initOpResults {opResult : OpResultPtr} {index : Nat} {hidx} :
    opResult.getFirstUse! (Rewriter.initOpResults ctx op types index hop hidx) = if opResult.op = op ∧ opResult.index < types.size ∧ op.getNumResults! ctx ≤ opResult.index then none else opResult.getFirstUse! ctx := by
  fun_induction Rewriter.initOpResults <;> grind [cases OpResultPtr]

@[grind =, simp_getset]
theorem OpResultPtr.getIndex!_initOpResults {opResult : OpResultPtr} {index : Nat} {hidx} :
    (opResult.getIndex! (Rewriter.initOpResults ctx op types index hop hidx)) =
    if opResult.op = op ∧ opResult.index < types.size ∧ op.getNumResults! ctx ≤ opResult.index then
      opResult.index
    else (opResult.getIndex! ctx) := by
  fun_induction Rewriter.initOpResults <;> grind [cases OpResultPtr]

@[grind =, simp_getset]
theorem OpResultPtr.getOwner!_initOpResults {opResult : OpResultPtr} {index : Nat} {hidx} :
    opResult.getOwner! (Rewriter.initOpResults ctx op types index hop hidx) = if opResult.op = op ∧ opResult.index < types.size ∧ op.getNumResults! ctx ≤ opResult.index then op else opResult.getOwner! ctx := by
  fun_induction Rewriter.initOpResults <;> grind [cases OpResultPtr]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_initOpResults {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.initOpResults ctx op types index hop hidx) = operation.getNumOperands! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_initOpResults {opOperand : OpOperandPtr} {index} {hidx} :
    opOperand.getValue! (Rewriter.initOpResults ctx op types index hop hidx) = opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_initOpResults {opOperand : OpOperandPtr} {index} {hidx} :
    opOperand.getOwner! (Rewriter.initOpResults ctx op types index hop hidx) = opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_initOpResults {opOperand : OpOperandPtr} {index} {hidx} :
    opOperand.getBack! (Rewriter.initOpResults ctx op types index hop hidx) = opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_initOpResults {opOperand : OpOperandPtr} {index} {hidx} :
    opOperand.getNextUse! (Rewriter.initOpResults ctx op types index hop hidx) = opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_initOpResults {operation : OperationPtr} {index} {hidx} :
    operation.getOperands! (Rewriter.initOpResults ctx op types index hop hidx) = operation.getOperands! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_initOpResults {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.initOpResults ctx op types index hop hidx) =
    operation.getNumSuccessors! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_initOpResults {blockOperand : BlockOperandPtr} {index} {hidx} :
    blockOperand.getValue! (Rewriter.initOpResults ctx op types index hop hidx) = blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_initOpResults {blockOperand : BlockOperandPtr} {index} {hidx} :
    blockOperand.getOwner! (Rewriter.initOpResults ctx op types index hop hidx) = blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_initOpResults {blockOperand : BlockOperandPtr} {index} {hidx} :
    blockOperand.getBack! (Rewriter.initOpResults ctx op types index hop hidx) = blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_initOpResults {blockOperand : BlockOperandPtr} {index} {hidx} :
    blockOperand.getNextUse! (Rewriter.initOpResults ctx op types index hop hidx) = blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_initOpResults {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.initOpResults ctx op types index hop hidx) i =
    operation.getSuccessor! ctx i := by
  fun_induction Rewriter.initOpResults <;> grind [OperationPtr.getSuccessor!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_initOpResults {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.initOpResults ctx op types index hop hidx) =
    operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_initOpResults,
    OperationPtr.getNumSuccessors!_initOpResults]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_initOpResults {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.initOpResults ctx op types index hop hidx) =
    operation.getNumRegions! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_initOpResults {operation : OperationPtr} :
    operation.getRegion! (Rewriter.initOpResults ctx op types index hop hidx) idx =
    operation.getRegion! ctx idx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtrPtr.get!_initOpResults {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.initOpResults ctx op types index hop hidx) =
    blockOperandPtr.get! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_initOpResults {block : BlockPtr} :
    block.getNumArguments! (Rewriter.initOpResults ctx op types index hop hidx) =
    block.getNumArguments! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_initOpResults {blockArg : BlockArgumentPtr} {index} {hidx} :
    blockArg.getOwner! (Rewriter.initOpResults ctx op types index hop hidx) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_initOpResults {blockArg : BlockArgumentPtr} {index} {hidx} :
    blockArg.getIndex! (Rewriter.initOpResults ctx op types index hop hidx) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_initOpResults {blockArg : BlockArgumentPtr} {index} {hidx} :
    blockArg.getFirstUse! (Rewriter.initOpResults ctx op types index hop hidx) = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_initOpResults {blockArg : BlockArgumentPtr} {index} {hidx} :
    blockArg.getType! (Rewriter.initOpResults ctx op types index hop hidx) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_initOpResults {region : RegionPtr} :
    region.getLastBlock! (Rewriter.initOpResults ctx op types index hop hidx) = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_initOpResults {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.initOpResults ctx op types index hop hidx) = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_initOpResults {region : RegionPtr} :
    region.getParent! (Rewriter.initOpResults ctx op types index hop hidx) = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  fun_induction Rewriter.initOpResults <;> grind

@[grind =, simp_getset]
theorem ValuePtr.getFirstUse!_initOpResults {value : ValuePtr} :
    value.getFirstUse! (Rewriter.initOpResults ctx op types index hop hidx) =
    match value with
    | .opResult opRes =>
      if opRes.op = op ∧ opRes.index < types.size ∧ op.getNumResults! ctx ≤ opRes.index then
        none
      else value.getFirstUse! ctx
    | _ => value.getFirstUse! ctx := by
  fun_induction Rewriter.initOpResults
  · grind
  · cases value <;> grind [cases OpResultPtr, cases ValuePtr]

@[grind =, simp_getset]
theorem ValuePtr.getType!_initOpResults {value : ValuePtr} :
    value.getType! (Rewriter.initOpResults ctx op types index hop hidx) =
    match value with
    | .opResult opRes =>
      if _ : opRes.op = op ∧ opRes.index < types.size ∧ op.getNumResults! ctx ≤ opRes.index then
        types[opRes.index]
      else value.getType! ctx
    | _ => value.getType! ctx := by
  fun_induction Rewriter.initOpResults
  · grind
  · cases value <;> grind [cases OpResultPtr, cases ValuePtr]

@[grind =, simp_getset]
theorem OpOperandPtrPtr.get!_initOpResults {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.initOpResults ctx op types index hop hidx) =
    match opOperandPtr with
    | .valueFirstUse (.opResult opRes) =>
      if _ : opRes.op = op ∧ opRes.index < types.size ∧ op.getNumResults! ctx ≤ opRes.index then none
      else (opRes.getFirstUse! ctx)
    | _ => opOperandPtr.get! ctx := by
  cases opOperandPtr
  · grind
  · simp only [get!_valueFirstUse_eq, ValuePtr.getFirstUse!_initOpResults, dite_eq_ite]; grind

@[grind =, simp_getset]
theorem Rewriter.initOpResults_inBounds (ptr : GenericPtr) :
    ptr.InBounds (initOpResults ctx op types index hop hidx) ↔
    match ptr with
    | .opResult resPtr
    | .value (.opResult resPtr)
    | .opOperandPtr (.valueFirstUse (.opResult resPtr)) =>
      if resPtr.op = op then
        resPtr.index < op.getNumResults! ctx + (types.size - index)
      else
        ptr.InBounds ctx
    | _ => ptr.InBounds ctx := by
  fun_induction Rewriter.initOpResults <;>
    grind [OpResultPtr.inBounds_def]

end Rewriter.initOpResults

end Veir
