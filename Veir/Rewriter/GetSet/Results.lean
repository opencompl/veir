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
/-! ## `Rewriter.pushResult` -/

section Rewriter.pushResult

variable {op : OperationPtr}

attribute [local grind] Rewriter.pushResult

@[simp, grind =]
theorem BlockPtr.get!_pushResult {block : BlockPtr} :
    block.get! (Rewriter.pushResult ctx op type hop) =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_pushResult {operation : OperationPtr} :
    (operation.get! (Rewriter.pushResult ctx op type hop)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_pushResult {operation : OperationPtr} :
    (operation.get! (Rewriter.pushResult ctx op type hop)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_pushResult {operation : OperationPtr} :
    (operation.get! (Rewriter.pushResult ctx op type hop)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_pushResult {operation : OperationPtr} :
    (operation.get! (Rewriter.pushResult ctx op type hop)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_pushResult {operation : OperationPtr} :
    (operation.get! (Rewriter.pushResult ctx op type hop)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_pushResult {operation : OperationPtr} :
    operation.getProperties! (Rewriter.pushResult ctx op type hop) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[grind =]
theorem OperationPtr.getNumResults!_pushResult {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.pushResult ctx op type hop) =
    if operation = op then operation.getNumResults! ctx + 1
    else operation.getNumResults! ctx := by
  grind

@[grind =]
theorem OpResultPtr.get!_pushResult {opResult : OpResultPtr} :
    opResult.get! (Rewriter.pushResult ctx op type hop) =
    if opResult = op.nextResult ctx then
      { type := type, firstUse := none, index := op.getNumResults! ctx, owner := op }
    else opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_pushResult {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.pushResult ctx op type hop) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_pushResult {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.pushResult ctx op type hop) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_pushResult {operation : OperationPtr} :
    operation.getOperands! (Rewriter.pushResult ctx op type hop) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_pushResult {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.pushResult ctx op type hop) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_pushResult {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.pushResult ctx op type hop) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_pushResult {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.pushResult ctx op type hop) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_pushResult {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.pushResult ctx op type hop) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_pushResult {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.pushResult ctx op type hop) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_pushResult {operation : OperationPtr} :
    operation.getRegion! (Rewriter.pushResult ctx op type hop) idx =
    operation.getRegion! ctx idx := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_pushResult {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.pushResult ctx op type hop) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_pushResult {block : BlockPtr} :
    block.getNumArguments! (Rewriter.pushResult ctx op type hop) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_pushResult {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.pushResult ctx op type hop) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_pushResult {region : RegionPtr} :
    region.get! (Rewriter.pushResult ctx op type hop) =
    region.get! ctx := by
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_pushResult {value : ValuePtr} :
    value.getFirstUse! (Rewriter.pushResult ctx op type hop) =
    if value = op.nextResult ctx then
      none
    else
      value.getFirstUse! ctx := by
  grind

@[grind =]
theorem ValuePtr.getType!_pushResult {value : ValuePtr} :
    value.getType! (Rewriter.pushResult ctx op type hop) =
    if value = op.nextResult ctx then
      type
    else
      value.getType! ctx := by
  grind

@[grind =]
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

@[simp, grind =]
theorem BlockPtr.get!_initOpResults {block : BlockPtr} :
    block.get! (Rewriter.initOpResults ctx op types index hop hidx) = block.get! ctx := by
  fun_induction Rewriter.initOpResults <;> grind


@[simp, grind =]
theorem OperationPtr.prev!_initOpResults {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpResults ctx op types index hop hidx)).prev =
    (operation.get! ctx).prev := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.next!_initOpResults {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpResults ctx op types index hop hidx)).next =
    (operation.get! ctx).next := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.parent!_initOpResults {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpResults ctx op types index hop hidx)).parent =
    (operation.get! ctx).parent := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.opType!_initOpResults {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpResults ctx op types index hop hidx)).opType =
    (operation.get! ctx).opType := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.attrs!_initOpResults {operation : OperationPtr} :
    (operation.get! (Rewriter.initOpResults ctx op types index hop hidx)).attrs =
    (operation.get! ctx).attrs := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.getProperties!_initOpResults {operation : OperationPtr} :
    operation.getProperties! (Rewriter.initOpResults ctx op types index hop hidx) opCode =
    operation.getProperties! ctx opCode := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_initOpResults {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.initOpResults ctx op types index hop hidx) =
    if operation = op then op.getNumResults! ctx + (types.size - index) else operation.getNumResults! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[local grind =]
theorem OpResultPtr.get!_initOpResults {opResult : OpResultPtr} {index : Nat} {hidx} :
    opResult.get! (Rewriter.initOpResults ctx op types index hop hidx) =
    if h : opResult.op = op ∧ opResult.index < types.size ∧ op.getNumResults! ctx ≤ opResult.index then
      { type := types[opResult.index], firstUse := none, index := opResult.index, owner := op }
    else opResult.get! ctx := by
  fun_induction Rewriter.initOpResults <;> grind [cases OpResultPtr]

@[grind =]
theorem OpResultPtr.type!_initOpResults {opResult : OpResultPtr} {index : Nat} {hidx} :
    (opResult.get! (Rewriter.initOpResults ctx op types index hop hidx)).type =
    if h : opResult.op = op ∧ opResult.index < types.size ∧ op.getNumResults! ctx ≤ opResult.index then
      types[opResult.index]
    else (opResult.get! ctx).type := by
  grind

@[grind =]
theorem OpResultPtr.firstUse!_initOpResults {opResult : OpResultPtr} {index : Nat} {hidx} :
    (opResult.get! (Rewriter.initOpResults ctx op types index hop hidx)).firstUse =
    if opResult.op = op ∧ opResult.index < types.size ∧ op.getNumResults! ctx ≤ opResult.index then none
    else (opResult.get! ctx).firstUse := by
  grind

@[grind =]
theorem OpResultPtr.index!_initOpResults {opResult : OpResultPtr} {index : Nat} {hidx} :
    (opResult.get! (Rewriter.initOpResults ctx op types index hop hidx)).index =
    if opResult.op = op ∧ opResult.index < types.size ∧ op.getNumResults! ctx ≤ opResult.index then
      opResult.index
    else (opResult.get! ctx).index := by
  grind

@[grind =]
theorem OpResultPtr.owner!_initOpResults {opResult : OpResultPtr} {index : Nat} {hidx} :
    (opResult.get! (Rewriter.initOpResults ctx op types index hop hidx)).owner =
    if opResult.op = op ∧ opResult.index < types.size ∧ op.getNumResults! ctx ≤ opResult.index then op
    else (opResult.get! ctx).owner := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_initOpResults {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.initOpResults ctx op types index hop hidx) = operation.getNumOperands! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OpOperandPtr.get!_initOpResults {opOperand : OpOperandPtr} {index} {hidx} :
    opOperand.get! (Rewriter.initOpResults ctx op types index hop hidx) = opOperand.get! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.getOperands!_initOpResults {operation : OperationPtr} {index} {hidx} :
    operation.getOperands! (Rewriter.initOpResults ctx op types index hop hidx) = operation.getOperands! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_initOpResults {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.initOpResults ctx op types index hop hidx) =
    operation.getNumSuccessors! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem BlockOperandPtr.get!_initOpResults {blockOperand : BlockOperandPtr} {index} {hidx} :
    blockOperand.get! (Rewriter.initOpResults ctx op types index hop hidx) =
    blockOperand.get! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_initOpResults {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.initOpResults ctx op types index hop hidx) i =
    operation.getSuccessor! ctx i := by
  fun_induction Rewriter.initOpResults <;> grind [OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_initOpResults {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.initOpResults ctx op types index hop hidx) =
    operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_initOpResults,
    OperationPtr.getNumSuccessors!_initOpResults]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_initOpResults {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.initOpResults ctx op types index hop hidx) =
    operation.getNumRegions! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem OperationPtr.getRegion!_initOpResults {operation : OperationPtr} :
    operation.getRegion! (Rewriter.initOpResults ctx op types index hop hidx) idx =
    operation.getRegion! ctx idx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_initOpResults {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.initOpResults ctx op types index hop hidx) =
    blockOperandPtr.get! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_initOpResults {block : BlockPtr} :
    block.getNumArguments! (Rewriter.initOpResults ctx op types index hop hidx) =
    block.getNumArguments! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_initOpResults {blockArg : BlockArgumentPtr} {index} {hidx} :
    blockArg.get! (Rewriter.initOpResults ctx op types index hop hidx) =
    blockArg.get! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[simp, grind =]
theorem RegionPtr.get!_initOpResults {region : RegionPtr} :
    region.get! (Rewriter.initOpResults ctx op types index hop hidx) =
    region.get! ctx := by
  fun_induction Rewriter.initOpResults <;> grind

@[grind =]
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

@[grind =]
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

@[grind =]
theorem OpOperandPtrPtr.get!_initOpResults {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.initOpResults ctx op types index hop hidx) =
    match opOperandPtr with
    | .valueFirstUse (.opResult opRes) =>
      if _ : opRes.op = op ∧ opRes.index < types.size ∧ op.getNumResults! ctx ≤ opRes.index then none
      else (opRes.get! ctx).firstUse
    | _ => opOperandPtr.get! ctx := by
  cases opOperandPtr
  · grind
  · simp only [get!_valueFirstUse_eq, ValuePtr.getFirstUse!_initOpResults, dite_eq_ite]; grind

end Rewriter.initOpResults

end Veir
