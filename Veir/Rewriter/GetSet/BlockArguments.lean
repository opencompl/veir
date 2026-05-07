module

public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic

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

/-! ## `Rewriter.pushBlockArgument` -/

section Rewriter.pushBlockArgument

variable {block : BlockPtr}

attribute [local grind] Rewriter.pushBlockArgument

@[simp, grind =]
theorem BlockPtr.firstUse!_Rewriter_pushBlockArgument {block' : BlockPtr} :
    (block'.get! (Rewriter.pushBlockArgument ctx block type hblock)).firstUse =
    (block'.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_Rewriter_pushBlockArgument {block' : BlockPtr} :
    (block'.get! (Rewriter.pushBlockArgument ctx block type hblock)).prev =
    (block'.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_Rewriter_pushBlockArgument {block' : BlockPtr} :
    (block'.get! (Rewriter.pushBlockArgument ctx block type hblock)).next =
    (block'.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_Rewriter_pushBlockArgument {block' : BlockPtr} :
    (block'.get! (Rewriter.pushBlockArgument ctx block type hblock)).parent =
    (block'.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_Rewriter_pushBlockArgument {block' : BlockPtr} :
    (block'.get! (Rewriter.pushBlockArgument ctx block type hblock)).firstOp =
    (block'.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_Rewriter_pushBlockArgument {block' : BlockPtr} :
    (block'.get! (Rewriter.pushBlockArgument ctx block type hblock)).lastOp =
    (block'.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.get!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.get! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getOpType! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getProperties! (Rewriter.pushBlockArgument ctx block type hblock) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_Rewriter_pushBlockArgument {opResult : OpResultPtr} :
    opResult.get! (Rewriter.pushBlockArgument ctx block type hblock) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_Rewriter_pushBlockArgument {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.pushBlockArgument ctx block type hblock) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getOperands! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_Rewriter_pushBlockArgument {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.pushBlockArgument ctx block type hblock) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.pushBlockArgument ctx block type hblock) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.pushBlockArgument ctx block type hblock) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_Rewriter_pushBlockArgument {operation : OperationPtr} :
    operation.getRegion! (Rewriter.pushBlockArgument ctx block type hblock) idx =
    operation.getRegion! ctx idx := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_Rewriter_pushBlockArgument {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.pushBlockArgument ctx block type hblock) =
    blockOperandPtr.get! ctx := by
  grind

@[grind =]
theorem BlockPtr.getNumArguments!_Rewriter_pushBlockArgument {block' : BlockPtr} :
    block'.getNumArguments! (Rewriter.pushBlockArgument ctx block type hblock) =
    if block = block' then
      block'.getNumArguments! ctx + 1
    else
      block'.getNumArguments! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.get!_Rewriter_pushBlockArgument {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.pushBlockArgument ctx block type hblock) =
    if blockArg = block.nextArgument ctx then
      { type := type, firstUse := none, index := block.getNumArguments! ctx, owner := block, loc := ()}
    else
      blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_Rewriter_pushBlockArgument {region : RegionPtr} :
    region.get! (Rewriter.pushBlockArgument ctx block type hblock) =
    region.get! ctx := by
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_Rewriter_pushBlockArgument {value : ValuePtr} :
    value.getFirstUse! (Rewriter.pushBlockArgument ctx block type hblock) =
    if value = block.nextArgument ctx then
      none
    else
      value.getFirstUse! ctx := by
  grind

@[grind =]
theorem ValuePtr.getType!_Rewriter_pushBlockArgument {value : ValuePtr} :
    value.getType! (Rewriter.pushBlockArgument ctx block type hblock) =
    if value = block.nextArgument ctx then
      type
    else
      value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_Rewriter_pushBlockArgument {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.pushBlockArgument ctx block type hblock) =
    if opOperandPtr = OpOperandPtrPtr.valueFirstUse (block.nextArgument ctx) then
      none
    else
      opOperandPtr.get! ctx := by
  grind

end Rewriter.pushBlockArgument

/-! ## `Rewriter.initBlockArguments` -/

section Rewriter.initBlockArguments

variable {op : OperationPtr}

attribute [local grind] Rewriter.initBlockArguments

@[simp, grind =]
theorem BlockPtr.firstUse!_initBlockArguments {block' : BlockPtr} :
    (block'.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂)).firstUse =
    (block'.get! ctx).firstUse := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =]
theorem BlockPtr.prev!_initBlockArguments {block' : BlockPtr} :
    (block'.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂)).prev =
    (block'.get! ctx).prev := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =]
theorem BlockPtr.next!_initBlockArguments {block' : BlockPtr} :
    (block'.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂)).next =
    (block'.get! ctx).next := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =]
theorem BlockPtr.parent!_initBlockArguments {block' : BlockPtr} :
    (block'.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂)).parent =
    (block'.get! ctx).parent := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =]
theorem BlockPtr.firstOp!_initBlockArguments {block' : BlockPtr} :
    (block'.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂)).firstOp =
    (block'.get! ctx).firstOp := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =]
theorem BlockPtr.lastOp!_initBlockArguments {block' : BlockPtr} :
    (block'.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂)).lastOp =
    (block'.get! ctx).lastOp := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =]
theorem OperationPtr.get!_initBlockArguments {operation : OperationPtr} :
    operation.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    operation.get! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =]
theorem OperationPtr.getOpType!_initBlockArguments {operation : OperationPtr} :
    operation.getOpType! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    operation.getOpType! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =]
theorem OperationPtr.getProperties!_initBlockArguments {operation : OperationPtr} :
    operation.getProperties! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) opCode =
    operation.getProperties! ctx opCode := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_initBlockArguments {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    operation.getNumResults! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =]
theorem OpResultPtr.get!_initBlockArguments {opResult : OpResultPtr} :
    opResult.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    opResult.get! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind [cases OpResultPtr]

@[simp, grind =]
theorem OperationPtr.getNumOperands!_initBlockArguments {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    operation.getNumOperands! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =]
theorem OpOperandPtr.get!_initBlockArguments {opOperand : OpOperandPtr}:
    opOperand.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) = opOperand.get! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =]
theorem OperationPtr.getOperands!_initBlockArguments {operation : OperationPtr} :
    operation.getOperands! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) = operation.getOperands! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_initBlockArguments {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    operation.getNumSuccessors! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =]
theorem BlockOperandPtr.get!_initBlockArguments {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    blockOperand.get! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_initBlockArguments {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) i =
    operation.getSuccessor! ctx i := by
  fun_induction Rewriter.initBlockArguments <;> grind [OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_initBlockArguments {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_initBlockArguments,
    OperationPtr.getNumSuccessors!_initBlockArguments]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_initBlockArguments {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    operation.getNumRegions! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =]
theorem OperationPtr.getRegion!_initBlockArguments {operation : OperationPtr} :
    operation.getRegion! (Rewriter.initBlockArguments ctx block types index h₁ h₂) idx =
    operation.getRegion! ctx idx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_initBlockArguments {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    blockOperandPtr.get! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[grind =]
theorem BlockPtr.getNumArguments!_initBlockArguments {block' : BlockPtr} :
    block'.getNumArguments! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    if block = block' then
      block'.getNumArguments! ctx + (types.size - idx)
    else
      block'.getNumArguments! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[grind =]
theorem BlockArgumentPtr.get!_initBlockArguments {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.initBlockArguments ctx bl types idx h₁ h₂) =
    if h : blockArg.block = bl ∧ blockArg.index < types.size ∧ bl.getNumArguments! ctx ≤ blockArg.index then
      { type := types[blockArg.index], firstUse := none, index := blockArg.index, owner := bl, loc := ()}
    else blockArg.get! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind [BlockPtr.getArgument_def, cases BlockArgumentPtr]

@[simp, grind =]
theorem RegionPtr.get!_initBlockArguments {region : RegionPtr} :
    region.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    region.get! ctx := by
  fun_induction Rewriter.initBlockArguments <;> grind

@[grind =]
theorem ValuePtr.getFirstUse!_initBlockArguments {value : ValuePtr} :
    value.getFirstUse! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    match value with
    | .blockArgument blockArg =>
      if blockArg.block = block ∧ blockArg.index < types.size ∧ block.getNumArguments! ctx ≤ blockArg.index then
        none
      else value.getFirstUse! ctx
    | _ => value.getFirstUse! ctx := by
  fun_induction Rewriter.initBlockArguments <;>
    grind [cases BlockArgumentPtr, cases ValuePtr, BlockPtr.getArgument_def]

@[grind =]
theorem ValuePtr.getType!_initBlockArguments {value : ValuePtr} :
    value.getType! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    match value with
    | .blockArgument blockArg =>
      if _ : blockArg.block = block ∧ blockArg.index < types.size ∧ block.getNumArguments! ctx ≤ blockArg.index then
        types[blockArg.index]
      else value.getType! ctx
    | _ => value.getType! ctx := by
  fun_induction Rewriter.initBlockArguments <;>
    grind [cases BlockArgumentPtr, cases ValuePtr, BlockPtr.getArgument_def]

@[grind =]
theorem OpOperandPtrPtr.get!_initBlockArguments {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.initBlockArguments ctx block types idx h₁ h₂) =
    match opOperandPtr with
    | .valueFirstUse (.blockArgument blockArg) =>
      if _ : blockArg.block = block ∧ blockArg.index < types.size ∧ block.getNumArguments! ctx ≤ blockArg.index then
        none
      else (blockArg.get! ctx).firstUse
    | _ => opOperandPtr.get! ctx := by
  cases opOperandPtr
  · grind
  · simp only [get!_valueFirstUse_eq, ValuePtr.getFirstUse!_initBlockArguments, dite_eq_ite]; grind

end Rewriter.initBlockArguments

end Veir
