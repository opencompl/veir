module

public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic

public section

/-
The getters we consider are:
* BlockPtr.get! optionally replaced by the following special cases:
  * Block.firstUse
  * Block.prev
  * Block.next
  * Block.parent
  * Block.firstOp
  * Block.lastOp
* OperationPtr.get! optionally replaced by the following special cases:
  * Operation.prev
  * Operation.next
  * Operation.parent
  * OperationPtr.getOpType!
  * Operation.attrs
* OperationPtr.getProperties!
* OperationPtr.getNumResults!
* OpResultPtr.get!
* OperationPtr.getNumOperands!
* OpOperandPtr.get! optionally replaced by the following special case:
* OperationPtr.getOperands!
* OperationPtr.getNumSuccessors!
* BlockOperandPtr.get!
* OperationPtr.getSuccessor!
* OperationPtr.getSuccessors!
* OperationPtr.getNumRegions!
* OperationPtr.getRegion!
* BlockOperandPtrPtr.get!
* BlockPtr.getNumArguments!
* BlockArgumentPtr.get!
* RegionPtr.get! with optionally special cases for:
  * firstBlock
  * lastBlock
  * parent
* ValuePtr.getFirstUse!
* ValuePtr.getType!
* OpOperandPtrPtr.get!
-/

namespace Veir

variable {OpInfo} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}
/-! ## `Rewriter.setType` -/

section Rewriter.setType

variable {value : ValuePtr}

attribute [local grind] Rewriter.setType

@[grind =]
theorem BlockPtr.get!_setType {block : BlockPtr} :
    block.get! (Rewriter.setType ctx value newType valueIn) =
    match value with
    | ValuePtr.opResult _ => block.get! ctx
    | ValuePtr.blockArgument ba =>
      if ba.block = block then
        { block.get! ctx with arguments :=
          (block.get! ctx).arguments.set! ba.index { ba.get! ctx with type := newType } }
      else
        block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_setType {block : BlockPtr} :
    (block.get! (Rewriter.setType ctx value newType valueIn)).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_setType {block : BlockPtr} :
    (block.get! (Rewriter.setType ctx value newType valueIn)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_setType {block : BlockPtr} :
    (block.get! (Rewriter.setType ctx value newType valueIn)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_setType {block : BlockPtr} :
    (block.get! (Rewriter.setType ctx value newType valueIn)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_setType {block : BlockPtr} :
    (block.get! (Rewriter.setType ctx value newType valueIn)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_setType {block : BlockPtr} :
    (block.get! (Rewriter.setType ctx value newType valueIn)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[grind =]
theorem OperationPtr.get!_setType {operation : OperationPtr} :
    operation.get! (Rewriter.setType ctx value newType valueIn) =
    match value with
    | ValuePtr.opResult or =>
      if or.op = operation then
        { operation.get! ctx with results :=
          (operation.get! ctx).results.set! or.index { or.get! ctx with type := newType } }
      else
        operation.get! ctx
    | ValuePtr.blockArgument _ => operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_setType {operation : OperationPtr} :
    (operation.get! (Rewriter.setType ctx value newType valueIn)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_setType {operation : OperationPtr} :
    (operation.get! (Rewriter.setType ctx value newType valueIn)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_setType {operation : OperationPtr} :
    (operation.get! (Rewriter.setType ctx value newType valueIn)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_setType {operation : OperationPtr} :
    operation.getOpType! (Rewriter.setType ctx value newType valueIn) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_setType {operation : OperationPtr} :
    (operation.get! (Rewriter.setType ctx value newType valueIn)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_setType {operation : OperationPtr} :
    operation.getProperties! (Rewriter.setType ctx value newType valueIn) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_setType {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.setType ctx value newType valueIn) =
    operation.getNumResults! ctx := by
  grind

@[grind =]
theorem OpResultPtr.get!_setType {opResult : OpResultPtr} :
    opResult.get! (Rewriter.setType ctx value newType valueIn) =
    if value = ValuePtr.opResult opResult then
      { opResult.get! ctx with type := newType }
    else
      opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_setType {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.setType ctx value newType valueIn) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_setType {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.setType ctx value newType valueIn) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_setType {operation : OperationPtr} :
    operation.getOperands! (Rewriter.setType ctx value newType valueIn) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_setType {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.setType ctx value newType valueIn) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_setType {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.setType ctx value newType valueIn) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_setType {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.setType ctx value newType valueIn) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_setType {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.setType ctx value newType valueIn) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_setType {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.setType ctx value newType valueIn) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_setType {operation : OperationPtr} :
    operation.getRegion! (Rewriter.setType ctx value newType valueIn) idx =
    operation.getRegion! ctx idx := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_setType {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.setType ctx value newType valueIn) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_setType {block : BlockPtr} :
    block.getNumArguments! (Rewriter.setType ctx value newType valueIn) =
    block.getNumArguments! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.get!_setType {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.setType ctx value newType valueIn) =
    if value = ValuePtr.blockArgument blockArg then
      { blockArg.get! ctx with type := newType }
    else
      blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_setType {region : RegionPtr} :
    region.get! (Rewriter.setType ctx value newType valueIn) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_setType {value' : ValuePtr} :
    value'.getFirstUse! (Rewriter.setType ctx value newType valueIn) =
    value'.getFirstUse! ctx := by
  grind

@[grind =]
theorem ValuePtr.getType!_setType {value' : ValuePtr} :
    value'.getType! (Rewriter.setType ctx value newType valueIn) =
    if value = value' then newType else value'.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_setType {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.setType ctx value newType valueIn) =
    opOperandPtr.get! ctx := by
  grind

end Rewriter.setType

end Veir
