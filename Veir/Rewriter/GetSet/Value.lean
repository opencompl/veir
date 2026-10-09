module

public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic
import all Veir.IR.Basic
import all Veir.IR.GetSet
import all Veir.Rewriter.LinkedList.GetSet
import Veir.Rewriter.WfRewriter.GetSetTactic

public section

namespace Veir

variable {OpInfo} [HasOpInfo OpInfo]

-- Relate the getters to the fields of the underlying structures.
attribute [local grind _=_]
  OperationPtr.getNextOp!_def OperationPtr.getPrevOp!_def OperationPtr.getParent!_def
  OperationPtr.getAttributes!_def OpOperandPtr.getNextUse!_def OpOperandPtr.getBack!_def
  OpOperandPtr.getOwner!_def OpOperandPtr.getValue!_def BlockOperandPtr.getNextUse!_def
  BlockOperandPtr.getBack!_def BlockOperandPtr.getOwner!_def BlockOperandPtr.getValue!_def
  OpResultPtr.getType!_def OpResultPtr.getFirstUse!_def OpResultPtr.getOwner!_def
  BlockPtr.getParent!_def BlockPtr.getFirstUse!_def BlockPtr.getFirstOp!_def
  BlockPtr.getLastOp!_def BlockPtr.getNextBlock!_def BlockPtr.getPrevBlock!_def
  BlockArgumentPtr.getType!_def BlockArgumentPtr.getFirstUse!_def
  BlockArgumentPtr.getIndex!_def BlockArgumentPtr.getLoc!_def
  BlockArgumentPtr.getOwner!_def RegionPtr.getParent!_def RegionPtr.getFirstBlock!_def
  RegionPtr.getLastBlock!_def OpResultPtr.getIndex!_def
variable {ctx : IRContext OpInfo}
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
variable {opCode : Dialect}
/-! ## `Rewriter.setType` -/

section Rewriter.setType

variable {value : ValuePtr}

attribute [local grind] Rewriter.setType

@[grind =, simp_getset]
private theorem BlockPtr.get!_setType {block : BlockPtr} :
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

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_setType {block : BlockPtr} :
    block.getParent! (Rewriter.setType ctx value newType valueIn) =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_setType {block : BlockPtr} :
    block.getFirstUse! (Rewriter.setType ctx value newType valueIn) =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_setType {block : BlockPtr} :
    block.getFirstOp! (Rewriter.setType ctx value newType valueIn) =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_setType {block : BlockPtr} :
    block.getLastOp! (Rewriter.setType ctx value newType valueIn) =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_setType {block : BlockPtr} :
    block.getNextBlock! (Rewriter.setType ctx value newType valueIn) =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_setType {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.setType ctx value newType valueIn) =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.firstUse!_setType {block : BlockPtr} :
    block.getFirstUse! (Rewriter.setType ctx value newType valueIn) =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.prev!_setType {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.setType ctx value newType valueIn) =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.next!_setType {block : BlockPtr} :
    block.getNextBlock! (Rewriter.setType ctx value newType valueIn) =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.parent!_setType {block : BlockPtr} :
    block.getParent! (Rewriter.setType ctx value newType valueIn) =
    block.getParent! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.firstOp!_setType {block : BlockPtr} :
    block.getFirstOp! (Rewriter.setType ctx value newType valueIn) =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.lastOp!_setType {block : BlockPtr} :
    block.getLastOp! (Rewriter.setType ctx value newType valueIn) =
    block.getLastOp! ctx := by
  grind

@[grind =, simp_getset]
private theorem OperationPtr.get!_setType {operation : OperationPtr} :
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

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_setType {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.setType ctx value newType valueIn) =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_setType {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.setType ctx value newType valueIn) =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_setType {operation : OperationPtr} :
    operation.getParent! (Rewriter.setType ctx value newType valueIn) =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_setType {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.setType ctx value newType valueIn) =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.prev!_setType {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.setType ctx value newType valueIn) =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.next!_setType {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.setType ctx value newType valueIn) =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.parent!_setType {operation : OperationPtr} :
    operation.getParent! (Rewriter.setType ctx value newType valueIn) =
    operation.getParent! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_setType {operation : OperationPtr} :
    operation.getOpType! (Rewriter.setType ctx value newType valueIn) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.attrs!_setType {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.setType ctx value newType valueIn) =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_setType {operation : OperationPtr} :
    operation.getProperties! (Rewriter.setType ctx value newType valueIn) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_setType {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.setType ctx value newType valueIn) =
    operation.getNumResults! ctx := by
  grind

@[grind =, simp_getset]
private theorem OpResultPtr.get!_setType {opResult : OpResultPtr} :
    opResult.get! (Rewriter.setType ctx value newType valueIn) =
    if value = ValuePtr.opResult opResult then
      { opResult.get! ctx with type := newType }
    else
      opResult.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_setType {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.setType ctx value newType valueIn) =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[grind =, simp_getset]
theorem OpResultPtr.getType!_setType {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.setType ctx value newType valueIn) =
    if value = ValuePtr.opResult opResult then newType else opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_setType {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.setType ctx value newType valueIn) =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_setType {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.setType ctx value newType valueIn) =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_setType {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.setType ctx value newType valueIn) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OpOperandPtr.get!_setType {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.setType ctx value newType valueIn) =
    opOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_setType {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.setType ctx value newType valueIn) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_setType {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.setType ctx value newType valueIn) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_setType {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.setType ctx value newType valueIn) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_setType {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.setType ctx value newType valueIn) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_setType {operation : OperationPtr} :
    operation.getOperands! (Rewriter.setType ctx value newType valueIn) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_setType {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.setType ctx value newType valueIn) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getBlockOperands!_setType {operation : OperationPtr} :
    operation.getBlockOperands! (Rewriter.setType ctx value newType valueIn) =
    operation.getBlockOperands! ctx := by
  simp only [OperationPtr.getBlockOperands!_def]
  grind

@[simp, grind =, simp_getset]
private theorem BlockOperandPtr.get!_setType {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.setType ctx value newType valueIn) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (Rewriter.setType ctx value newType valueIn) =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (Rewriter.setType ctx value newType valueIn) =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (Rewriter.setType ctx value newType valueIn) =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (Rewriter.setType ctx value newType valueIn) =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_setType {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.setType ctx value newType valueIn) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_setType {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.setType ctx value newType valueIn) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_setType {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.setType ctx value newType valueIn) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_setType {operation : OperationPtr} :
    operation.getRegion! (Rewriter.setType ctx value newType valueIn) idx =
    operation.getRegion! ctx idx := by
  grind

@[simp, grind =, simp_getset]
private theorem BlockOperandPtrPtr.get!_setType {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.setType ctx value newType valueIn) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_setType {block : BlockPtr} :
    block.getNumArguments! (Rewriter.setType ctx value newType valueIn) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getBlockArguments!_setType {block : BlockPtr} :
    block.getBlockArguments! (Rewriter.setType ctx value newType valueIn) =
    block.getBlockArguments! ctx := by
  simp only [BlockPtr.getBlockArguments!_def]
  grind

@[grind =, simp_getset]
private theorem BlockArgumentPtr.get!_setType {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.setType ctx value newType valueIn) =
    if value = ValuePtr.blockArgument blockArg then
      { blockArg.get! ctx with type := newType }
    else
      blockArg.get! ctx := by
  grind

@[grind =, simp_getset]
theorem BlockArgumentPtr.getType!_setType {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.setType ctx value newType valueIn) =
    if value = ValuePtr.blockArgument blockArg then newType else blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_setType {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.setType ctx value newType valueIn) =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_setType {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.setType ctx value newType valueIn) =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getLoc!_setType {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (Rewriter.setType ctx value newType valueIn) =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_setType {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.setType ctx value newType valueIn) =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
private theorem RegionPtr.get!_setType {region : RegionPtr} :
    region.get! (Rewriter.setType ctx value newType valueIn) =
    region.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_setType {region : RegionPtr} :
    region.getParent! (Rewriter.setType ctx value newType valueIn) =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_setType {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.setType ctx value newType valueIn) =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_setType {region : RegionPtr} :
    region.getLastBlock! (Rewriter.setType ctx value newType valueIn) =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getFirstUse!_setType {value' : ValuePtr} :
    value'.getFirstUse! (Rewriter.setType ctx value newType valueIn) =
    value'.getFirstUse! ctx := by
  grind

@[grind =, simp_getset]
theorem ValuePtr.getType!_setType {value' : ValuePtr} :
    value'.getType! (Rewriter.setType ctx value newType valueIn) =
    if value = value' then newType else value'.getType! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OpOperandPtrPtr.get!_setType {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.setType ctx value newType valueIn) =
    opOperandPtr.get! ctx := by
  grind

end Rewriter.setType

end Veir
