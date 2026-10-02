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
/-! ## `Rewriter.setAttributes` -/

section Rewriter.setAttributes

variable {op : OperationPtr} {newAttrs : DictionaryAttr} {opIn : op.InBounds ctx}

attribute [local grind] Rewriter.setAttributes

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_setAttributes {block : BlockPtr} :
    block.getFirstUse! (Rewriter.setAttributes ctx op newAttrs opIn) = block.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_setAttributes {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.setAttributes ctx op newAttrs opIn) = block.getPrevBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_setAttributes {block : BlockPtr} :
    block.getNextBlock! (Rewriter.setAttributes ctx op newAttrs opIn) = block.getNextBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_setAttributes {block : BlockPtr} :
    block.getParent! (Rewriter.setAttributes ctx op newAttrs opIn) = block.getParent! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_setAttributes {block : BlockPtr} :
    block.getFirstOp! (Rewriter.setAttributes ctx op newAttrs opIn) = block.getFirstOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_setAttributes {block : BlockPtr} :
    block.getLastOp! (Rewriter.setAttributes ctx op newAttrs opIn) = block.getLastOp! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getRegions!_setAttributes {op' : OperationPtr} :
    op'.getRegions! (Rewriter.setAttributes ctx op newAttrs opIn) = op'.getRegions! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_setAttributes {op' : OperationPtr} :
    op'.getPrevOp! (Rewriter.setAttributes ctx op newAttrs opIn) = op'.getPrevOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_setAttributes {op' : OperationPtr} :
    op'.getNextOp! (Rewriter.setAttributes ctx op newAttrs opIn) = op'.getNextOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_setAttributes {op' : OperationPtr} :
    op'.getParent! (Rewriter.setAttributes ctx op newAttrs opIn) = op'.getParent! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_setAttributes {op' : OperationPtr} :
    op'.getOpType! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getOpType! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getAttributes!_setAttributes {op' : OperationPtr} :
    op'.getAttributes! (Rewriter.setAttributes ctx op newAttrs opIn) = if op' = op then newAttrs else op'.getAttributes! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_setAttributes {op' : OperationPtr} :
    op'.getProperties! (Rewriter.setAttributes ctx op newAttrs opIn) opCode =
    op'.getProperties! ctx opCode := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_setAttributes {op' : OperationPtr} :
    op'.getNumResults! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getNumResults! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_setAttributes {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.setAttributes ctx op newAttrs opIn) = opResult.getOwner! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_setAttributes {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.setAttributes ctx op newAttrs opIn) = opResult.getIndex! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_setAttributes {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.setAttributes ctx op newAttrs opIn) = opResult.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_setAttributes {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.setAttributes ctx op newAttrs opIn) = opResult.getType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_setAttributes {op' : OperationPtr} :
    op'.getNumOperands! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getNumOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_setAttributes {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.setAttributes ctx op newAttrs opIn) = opOperand.getValue! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_setAttributes {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.setAttributes ctx op newAttrs opIn) = opOperand.getOwner! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_setAttributes {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.setAttributes ctx op newAttrs opIn) = opOperand.getBack! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_setAttributes {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.setAttributes ctx op newAttrs opIn) = opOperand.getNextUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_setAttributes {op' : OperationPtr} :
    op'.getOperands! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_setAttributes {op' : OperationPtr} :
    op'.getNumSuccessors! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getNumSuccessors! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (Rewriter.setAttributes ctx op newAttrs opIn) = blockOperand.getValue! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (Rewriter.setAttributes ctx op newAttrs opIn) = blockOperand.getOwner! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (Rewriter.setAttributes ctx op newAttrs opIn) = blockOperand.getBack! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (Rewriter.setAttributes ctx op newAttrs opIn) = blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_setAttributes {op' : OperationPtr} :
    op'.getSuccessor! (Rewriter.setAttributes ctx op newAttrs opIn) index =
    op'.getSuccessor! ctx index := by
  simp only [OperationPtr.getSuccessor!_def, ← BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_setAttributes {op' : OperationPtr} :
    op'.getSuccessors! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_setAttributes {op' : OperationPtr} :
    op'.getNumRegions! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getNumRegions! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_setAttributes {op' : OperationPtr} :
    op'.getRegion! (Rewriter.setAttributes ctx op newAttrs opIn) index =
    op'.getRegion! ctx index := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =, simp_getset]
theorem BlockOperandPtrPtr.get!_setAttributes {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get!  (Rewriter.setAttributes ctx op newAttrs opIn) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_setAttributes {block : BlockPtr} :
    block.getNumArguments! (Rewriter.setAttributes ctx op newAttrs opIn) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_setAttributes {blockArgument : BlockArgumentPtr} :
    blockArgument.getOwner! (Rewriter.setAttributes ctx op newAttrs opIn) = blockArgument.getOwner! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_setAttributes {blockArgument : BlockArgumentPtr} :
    blockArgument.getIndex! (Rewriter.setAttributes ctx op newAttrs opIn) = blockArgument.getIndex! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_setAttributes {blockArgument : BlockArgumentPtr} :
    blockArgument.getFirstUse! (Rewriter.setAttributes ctx op newAttrs opIn) = blockArgument.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_setAttributes {blockArgument : BlockArgumentPtr} :
    blockArgument.getType! (Rewriter.setAttributes ctx op newAttrs opIn) = blockArgument.getType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_setAttributes {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.setAttributes ctx op newAttrs opIn) = region.getFirstBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_setAttributes {region : RegionPtr} :
    region.getLastBlock! (Rewriter.setAttributes ctx op newAttrs opIn) = region.getLastBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_setAttributes {region : RegionPtr} :
    region.getParent! (Rewriter.setAttributes ctx op newAttrs opIn) = region.getParent! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getFirstUse!_setAttributes {value : ValuePtr} :
    value.getFirstUse! (Rewriter.setAttributes ctx op newAttrs opIn)  =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getType!_setAttributes {value : ValuePtr} :
    value.getType! (Rewriter.setAttributes ctx op newAttrs opIn)  =
    value.getType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtrPtr.get!_setAttributes {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.setAttributes ctx op newAttrs opIn) =
    opOperandPtr.get! ctx := by
  grind

end Rewriter.setAttributes
/-! ## `Rewriter.setProperties` -/

section Rewriter.setProperties

variable {op : OperationPtr} {newProps : propertiesOf opCode}
         {opIn : op.InBounds ctx} {hprop : op.getOpType! ctx = opCode}

attribute [local grind] Rewriter.setProperties

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_setProperties {block : BlockPtr} :
    block.getFirstUse! (Rewriter.setProperties ctx op opCode newProps opIn hprop) = block.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_setProperties {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.setProperties ctx op opCode newProps opIn hprop) = block.getPrevBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_setProperties {block : BlockPtr} :
    block.getNextBlock! (Rewriter.setProperties ctx op opCode newProps opIn hprop) = block.getNextBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_setProperties {block : BlockPtr} :
    block.getParent! (Rewriter.setProperties ctx op opCode newProps opIn hprop) = block.getParent! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_setProperties {block : BlockPtr} :
    block.getFirstOp! (Rewriter.setProperties ctx op opCode newProps opIn hprop) = block.getFirstOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_setProperties {block : BlockPtr} :
    block.getLastOp! (Rewriter.setProperties ctx op opCode newProps opIn hprop) = block.getLastOp! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getRegions!_setProperties {operation : OperationPtr} :
    operation.getRegions! (Rewriter.setProperties ctx op opCode newProps opIn hprop) = operation.getRegions! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_setProperties {op' : OperationPtr} :
    op'.getPrevOp! (Rewriter.setProperties ctx op opCode newProps opIn) = op'.getPrevOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_setProperties {op' : OperationPtr} :
    op'.getNextOp! (Rewriter.setProperties ctx op opCode newProps opIn) = op'.getNextOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_setProperties {op' : OperationPtr} :
    op'.getParent! (Rewriter.setProperties ctx op opCode newProps opIn) = op'.getParent! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_setProperties {op' : OperationPtr} :
    op'.getOpType! (Rewriter.setProperties ctx op opCode newProps opIn) =
    op'.getOpType! ctx := by
  grind

@[simp ,grind =, simp_getset]
theorem OperationPtr.getAttributes!_setProperties {op' : OperationPtr} :
    op'.getAttributes! (Rewriter.setProperties ctx op opCode newProps opIn) = op'.getAttributes! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getProperties!_setProperties
    {GetterDialect : Type} [HasOpInfo GetterDialect]
    [HasDialect OpInfo GetterDialect] {getterOpCode : GetterDialect}
    {op' : OperationPtr} :
    op'.getProperties!
      (Rewriter.setProperties ctx op opCode newProps opIn hprop)
      getterOpCode =
    if op' = op then
      if h : ofDialect OpInfo opCode = ofDialect OpInfo getterOpCode then
        HasDialect.toDialectProperties getterOpCode
          (h ▸ HasDialect.ofDialectProperties OpInfo opCode newProps)
      else
        default
    else
      op'.getProperties! ctx getterOpCode := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_setProperties {op' : OperationPtr} :
    op'.getNumResults! (Rewriter.setProperties ctx op opCode newProps opIn) =
    op'.getNumResults! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_setProperties {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.setProperties ctx op opCode newProps opIn) = opResult.getOwner! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_setProperties {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.setProperties ctx op opCode newProps opIn) = opResult.getIndex! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_setProperties {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.setProperties ctx op opCode newProps opIn) = opResult.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_setProperties {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.setProperties ctx op opCode newProps opIn) = opResult.getType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_setProperties {op' : OperationPtr} :
    op'.getNumOperands! (Rewriter.setProperties ctx op opCode newProps opIn) =
    op'.getNumOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_setProperties {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.setProperties ctx op opCode newProps opIn) = opOperand.getValue! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_setProperties {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.setProperties ctx op opCode newProps opIn) = opOperand.getOwner! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_setProperties {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.setProperties ctx op opCode newProps opIn) = opOperand.getBack! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_setProperties {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.setProperties ctx op opCode newProps opIn) = opOperand.getNextUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_setProperties {op' : OperationPtr} :
    op'.getOperands! (Rewriter.setProperties ctx op opCode newProps opIn) =
    op'.getOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_setProperties {op' : OperationPtr} :
    op'.getNumSuccessors! (Rewriter.setProperties ctx op opCode newProps opIn) =
    op'.getNumSuccessors! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (Rewriter.setProperties ctx op opCode newProps opIn) = blockOperand.getValue! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (Rewriter.setProperties ctx op opCode newProps opIn) = blockOperand.getOwner! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (Rewriter.setProperties ctx op opCode newProps opIn) = blockOperand.getBack! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (Rewriter.setProperties ctx op opCode newProps opIn) = blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_setProperties {op' : OperationPtr} :
    op'.getSuccessor! (Rewriter.setProperties ctx op opCode newProps opIn) index =
    op'.getSuccessor! ctx index := by
  simp only [OperationPtr.getSuccessor!_def, ← BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_setProperties {op' : OperationPtr} :
    op'.getSuccessors! (Rewriter.setProperties ctx op opCode newProps opIn) =
    op'.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_setProperties {op' : OperationPtr} :
    op'.getNumRegions! (Rewriter.setProperties ctx op opCode newProps opIn) =
    op'.getNumRegions! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_setProperties {op' : OperationPtr} :
    op'.getRegion! (Rewriter.setProperties ctx op opCode newProps opIn) index =
    op'.getRegion! ctx index := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =, simp_getset]
theorem BlockOperandPtrPtr.get!_setProperties {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get!  (Rewriter.setProperties ctx op opCode newProps opIn) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_setProperties {block : BlockPtr} :
    block.getNumArguments! (Rewriter.setProperties ctx op opCode newProps opIn) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_setProperties {blockArgument : BlockArgumentPtr} :
    blockArgument.getOwner! (Rewriter.setProperties ctx op opCode newProps opIn) = blockArgument.getOwner! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_setProperties {blockArgument : BlockArgumentPtr} :
    blockArgument.getIndex! (Rewriter.setProperties ctx op opCode newProps opIn) = blockArgument.getIndex! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_setProperties {blockArgument : BlockArgumentPtr} :
    blockArgument.getFirstUse! (Rewriter.setProperties ctx op opCode newProps opIn) = blockArgument.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_setProperties {blockArgument : BlockArgumentPtr} :
    blockArgument.getType! (Rewriter.setProperties ctx op opCode newProps opIn) = blockArgument.getType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_setProperties {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.setProperties ctx op opCode newProps opIn) = region.getFirstBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_setProperties {region : RegionPtr} :
    region.getLastBlock! (Rewriter.setProperties ctx op opCode newProps opIn) = region.getLastBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_setProperties {region : RegionPtr} :
    region.getParent! (Rewriter.setProperties ctx op opCode newProps opIn) = region.getParent! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getFirstUse!_setProperties {value : ValuePtr} :
    value.getFirstUse! (Rewriter.setProperties ctx op opCode newProps opIn)  =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getType!_setProperties {value : ValuePtr} :
    value.getType! (Rewriter.setProperties ctx op opCode newProps opIn)  =
    value.getType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtrPtr.get!_setProperties {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.setProperties ctx op opCode newProps opIn) =
    opOperandPtr.get! ctx := by
  grind

end Rewriter.setProperties

end Veir
