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
/-! ## `Rewriter.setAttributes` -/

section Rewriter.setAttributes

variable {op : OperationPtr} {newAttrs : DictionaryAttr} {opIn : op.InBounds ctx}

attribute [local grind] Rewriter.setAttributes

@[simp, grind =]
theorem BlockPtr.get!_setAttributes {block : BlockPtr} :
    block.get! (Rewriter.setAttributes ctx op newAttrs opIn) =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_setAttributes {block : BlockPtr} :
    (block.get! (Rewriter.setAttributes ctx op newAttrs opIn)).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_setAttributes {block : BlockPtr} :
    (block.get! (Rewriter.setAttributes ctx op newAttrs opIn)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_setAttributes {block : BlockPtr} :
    (block.get! (Rewriter.setAttributes ctx op newAttrs opIn)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_setAttributes {block : BlockPtr} :
    (block.get! (Rewriter.setAttributes ctx op newAttrs opIn)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_setAttributes {block : BlockPtr} :
    (block.get! (Rewriter.setAttributes ctx op newAttrs opIn)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_setAttributes {block : BlockPtr} :
    (block.get! (Rewriter.setAttributes ctx op newAttrs opIn)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[grind =]
theorem OperationPtr.get!_setAttributes {op' : OperationPtr} :
    op'.get! (Rewriter.setAttributes ctx op newAttrs opIn) =
    if op' = op then
      { op'.get! ctx with attrs := newAttrs }
    else
      op'.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_setAttributes {op' : OperationPtr} :
    (op'.get! (Rewriter.setAttributes ctx op newAttrs opIn)).prev =
    (op'.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_setAttributes {op' : OperationPtr} :
    (op'.get! (Rewriter.setAttributes ctx op newAttrs opIn)).next =
    (op'.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_setAttributes {op' : OperationPtr} :
    (op'.get! (Rewriter.setAttributes ctx op newAttrs opIn)).parent =
    (op'.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_setAttributes {op' : OperationPtr} :
    op'.getOpType! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getOpType! ctx := by
  grind

@[grind =]
theorem OperationPtr.attrs!_setAttributes {op' : OperationPtr} :
    (op'.get! (Rewriter.setAttributes ctx op newAttrs opIn)).attrs =
    if op' = op then newAttrs else (op'.get! ctx).attrs  := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_setAttributes {op' : OperationPtr} :
    op'.getProperties! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getProperties! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_setAttributes {op' : OperationPtr} :
    op'.getNumResults! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_setAttributes {opResult : OpResultPtr} :
    opResult.get! (Rewriter.setAttributes ctx op newAttrs opIn) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_setAttributes {op' : OperationPtr} :
    op'.getNumOperands! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_setAttributes {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.setAttributes ctx op newAttrs opIn) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_setAttributes {op' : OperationPtr} :
    op'.getOperands! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_setAttributes {op' : OperationPtr} :
    op'.getNumSuccessors! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.setAttributes ctx op newAttrs opIn) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_setAttributes {op' : OperationPtr} :
    op'.getSuccessor! (Rewriter.setAttributes ctx op newAttrs opIn) index =
    op'.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_setAttributes {op' : OperationPtr} :
    op'.getSuccessors! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_setAttributes {op' : OperationPtr} :
    op'.getNumRegions! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getNumRegions! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =]
theorem OperationPtr.getRegion!_setAttributes {op' : OperationPtr} :
    op'.getRegion! (Rewriter.setAttributes ctx op newAttrs opIn) index =
    op'.getRegion! ctx index := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_setAttributes {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get!  (Rewriter.setAttributes ctx op newAttrs opIn) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_setAttributes {block : BlockPtr} :
    block.getNumArguments! (Rewriter.setAttributes ctx op newAttrs opIn) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_setAttributes {blockArgument : BlockArgumentPtr} :
    blockArgument.get!  (Rewriter.setAttributes ctx op newAttrs opIn) =
    blockArgument.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_setAttributes {region : RegionPtr} :
    region.get! (Rewriter.setAttributes ctx op newAttrs opIn) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.firstBlock!_setAttributes {region : RegionPtr} :
    (region.get! (Rewriter.setAttributes ctx op newAttrs opIn)).firstBlock =
    (region.get! ctx).firstBlock := by
  grind

@[simp, grind =]
theorem RegionPtr.lastBlock!_setAttributes {region : RegionPtr} :
    (region.get! (Rewriter.setAttributes ctx op newAttrs opIn)).lastBlock =
    (region.get! ctx).lastBlock := by
  grind

@[simp, grind =]
theorem RegionPtr.parent!_setAttributes {region : RegionPtr} :
    (region.get! (Rewriter.setAttributes ctx op newAttrs opIn)).parent =
    (region.get! ctx).parent := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_setAttributes {value : ValuePtr} :
    value.getFirstUse! (Rewriter.setAttributes ctx op newAttrs opIn)  =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_setAttributes {value : ValuePtr} :
    value.getType! (Rewriter.setAttributes ctx op newAttrs opIn)  =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_setAttributes {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.setAttributes ctx op newAttrs opIn) =
    opOperandPtr.get! ctx := by
  grind

end Rewriter.setAttributes
/-! ## `Rewriter.setProperties` -/

section Rewriter.setProperties

variable {opCode: OpInfo} {op : OperationPtr} {newProps : HasOpInfo.propertiesOf opCode} {opIn : op.InBounds ctx}
         {opIn: op.InBounds ctx} {hprop : op.getOpType! ctx = opCode}

attribute [local grind] Rewriter.setProperties

@[simp, grind =]
theorem BlockPtr.get!_setProperties {block : BlockPtr} :
    block.get! (Rewriter.setProperties ctx op newProps opIn hprop) =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_setProperties {block : BlockPtr} :
    (block.get! (Rewriter.setProperties ctx op newProps opIn hprop)).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_setProperties {block : BlockPtr} :
    (block.get! (Rewriter.setProperties ctx op newProps opIn hprop)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_setProperties {block : BlockPtr} :
    (block.get! (Rewriter.setProperties ctx op newProps opIn hprop)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_setProperties {block : BlockPtr} :
    (block.get! (Rewriter.setProperties ctx op newProps opIn hprop)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_setProperties {block : BlockPtr} :
    (block.get! (Rewriter.setProperties ctx op newProps opIn hprop)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_setProperties {block : BlockPtr} :
    (block.get! (Rewriter.setProperties ctx op newProps opIn hprop)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[grind =]
theorem OperationPtr.get!_setProperties {operation : OperationPtr} :
    operation.get! (Rewriter.setProperties ctx op newProps opIn hprop) =
    if operation = op then
      { operation.get! ctx with opType := op.getOpType! ctx, properties := hprop ▸ newProps }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_setProperties {op' : OperationPtr} :
    (op'.get! (Rewriter.setProperties ctx op newProps opIn)).prev =
    (op'.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_setProperties {op' : OperationPtr} :
    (op'.get! (Rewriter.setProperties ctx op newProps opIn)).next =
    (op'.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_setProperties {op' : OperationPtr} :
    (op'.get! (Rewriter.setProperties ctx op newProps opIn)).parent =
    (op'.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_setProperties {op' : OperationPtr} :
    op'.getOpType! (Rewriter.setProperties ctx op newProps opIn) =
    op'.getOpType! ctx := by
  grind

@[simp ,grind =]
theorem OperationPtr.attrs!_setProperties {op' : OperationPtr} :
    (op'.get! (Rewriter.setProperties ctx op newProps opIn)).attrs =
    (op'.get! ctx).attrs := by
  grind

@[grind =]
theorem OperationPtr.getProperties!_setProperties {op' : OperationPtr} {opCode' : OpInfo}:
    op'.getProperties! (Rewriter.setProperties ctx op newProps opIn hprop) opCode' =
    if op' = op then
      if h: opCode' = opCode then h ▸ newProps else default
    else
      op'.getProperties! ctx opCode' := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_setProperties {op' : OperationPtr} :
    op'.getNumResults! (Rewriter.setProperties ctx op newProps opIn) =
    op'.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_setProperties {opResult : OpResultPtr} :
    opResult.get! (Rewriter.setProperties ctx op newProps opIn) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_setProperties {op' : OperationPtr} :
    op'.getNumOperands! (Rewriter.setProperties ctx op newProps opIn) =
    op'.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_setProperties {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.setProperties ctx op newProps opIn) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_setProperties {op' : OperationPtr} :
    op'.getOperands! (Rewriter.setProperties ctx op newProps opIn) =
    op'.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_setProperties {op' : OperationPtr} :
    op'.getNumSuccessors! (Rewriter.setProperties ctx op newProps opIn) =
    op'.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.setProperties ctx op newProps opIn) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_setProperties {op' : OperationPtr} :
    op'.getSuccessor! (Rewriter.setProperties ctx op newProps opIn) index =
    op'.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_setProperties {op' : OperationPtr} :
    op'.getSuccessors! (Rewriter.setProperties ctx op newProps opIn) =
    op'.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_setProperties {op' : OperationPtr} :
    op'.getNumRegions! (Rewriter.setProperties ctx op newProps opIn) =
    op'.getNumRegions! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =]
theorem OperationPtr.getRegion!_setProperties {op' : OperationPtr} :
    op'.getRegion! (Rewriter.setProperties ctx op newProps opIn) index =
    op'.getRegion! ctx index := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_setProperties {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get!  (Rewriter.setProperties ctx op newProps opIn) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_setProperties {block : BlockPtr} :
    block.getNumArguments! (Rewriter.setProperties ctx op newProps opIn) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_setProperties {blockArgument : BlockArgumentPtr} :
    blockArgument.get!  (Rewriter.setProperties ctx op newProps opIn) =
    blockArgument.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_setProperties {region : RegionPtr} :
    region.get! (Rewriter.setProperties ctx op newProps opIn) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.firstBlock!_setProperties {region : RegionPtr} :
    (region.get! (Rewriter.setProperties ctx op newProps opIn)).firstBlock =
    (region.get! ctx).firstBlock := by
  grind

@[simp, grind =]
theorem RegionPtr.lastBlock!_setProperties {region : RegionPtr} :
    (region.get! (Rewriter.setProperties ctx op newProps opIn)).lastBlock =
    (region.get! ctx).lastBlock := by
  grind

@[simp, grind =]
theorem RegionPtr.parent!_setProperties {region : RegionPtr} :
    (region.get! (Rewriter.setProperties ctx op newProps opIn)).parent =
    (region.get! ctx).parent := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_setProperties {value : ValuePtr} :
    value.getFirstUse! (Rewriter.setProperties ctx op newProps opIn)  =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_setProperties {value : ValuePtr} :
    value.getType! (Rewriter.setProperties ctx op newProps opIn)  =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_setProperties {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.setProperties ctx op newProps opIn) =
    opOperandPtr.get! ctx := by
  grind

end Rewriter.setProperties

end Veir
