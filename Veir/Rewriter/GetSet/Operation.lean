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
/-! ## `Rewriter.setAttributes` -/

section Rewriter.setAttributes

variable {op : OperationPtr} {newAttrs : DictionaryAttr} {opIn : op.InBounds ctx}

attribute [local grind] Rewriter.setAttributes

@[simp, grind =, simp_getset]
theorem BlockPtr.get!_setAttributes {block : BlockPtr} :
    block.get! (Rewriter.setAttributes ctx op newAttrs opIn) =
    block.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_setAttributes {block : BlockPtr} :
    block.getParent! (Rewriter.setAttributes ctx op newAttrs opIn) =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_setAttributes {block : BlockPtr} :
    block.getFirstUse! (Rewriter.setAttributes ctx op newAttrs opIn) =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_setAttributes {block : BlockPtr} :
    block.getFirstOp! (Rewriter.setAttributes ctx op newAttrs opIn) =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_setAttributes {block : BlockPtr} :
    block.getLastOp! (Rewriter.setAttributes ctx op newAttrs opIn) =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_setAttributes {block : BlockPtr} :
    block.getNextBlock! (Rewriter.setAttributes ctx op newAttrs opIn) =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_setAttributes {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.setAttributes ctx op newAttrs opIn) =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.firstUse!_setAttributes {block : BlockPtr} :
    (block.get! (Rewriter.setAttributes ctx op newAttrs opIn)).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.prev!_setAttributes {block : BlockPtr} :
    (block.get! (Rewriter.setAttributes ctx op newAttrs opIn)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.next!_setAttributes {block : BlockPtr} :
    (block.get! (Rewriter.setAttributes ctx op newAttrs opIn)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.parent!_setAttributes {block : BlockPtr} :
    (block.get! (Rewriter.setAttributes ctx op newAttrs opIn)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.firstOp!_setAttributes {block : BlockPtr} :
    (block.get! (Rewriter.setAttributes ctx op newAttrs opIn)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.lastOp!_setAttributes {block : BlockPtr} :
    (block.get! (Rewriter.setAttributes ctx op newAttrs opIn)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.get!_setAttributes {op' : OperationPtr} :
    op'.get! (Rewriter.setAttributes ctx op newAttrs opIn) =
    if op' = op then
      { op'.get! ctx with attrs := newAttrs }
    else
      op'.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_setAttributes {op' : OperationPtr} :
    op'.getNextOp! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_setAttributes {op' : OperationPtr} :
    op'.getPrevOp! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_setAttributes {op' : OperationPtr} :
    op'.getParent! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[grind =, simp_getset]
theorem OperationPtr.getAttributes!_setAttributes {op' : OperationPtr} :
    op'.getAttributes! (Rewriter.setAttributes ctx op newAttrs opIn) =
    if op' = op then newAttrs else op'.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.prev!_setAttributes {op' : OperationPtr} :
    (op'.get! (Rewriter.setAttributes ctx op newAttrs opIn)).prev =
    (op'.get! ctx).prev := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.next!_setAttributes {op' : OperationPtr} :
    (op'.get! (Rewriter.setAttributes ctx op newAttrs opIn)).next =
    (op'.get! ctx).next := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.parent!_setAttributes {op' : OperationPtr} :
    (op'.get! (Rewriter.setAttributes ctx op newAttrs opIn)).parent =
    (op'.get! ctx).parent := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_setAttributes {op' : OperationPtr} :
    op'.getOpType! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getOpType! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.attrs!_setAttributes {op' : OperationPtr} :
    (op'.get! (Rewriter.setAttributes ctx op newAttrs opIn)).attrs =
    if op' = op then newAttrs else (op'.get! ctx).attrs  := by
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
theorem OpResultPtr.get!_setAttributes {opResult : OpResultPtr} :
    opResult.get! (Rewriter.setAttributes ctx op newAttrs opIn) =
    opResult.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_setAttributes {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.setAttributes ctx op newAttrs opIn) =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_setAttributes {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.setAttributes ctx op newAttrs opIn) =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_setAttributes {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.setAttributes ctx op newAttrs opIn) =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_setAttributes {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.setAttributes ctx op newAttrs opIn) =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_setAttributes {op' : OperationPtr} :
    op'.getNumOperands! (Rewriter.setAttributes ctx op newAttrs opIn) =
    op'.getNumOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.get!_setAttributes {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.setAttributes ctx op newAttrs opIn) =
    opOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_setAttributes {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.setAttributes ctx op newAttrs opIn) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_setAttributes {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.setAttributes ctx op newAttrs opIn) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_setAttributes {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.setAttributes ctx op newAttrs opIn) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_setAttributes {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.setAttributes ctx op newAttrs opIn) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockOperandPtr.get!_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.setAttributes ctx op newAttrs opIn) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (Rewriter.setAttributes ctx op newAttrs opIn) =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (Rewriter.setAttributes ctx op newAttrs opIn) =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (Rewriter.setAttributes ctx op newAttrs opIn) =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (Rewriter.setAttributes ctx op newAttrs opIn) =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_setAttributes {op' : OperationPtr} :
    op'.getSuccessor! (Rewriter.setAttributes ctx op newAttrs opIn) index =
    op'.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

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
theorem BlockArgumentPtr.get!_setAttributes {blockArgument : BlockArgumentPtr} :
    blockArgument.get!  (Rewriter.setAttributes ctx op newAttrs opIn) =
    blockArgument.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_setAttributes {blockArgument : BlockArgumentPtr} :
    blockArgument.getType!  (Rewriter.setAttributes ctx op newAttrs opIn) =
    blockArgument.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_setAttributes {blockArgument : BlockArgumentPtr} :
    blockArgument.getFirstUse!  (Rewriter.setAttributes ctx op newAttrs opIn) =
    blockArgument.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_setAttributes {blockArgument : BlockArgumentPtr} :
    blockArgument.getIndex!  (Rewriter.setAttributes ctx op newAttrs opIn) =
    blockArgument.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getLoc!_setAttributes {blockArgument : BlockArgumentPtr} :
    blockArgument.getLoc!  (Rewriter.setAttributes ctx op newAttrs opIn) =
    blockArgument.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_setAttributes {blockArgument : BlockArgumentPtr} :
    blockArgument.getOwner!  (Rewriter.setAttributes ctx op newAttrs opIn) =
    blockArgument.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.get!_setAttributes {region : RegionPtr} :
    region.get! (Rewriter.setAttributes ctx op newAttrs opIn) =
    region.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_setAttributes {region : RegionPtr} :
    region.getParent! (Rewriter.setAttributes ctx op newAttrs opIn) =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_setAttributes {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.setAttributes ctx op newAttrs opIn) =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_setAttributes {region : RegionPtr} :
    region.getLastBlock! (Rewriter.setAttributes ctx op newAttrs opIn) =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.firstBlock!_setAttributes {region : RegionPtr} :
    (region.get! (Rewriter.setAttributes ctx op newAttrs opIn)).firstBlock =
    (region.get! ctx).firstBlock := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.lastBlock!_setAttributes {region : RegionPtr} :
    (region.get! (Rewriter.setAttributes ctx op newAttrs opIn)).lastBlock =
    (region.get! ctx).lastBlock := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.parent!_setAttributes {region : RegionPtr} :
    (region.get! (Rewriter.setAttributes ctx op newAttrs opIn)).parent =
    (region.get! ctx).parent := by
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
theorem BlockPtr.get!_setProperties {block : BlockPtr} :
    block.get! (Rewriter.setProperties ctx op opCode newProps opIn hprop) =
    block.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_setProperties {block : BlockPtr} :
    block.getParent! (Rewriter.setProperties ctx op opCode newProps opIn hprop) =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_setProperties {block : BlockPtr} :
    block.getFirstUse! (Rewriter.setProperties ctx op opCode newProps opIn hprop) =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_setProperties {block : BlockPtr} :
    block.getFirstOp! (Rewriter.setProperties ctx op opCode newProps opIn hprop) =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_setProperties {block : BlockPtr} :
    block.getLastOp! (Rewriter.setProperties ctx op opCode newProps opIn hprop) =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_setProperties {block : BlockPtr} :
    block.getNextBlock! (Rewriter.setProperties ctx op opCode newProps opIn hprop) =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_setProperties {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.setProperties ctx op opCode newProps opIn hprop) =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.firstUse!_setProperties {block : BlockPtr} :
    (block.get! (Rewriter.setProperties ctx op opCode newProps opIn hprop)).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.prev!_setProperties {block : BlockPtr} :
    (block.get! (Rewriter.setProperties ctx op opCode newProps opIn hprop)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.next!_setProperties {block : BlockPtr} :
    (block.get! (Rewriter.setProperties ctx op opCode newProps opIn hprop)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.parent!_setProperties {block : BlockPtr} :
    (block.get! (Rewriter.setProperties ctx op opCode newProps opIn hprop)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.firstOp!_setProperties {block : BlockPtr} :
    (block.get! (Rewriter.setProperties ctx op opCode newProps opIn hprop)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.lastOp!_setProperties {block : BlockPtr} :
    (block.get! (Rewriter.setProperties ctx op opCode newProps opIn hprop)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.get!_setProperties {operation : OperationPtr} :
    operation.get! (Rewriter.setProperties ctx op opCode newProps opIn hprop) =
    if operation = op then
      { operation.get! ctx with
        opType := op.getOpType! ctx
        properties := hprop ▸ HasDialect.ofDialectProperties OpInfo opCode newProps }
    else
      operation.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_setProperties {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.setProperties ctx op opCode newProps opIn hprop) =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_setProperties {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.setProperties ctx op opCode newProps opIn hprop) =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_setProperties {operation : OperationPtr} :
    operation.getParent! (Rewriter.setProperties ctx op opCode newProps opIn hprop) =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_setProperties {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.setProperties ctx op opCode newProps opIn hprop) =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.prev!_setProperties {op' : OperationPtr} :
    (op'.get! (Rewriter.setProperties ctx op opCode newProps opIn)).prev =
    (op'.get! ctx).prev := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.next!_setProperties {op' : OperationPtr} :
    (op'.get! (Rewriter.setProperties ctx op opCode newProps opIn)).next =
    (op'.get! ctx).next := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.parent!_setProperties {op' : OperationPtr} :
    (op'.get! (Rewriter.setProperties ctx op opCode newProps opIn)).parent =
    (op'.get! ctx).parent := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_setProperties {op' : OperationPtr} :
    op'.getOpType! (Rewriter.setProperties ctx op opCode newProps opIn) =
    op'.getOpType! ctx := by
  grind

@[simp ,grind =, simp_getset]
theorem OperationPtr.attrs!_setProperties {op' : OperationPtr} :
    (op'.get! (Rewriter.setProperties ctx op opCode newProps opIn)).attrs =
    (op'.get! ctx).attrs := by
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
theorem OpResultPtr.get!_setProperties {opResult : OpResultPtr} :
    opResult.get! (Rewriter.setProperties ctx op opCode newProps opIn) =
    opResult.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_setProperties {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.setProperties ctx op opCode newProps opIn) =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_setProperties {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.setProperties ctx op opCode newProps opIn) =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_setProperties {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.setProperties ctx op opCode newProps opIn) =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_setProperties {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.setProperties ctx op opCode newProps opIn) =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_setProperties {op' : OperationPtr} :
    op'.getNumOperands! (Rewriter.setProperties ctx op opCode newProps opIn) =
    op'.getNumOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.get!_setProperties {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.setProperties ctx op opCode newProps opIn) =
    opOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_setProperties {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.setProperties ctx op opCode newProps opIn) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_setProperties {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.setProperties ctx op opCode newProps opIn) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_setProperties {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.setProperties ctx op opCode newProps opIn) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_setProperties {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.setProperties ctx op opCode newProps opIn) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockOperandPtr.get!_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.setProperties ctx op opCode newProps opIn) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (Rewriter.setProperties ctx op opCode newProps opIn) =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (Rewriter.setProperties ctx op opCode newProps opIn) =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (Rewriter.setProperties ctx op opCode newProps opIn) =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (Rewriter.setProperties ctx op opCode newProps opIn) =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_setProperties {op' : OperationPtr} :
    op'.getSuccessor! (Rewriter.setProperties ctx op opCode newProps opIn) index =
    op'.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

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
theorem BlockArgumentPtr.get!_setProperties {blockArgument : BlockArgumentPtr} :
    blockArgument.get!  (Rewriter.setProperties ctx op opCode newProps opIn) =
    blockArgument.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_setProperties {blockArgument : BlockArgumentPtr} :
    blockArgument.getType!  (Rewriter.setProperties ctx op opCode newProps opIn) =
    blockArgument.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_setProperties {blockArgument : BlockArgumentPtr} :
    blockArgument.getFirstUse!  (Rewriter.setProperties ctx op opCode newProps opIn) =
    blockArgument.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_setProperties {blockArgument : BlockArgumentPtr} :
    blockArgument.getIndex!  (Rewriter.setProperties ctx op opCode newProps opIn) =
    blockArgument.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getLoc!_setProperties {blockArgument : BlockArgumentPtr} :
    blockArgument.getLoc!  (Rewriter.setProperties ctx op opCode newProps opIn) =
    blockArgument.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_setProperties {blockArgument : BlockArgumentPtr} :
    blockArgument.getOwner!  (Rewriter.setProperties ctx op opCode newProps opIn) =
    blockArgument.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.get!_setProperties {region : RegionPtr} :
    region.get! (Rewriter.setProperties ctx op opCode newProps opIn) =
    region.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_setProperties {region : RegionPtr} :
    region.getParent! (Rewriter.setProperties ctx op opCode newProps opIn) =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_setProperties {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.setProperties ctx op opCode newProps opIn) =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_setProperties {region : RegionPtr} :
    region.getLastBlock! (Rewriter.setProperties ctx op opCode newProps opIn) =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.firstBlock!_setProperties {region : RegionPtr} :
    (region.get! (Rewriter.setProperties ctx op opCode newProps opIn)).firstBlock =
    (region.get! ctx).firstBlock := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.lastBlock!_setProperties {region : RegionPtr} :
    (region.get! (Rewriter.setProperties ctx op opCode newProps opIn)).lastBlock =
    (region.get! ctx).lastBlock := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.parent!_setProperties {region : RegionPtr} :
    (region.get! (Rewriter.setProperties ctx op opCode newProps opIn)).parent =
    (region.get! ctx).parent := by
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
