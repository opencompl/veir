module

public import Veir.IR.Basic
import Veir.IR.InBounds
import Veir.IR.GetSet

namespace Veir

attribute [local grind _=_] BlockArgumentPtr.getFirstUse!_def BlockArgumentPtr.getFirstUse_def BlockArgumentPtr.getIndex!_def BlockArgumentPtr.getIndex_def BlockArgumentPtr.getLoc!_def BlockArgumentPtr.getLoc_def BlockArgumentPtr.getOwner!_def BlockArgumentPtr.getOwner_def BlockArgumentPtr.getType!_def BlockArgumentPtr.getType_def BlockOperandPtr.getBack!_def BlockOperandPtr.getBack_def BlockOperandPtr.getNextUse!_def BlockOperandPtr.getNextUse_def BlockOperandPtr.getOwner!_def BlockOperandPtr.getOwner_def BlockOperandPtr.getValue!_def BlockOperandPtr.getValue_def BlockPtr.getFirstOp!_def BlockPtr.getFirstOp_def BlockPtr.getFirstUse!_def BlockPtr.getFirstUse_def BlockPtr.getLastOp!_def BlockPtr.getLastOp_def BlockPtr.getNextBlock!_def BlockPtr.getNextBlock_def BlockPtr.getParent!_def BlockPtr.getParent_def BlockPtr.getPrevBlock!_def BlockPtr.getPrevBlock_def OpOperandPtr.getBack!_def OpOperandPtr.getBack_def OpOperandPtr.getNextUse!_def OpOperandPtr.getNextUse_def OpOperandPtr.getOwner!_def OpOperandPtr.getOwner_def OpOperandPtr.getValue!_def OpOperandPtr.getValue_def OpResultPtr.getFirstUse!_def OpResultPtr.getFirstUse_def OpResultPtr.getOwner!_def OpResultPtr.getOwner_def OpResultPtr.getIndex!_def OpResultPtr.getIndex_def OpResultPtr.getType!_def OpResultPtr.getType_def OperationPtr.getAttributes!_def OperationPtr.getAttributes_def OperationPtr.getNextOp!_def OperationPtr.getNextOp_def OperationPtr.getOpType!_def OperationPtr.getParent!_def OperationPtr.getParent_def OperationPtr.getPrevOp!_def OperationPtr.getPrevOp_def OperationPtr.getRegions!_def RegionPtr.getFirstBlock!_def RegionPtr.getFirstBlock_def RegionPtr.getLastBlock!_def RegionPtr.getLastBlock_def RegionPtr.getParent!_def RegionPtr.getParent_def

/-- Like `unfold_field_getters_in_grind`, but lets `grind` rewrite in both directions, so that
projections arising from unfolded definitions also trigger patterns stated with getters. -/
macro "fold_field_getters_in_grind" : command => `(
  attribute [local grind _=_] BlockArgumentPtr.getFirstUse!_def BlockArgumentPtr.getFirstUse_def BlockArgumentPtr.getIndex!_def BlockArgumentPtr.getIndex_def BlockArgumentPtr.getLoc!_def BlockArgumentPtr.getLoc_def BlockArgumentPtr.getOwner!_def BlockArgumentPtr.getOwner_def BlockArgumentPtr.getType!_def BlockArgumentPtr.getType_def BlockOperandPtr.getBack!_def BlockOperandPtr.getBack_def BlockOperandPtr.getNextUse!_def BlockOperandPtr.getNextUse_def BlockOperandPtr.getOwner!_def BlockOperandPtr.getOwner_def BlockOperandPtr.getValue!_def BlockOperandPtr.getValue_def BlockPtr.getFirstOp!_def BlockPtr.getFirstOp_def BlockPtr.getFirstUse!_def BlockPtr.getFirstUse_def BlockPtr.getLastOp!_def BlockPtr.getLastOp_def BlockPtr.getNextBlock!_def BlockPtr.getNextBlock_def BlockPtr.getParent!_def BlockPtr.getParent_def BlockPtr.getPrevBlock!_def BlockPtr.getPrevBlock_def OpOperandPtr.getBack!_def OpOperandPtr.getBack_def OpOperandPtr.getNextUse!_def OpOperandPtr.getNextUse_def OpOperandPtr.getOwner!_def OpOperandPtr.getOwner_def OpOperandPtr.getValue!_def OpOperandPtr.getValue_def OpResultPtr.getFirstUse!_def OpResultPtr.getFirstUse_def OpResultPtr.getOwner!_def OpResultPtr.getOwner_def OpResultPtr.getIndex!_def OpResultPtr.getIndex_def OpResultPtr.getType!_def OpResultPtr.getType_def OperationPtr.getAttributes!_def OperationPtr.getAttributes_def OperationPtr.getNextOp!_def OperationPtr.getNextOp_def OperationPtr.getOpType!_def OperationPtr.getParent!_def OperationPtr.getParent_def OperationPtr.getPrevOp!_def OperationPtr.getPrevOp_def OperationPtr.getRegions!_def RegionPtr.getFirstBlock!_def RegionPtr.getFirstBlock_def RegionPtr.getLastBlock!_def RegionPtr.getLastBlock_def RegionPtr.getParent!_def RegionPtr.getParent_def
)

variable {OpInfo : Type} [IsOpCode OpInfo]
variable {ctx : IRContext OpInfo}

public section

/-
  FieldsInBounds implementation.
  These are the predicates that ensures that all pointers in a program are in bounds.
-/

structure OpResult.FieldsInBounds (res : OpResultPtr) (ctx : IRContext OpInfo) : Prop where
  firstUse_inBounds : (res.getFirstUse! ctx).maybe OpOperandPtr.InBounds ctx
  owner_inBounds : (res.getOwner! ctx).InBounds ctx

structure OpOperand.FieldsInBounds (operand : OpOperandPtr) (ctx : IRContext OpInfo) : Prop where
  nextUse_inBounds : (operand.getNextUse! ctx).maybe OpOperandPtr.InBounds ctx
  back_inBounds : (operand.getBack! ctx).InBounds ctx
  owner_inBounds : (operand.getOwner! ctx).InBounds ctx
  value_inBounds : (operand.getValue! ctx).InBounds ctx

structure BlockOperand.FieldsInBounds (operand : BlockOperandPtr) (ctx : IRContext OpInfo) : Prop where
  nextUse_inBounds : (operand.getNextUse! ctx).maybe BlockOperandPtr.InBounds ctx
  back_inBounds : (operand.getBack! ctx).InBounds ctx
  owner_inBounds : (operand.getOwner! ctx).InBounds ctx
  value_inBounds : (operand.getValue! ctx).InBounds ctx

structure Operation.FieldsInBounds (operation : OperationPtr) (ctx : IRContext OpInfo) (hin : operation.InBounds ctx) : Prop where
  results_inBounds (res : OpResultPtr) (hres : res.InBounds ctx) : res.op = operation → OpResult.FieldsInBounds res ctx
  prev_inBounds : (operation.getPrevOp! ctx).maybe OperationPtr.InBounds ctx
  next_inBounds : (operation.getNextOp! ctx).maybe OperationPtr.InBounds ctx
  parent_inBounds : (operation.getParent! ctx).maybe BlockPtr.InBounds ctx
  blockOperands_inBounds (operand : BlockOperandPtr) (h : operand.InBounds ctx):
    operand.op = operation → BlockOperand.FieldsInBounds operand ctx
  regions_inBounds i (hi : i < operation.getNumRegions! ctx) :
    (operation.getRegion! ctx i).InBounds ctx
  operands_inBounds (operand : OpOperandPtr) (h : operand.InBounds ctx):
    operand.op = operation → OpOperand.FieldsInBounds operand ctx

@[local grind]
structure BlockArgument.FieldsInBounds (arg : BlockArgumentPtr) (ctx : IRContext OpInfo) : Prop where
  firstUse_inBounds : (arg.getFirstUse! ctx).maybe OpOperandPtr.InBounds ctx
  owner_inBounds : (arg.getOwner! ctx).InBounds ctx

@[local grind]
structure Block.FieldsInBounds (block : BlockPtr) (ctx : IRContext OpInfo) (hin : block.InBounds ctx) : Prop where
  firstUse_inBounds : (block.getFirstUse! ctx).maybe BlockOperandPtr.InBounds ctx
  prev_inBounds : (block.getPrevBlock! ctx).maybe BlockPtr.InBounds ctx
  next_inBounds : (block.getNextBlock! ctx).maybe BlockPtr.InBounds ctx
  parent_inBounds : (block.getParent! ctx).maybe RegionPtr.InBounds ctx
  firstOp_inBounds : (block.getFirstOp! ctx).maybe OperationPtr.InBounds ctx
  lastOp_inBounds : (block.getLastOp! ctx).maybe OperationPtr.InBounds ctx
  arguments_inBounds (arg : BlockArgumentPtr) (h : arg.InBounds ctx) :
    arg.block = block → BlockArgument.FieldsInBounds arg ctx

@[local grind]
structure Region.FieldsInBounds (region : RegionPtr) (ctx : IRContext OpInfo) : Prop where
  firstBlock_inBounds block : region.getFirstBlock! ctx = some block → block.InBounds ctx
  lastBlock_inBounds block : region.getLastBlock! ctx = some block → block.InBounds ctx
  parent_inBounds parent : region.getParent! ctx = some parent → parent.InBounds ctx

/--
    Ensures that all pointers referenced by any structure in the context are in bounds.
-/
structure IRContext.FieldsInBounds (ctx : IRContext OpInfo) : Prop where
  operations_inBounds (op : OperationPtr) opIn : Operation.FieldsInBounds op ctx opIn
  blocks_inBounds (block : BlockPtr) blockIn : Block.FieldsInBounds block ctx blockIn
  regions_inBounds (region : RegionPtr) (regionIn : region.InBounds ctx) : Region.FieldsInBounds region ctx

attribute [local grind =] Option.maybe_def

section default

@[grind .]
theorem IRContext.default_FieldsInBounds : IRContext.FieldsInBounds (default : IRContext OpInfo) := by
  simp only [default_def]
  grind [IRContext.FieldsInBounds, OperationPtr.inBounds_def,
    BlockPtr.inBounds_def, RegionPtr.inBounds_def]

end default

section get

/-
  Theorems combining `get` methods with `IRContext.fieldsInBounds`.
  These should be the only theorems that unfolds the `FieldsInBounds
  structures.
-/

variable {ctx : IRContext OpInfo}

attribute [local grind] IRContext.FieldsInBounds
  OpOperand.FieldsInBounds BlockOperand.FieldsInBounds
  Operation.FieldsInBounds Block.FieldsInBounds Region.FieldsInBounds

section OpResultPtr

variable {res : OpResultPtr}
attribute [local grind] OpResult.FieldsInBounds

theorem OpResultPtr.firstUse!_inBounds :
    ctx.FieldsInBounds →
    res.InBounds ctx →
    (res.getFirstUse! ctx).maybe OpOperandPtr.InBounds ctx := by
  grind

grind_pattern OpResultPtr.firstUse!_inBounds => (res.getFirstUse! ctx), ctx.FieldsInBounds

theorem OpResultPtr.owner!_inBounds :
    ctx.FieldsInBounds →
    res.InBounds ctx →
    (res.getOwner! ctx).InBounds ctx := by
  grind

grind_pattern OpResultPtr.owner!_inBounds => (res.getOwner! ctx), ctx.FieldsInBounds

end OpResultPtr

section BlockArgument

variable {arg : BlockArgumentPtr}
attribute [local grind] BlockArgument.FieldsInBounds

theorem BlockArgumentPtr.firstUse!_inBounds :
    ctx.FieldsInBounds →
    arg.InBounds ctx →
    (arg.getFirstUse! ctx).maybe OpOperandPtr.InBounds ctx := by
  intros
  have : arg.block.InBounds ctx := by grind
  grind

grind_pattern BlockArgumentPtr.firstUse!_inBounds => (arg.getFirstUse! ctx), ctx.FieldsInBounds

theorem BlockArgumentPtr.owner!_inBounds :
    ctx.FieldsInBounds →
    arg.InBounds ctx →
    (arg.getOwner! ctx).InBounds ctx := by
  intros
  have : arg.block.InBounds ctx := by grind
  grind

grind_pattern BlockArgumentPtr.owner!_inBounds => (arg.getOwner! ctx), ctx.FieldsInBounds

end BlockArgument

section OpOperand

variable {operand : OpOperandPtr}
attribute [local grind] OpOperand.FieldsInBounds

theorem OpOperandPtr.nextUse!_inBounds :
    ctx.FieldsInBounds →
    operand.InBounds ctx →
    (operand.getNextUse! ctx).maybe OpOperandPtr.InBounds ctx := by
  intros
  have : operand.op.InBounds ctx := by grind
  grind

grind_pattern OpOperandPtr.nextUse!_inBounds => (operand.getNextUse! ctx), ctx.FieldsInBounds

theorem OpOperandPtr.back!_inBounds :
    ctx.FieldsInBounds →
    operand.InBounds ctx →
    (operand.getBack! ctx).InBounds ctx := by
  intros
  have : operand.op.InBounds ctx := by grind
  grind

grind_pattern OpOperandPtr.back!_inBounds => (operand.getBack! ctx), ctx.FieldsInBounds

theorem OpOperandPtr.owner!_inBounds :
    ctx.FieldsInBounds →
    operand.InBounds ctx →
    (operand.getOwner! ctx).InBounds ctx := by
  intros
  have : operand.op.InBounds ctx := by grind
  grind

grind_pattern OpOperandPtr.owner!_inBounds => (operand.getOwner! ctx), ctx.FieldsInBounds

theorem OpOperandPtr.value!_inBounds :
    ctx.FieldsInBounds →
    operand.InBounds ctx →
    (operand.getValue! ctx).InBounds ctx := by
  intros
  have : operand.op.InBounds ctx := by grind
  grind

grind_pattern OpOperandPtr.value!_inBounds => (operand.getValue! ctx), ctx.FieldsInBounds

end OpOperand

section BlockOperand

variable {operand : BlockOperandPtr}
attribute [local grind] BlockOperand.FieldsInBounds

theorem BlockOperandPtr.nextUse!_inBounds :
    ctx.FieldsInBounds →
    operand.InBounds ctx →
    (operand.getNextUse! ctx).maybe BlockOperandPtr.InBounds ctx := by
  intros
  have : operand.op.InBounds ctx := by grind
  grind

grind_pattern BlockOperandPtr.nextUse!_inBounds => (operand.getNextUse! ctx), ctx.FieldsInBounds

theorem BlockOperandPtr.back!_inBounds :
    ctx.FieldsInBounds →
    operand.InBounds ctx →
    (operand.getBack! ctx).InBounds ctx := by
  intros
  have : operand.op.InBounds ctx := by grind
  grind

grind_pattern BlockOperandPtr.back!_inBounds => (operand.getBack! ctx), ctx.FieldsInBounds

theorem BlockOperandPtr.owner!_inBounds :
    ctx.FieldsInBounds →
    operand.InBounds ctx →
    (operand.getOwner! ctx).InBounds ctx := by
  intros
  have : operand.op.InBounds ctx := by grind
  grind

grind_pattern BlockOperandPtr.owner!_inBounds => (operand.getOwner! ctx), ctx.FieldsInBounds

theorem BlockOperandPtr.value!_inBounds :
    ctx.FieldsInBounds →
    operand.InBounds ctx →
    (operand.getValue! ctx).InBounds ctx := by
  intros
  have : operand.op.InBounds ctx := by grind
  grind

grind_pattern BlockOperandPtr.value!_inBounds => (operand.getValue! ctx), ctx.FieldsInBounds

end BlockOperand

section Operation

variable {operation : OperationPtr}
attribute [local grind] Operation.FieldsInBounds

theorem OperationPtr.prev!_inBounds :
    ctx.FieldsInBounds →
    operation.InBounds ctx →
    (operation.getPrevOp! ctx).maybe OperationPtr.InBounds ctx := by
  intros
  grind

grind_pattern OperationPtr.prev!_inBounds => (operation.getPrevOp! ctx), ctx.FieldsInBounds

theorem OperationPtr.next!_inBounds :
    ctx.FieldsInBounds →
    operation.InBounds ctx →
    (operation.getNextOp! ctx).maybe OperationPtr.InBounds ctx := by
  intros
  grind

grind_pattern OperationPtr.next!_inBounds => (operation.getNextOp! ctx), ctx.FieldsInBounds

theorem OperationPtr.parent!_inBounds :
    ctx.FieldsInBounds →
    operation.InBounds ctx →
    (operation.getParent! ctx).maybe BlockPtr.InBounds ctx := by
  intros
  grind

grind_pattern OperationPtr.parent!_inBounds => (operation.getParent! ctx), ctx.FieldsInBounds

theorem OperationPtr.getRegions!_inBounds :
    ctx.FieldsInBounds →
    operation.InBounds ctx →
    i < operation.getNumRegions! ctx →
    (operation.getRegion! ctx i).InBounds ctx := by
  intros
  grind

grind_pattern OperationPtr.getRegions!_inBounds => (operation.getRegion! ctx i), ctx.FieldsInBounds

theorem OperationPtr.getOperands!_inBounds :
    ctx.FieldsInBounds →
    operation.InBounds ctx →
    operand ∈ operation.getOperands! ctx →
    operand.InBounds ctx := by
  grind [getOperands!.mem_iff_exists_index]

grind_pattern OperationPtr.getOperands!_inBounds => operand ∈ operation.getOperands! ctx, ctx.FieldsInBounds

end Operation

section Block

variable {block : BlockPtr}

attribute [local grind] Block.FieldsInBounds

theorem BlockPtr.firstUse!_inBounds :
    ctx.FieldsInBounds →
    block.InBounds ctx →
    (block.getFirstUse! ctx).maybe BlockOperandPtr.InBounds ctx := by
  grind

grind_pattern BlockPtr.firstUse!_inBounds => (block.getFirstUse! ctx), ctx.FieldsInBounds

theorem BlockPtr.prev!_inBounds :
    ctx.FieldsInBounds →
    block.InBounds ctx →
    (block.getPrevBlock! ctx).maybe BlockPtr.InBounds ctx := by
  grind

grind_pattern BlockPtr.prev!_inBounds => (block.getPrevBlock! ctx), ctx.FieldsInBounds

theorem BlockPtr.next!_inBounds :
    ctx.FieldsInBounds →
    block.InBounds ctx →
    (block.getNextBlock! ctx).maybe BlockPtr.InBounds ctx := by
  grind

grind_pattern BlockPtr.next!_inBounds => (block.getNextBlock! ctx), ctx.FieldsInBounds

theorem BlockPtr.parent!_inBounds :
    ctx.FieldsInBounds →
    block.InBounds ctx →
    (block.getParent! ctx).maybe RegionPtr.InBounds ctx := by
  grind

grind_pattern BlockPtr.parent!_inBounds => (block.getParent! ctx), ctx.FieldsInBounds

theorem BlockPtr.firstOp!_inBounds :
    ctx.FieldsInBounds →
    block.InBounds ctx →
    (block.getFirstOp! ctx).maybe OperationPtr.InBounds ctx := by
  grind

grind_pattern BlockPtr.firstOp!_inBounds => (block.getFirstOp! ctx), ctx.FieldsInBounds

theorem BlockPtr.lastOp!_inBounds :
    ctx.FieldsInBounds →
    block.InBounds ctx →
    (block.getLastOp! ctx).maybe OperationPtr.InBounds ctx := by
  grind

grind_pattern BlockPtr.lastOp!_inBounds => (block.getLastOp! ctx), ctx.FieldsInBounds

theorem BlockPtr.arguments_inBounds :
    ctx.FieldsInBounds →
    block.InBounds ctx →
    i < block.getNumArguments! ctx →
    (block.getArgument i).InBounds ctx := by
  intros
  grind

grind_pattern BlockPtr.arguments_inBounds => (block.getArgument i), ctx.FieldsInBounds

theorem BlockPtr.getArguments!_inBounds :
    ctx.FieldsInBounds →
    block.InBounds ctx →
    blockArg ∈ block.getArguments! ctx →
    blockArg.InBounds ctx := by
  grind [getArguments!.mem_iff_exists_index]

grind_pattern BlockPtr.getArguments!_inBounds => blockArg ∈ block.getArguments! ctx, ctx.FieldsInBounds


end Block

section Region

variable {region : RegionPtr}

attribute [local grind] Region.FieldsInBounds

theorem RegionPtr.firstBlock!_inBounds :
    ctx.FieldsInBounds →
    region.InBounds ctx →
    (region.getFirstBlock! ctx).maybe BlockPtr.InBounds ctx := by
  grind

grind_pattern RegionPtr.firstBlock!_inBounds => (region.getFirstBlock! ctx), ctx.FieldsInBounds

theorem RegionPtr.lastBlock!_inBounds :
    ctx.FieldsInBounds →
    region.InBounds ctx →
    (region.getLastBlock! ctx).maybe BlockPtr.InBounds ctx := by
  grind

grind_pattern RegionPtr.lastBlock!_inBounds => (region.getLastBlock! ctx), ctx.FieldsInBounds

theorem RegionPtr.parent!_inBounds :
    ctx.FieldsInBounds →
    region.InBounds ctx →
    (region.getParent! ctx).maybe OperationPtr.InBounds ctx := by
  grind

grind_pattern RegionPtr.parent!_inBounds => (region.getParent! ctx), ctx.FieldsInBounds

end Region

section ValuePtr

variable {value : ValuePtr}

theorem ValuePtr.getFirstUse!_inBounds :
    ctx.FieldsInBounds →
    value.InBounds ctx →
    (value.getFirstUse! ctx).maybe OpOperandPtr.InBounds ctx := by
  cases value <;> grind

grind_pattern ValuePtr.getFirstUse!_inBounds => (value.getFirstUse! ctx), ctx.FieldsInBounds

theorem ValuePtr.definingOp?_inBounds :
    ctx.FieldsInBounds →
    value.InBounds ctx →
    value.definingOp?.maybe OperationPtr.InBounds ctx := by
  cases value <;> grind

grind_pattern ValuePtr.definingOp?_inBounds => value.definingOp?, ctx.FieldsInBounds

end ValuePtr

section OpOperandPtrPtr

variable {ptr : OpOperandPtrPtr}

theorem OpOperandPtrPtr.get!_inBounds :
    ctx.FieldsInBounds →
    ptr.InBounds ctx →
    (ptr.get! ctx).maybe OpOperandPtr.InBounds ctx := by
  cases ptr <;> grind

grind_pattern OpOperandPtrPtr.get!_inBounds => (ptr.get! ctx), ctx.FieldsInBounds

end OpOperandPtrPtr

section BlockOperandPtrPtr

variable {ptr : BlockOperandPtrPtr}

theorem BlockOperandPtrPtr.get!_inBounds :
    ctx.FieldsInBounds →
    ptr.InBounds ctx →
    (ptr.get! ctx).maybe BlockOperandPtr.InBounds ctx := by
  cases ptr <;> grind

grind_pattern BlockOperandPtrPtr.get!_inBounds => (ptr.get! ctx), ctx.FieldsInBounds

end BlockOperandPtrPtr

@[grind .]
theorem OperationPtr.get_fieldsInBounds (ctx : IRContext OpInfo) (ptr : OperationPtr)
    (ctxInBounds : ctx.FieldsInBounds)
    (ptrInBounds : ptr.InBounds ctx) :
    Operation.FieldsInBounds ptr ctx ptrInBounds := by
  grind [IRContext.FieldsInBounds]

@[grind .]
theorem BlockPtr.get_fieldsInBounds (ctx : IRContext OpInfo) (ptr : BlockPtr)
    (ctxInBounds : ctx.FieldsInBounds)
    (ptrInBounds : ptr.InBounds ctx) :
    Block.FieldsInBounds ptr ctx ptrInBounds := by
  grind [IRContext.FieldsInBounds]

@[grind .]
theorem RegionPtr.get_fieldsInBounds (ctx : IRContext OpInfo) (ptr : RegionPtr)
    (ctxInBounds : ctx.FieldsInBounds)
    (ptrInBounds : ptr.InBounds ctx) :
    Region.FieldsInBounds ptr ctx := by
  grind [IRContext.FieldsInBounds]

@[grind .]
theorem OpResultPtr.get_fieldsInBounds (ctx : IRContext OpInfo) (ptr : OpResultPtr)
    (ctxInBounds : ctx.FieldsInBounds)
    (ptrInBounds : ptr.InBounds ctx) :
    OpResult.FieldsInBounds ptr ctx := by
  have opInBounds := OperationPtr.get_fieldsInBounds ctx ptr.op ctxInBounds (by grind)
  grind

@[grind .]
theorem OpOperandPtr.get_fieldsInBounds (ctx : IRContext OpInfo) (ptr : OpOperandPtr)
    (ctxInBounds : ctx.FieldsInBounds)
    (ptrInBounds : ptr.InBounds ctx) :
    OpOperand.FieldsInBounds ptr ctx := by
  have opInBounds := OperationPtr.get_fieldsInBounds ctx ptr.op ctxInBounds (by grind)
  grind

@[grind .]
theorem BlockOperandPtr.get_fieldsInBounds (ctx : IRContext OpInfo) (ptr : BlockOperandPtr)
    (ctxInBounds : ctx.FieldsInBounds)
    (ptrInBounds : ptr.InBounds ctx) :
    BlockOperand.FieldsInBounds ptr ctx := by
  have opInBounds := OperationPtr.get_fieldsInBounds ctx ptr.op ctxInBounds (by grind)
  grind

@[grind .]
theorem BlockArgumentPtr.get_fieldsInBounds (ctx : IRContext OpInfo) (ptr : BlockArgumentPtr)
    (ctxInBounds : ctx.FieldsInBounds)
    (ptrInBounds : ptr.InBounds ctx) :
    BlockArgument.FieldsInBounds ptr ctx := by
  have blockInBounds :=
    BlockPtr.get_fieldsInBounds ctx ptr.block ctxInBounds (by grind)
  grind

end get

/- Preservation theorems for FieldsInBounds -/

theorem Operation.fieldsInBounds_unchanged {op : OperationPtr} (ctx ctx' : IRContext OpInfo)
    (opInBounds : op.InBounds ctx)
    (opInBounds': op.InBounds ctx')
    (hh : ctx.FieldsInBounds)
    (hFIB : Operation.FieldsInBounds op ctx opInBounds)
    (hSameInBoundsOp : ∀ op : OperationPtr, op.InBounds ctx → op.InBounds ctx')
    (hSameInBoundsOpRes : ∀ opRes : OpResultPtr, opRes.InBounds ctx ↔ opRes.InBounds ctx')
    (hSameInBoundsOpOperand : ∀ opOperand : OpOperandPtr, opOperand.InBounds ctx ↔ opOperand.InBounds ctx')
    (hSameInBoundsOpOperandPtr : ∀ opOperandPtr : OpOperandPtrPtr, opOperandPtr.InBounds ctx → opOperandPtr.InBounds ctx')
    (hSameInBoundsBlockOperand : ∀ blockOperand : BlockOperandPtr, blockOperand.InBounds ctx ↔ blockOperand.InBounds ctx')
    (hSameInBoundsBlockOperandPtr : ∀ blockOperandPtr : BlockOperandPtrPtr, blockOperandPtr.InBounds ctx → blockOperandPtr.InBounds ctx')
    (hSameInBoundsBlock : ∀ block : BlockPtr, block.InBounds ctx → block.InBounds ctx')
    (hSameInBoundsRegion : ∀ region : RegionPtr, region.InBounds ctx → region.InBounds ctx')
    (hSameInBoundsValue : ∀ value : ValuePtr, value.InBounds ctx → value.InBounds ctx')
    (hSamePrev : op.getPrevOp! ctx' = op.getPrevOp! ctx)
    (hSameNext : op.getNextOp! ctx' = op.getNextOp! ctx)
    (hSameParent : op.getParent! ctx' = op.getParent! ctx)
    (hSameNumRegions : op.getNumRegions! ctx' = op.getNumRegions! ctx)
    (hSameRegion : ∀ i, op.getRegion! ctx' i = op.getRegion! ctx i)
    (hSameResultFirstUse : ∀ res : OpResultPtr, res.op = op → res.getFirstUse! ctx' = res.getFirstUse! ctx)
    (hSameResultOwner : ∀ res : OpResultPtr, res.op = op → res.getOwner! ctx' = res.getOwner! ctx)
    (hSameOperandNextUse : ∀ opr : OpOperandPtr, opr.op = op → opr.getNextUse! ctx' = opr.getNextUse! ctx)
    (hSameOperandBack : ∀ opr : OpOperandPtr, opr.op = op → opr.getBack! ctx' = opr.getBack! ctx)
    (hSameOperandOwner : ∀ opr : OpOperandPtr, opr.op = op → opr.getOwner! ctx' = opr.getOwner! ctx)
    (hSameOperandValue : ∀ opr : OpOperandPtr, opr.op = op → opr.getValue! ctx' = opr.getValue! ctx)
    (hSameBlockOperandNextUse : ∀ opr : BlockOperandPtr, opr.op = op → opr.getNextUse! ctx' = opr.getNextUse! ctx)
    (hSameBlockOperandBack : ∀ opr : BlockOperandPtr, opr.op = op → opr.getBack! ctx' = opr.getBack! ctx)
    (hSameBlockOperandOwner : ∀ opr : BlockOperandPtr, opr.op = op → opr.getOwner! ctx' = opr.getOwner! ctx)
    (hSameBlockOperandValue : ∀ opr : BlockOperandPtr, opr.op = op → opr.getValue! ctx' = opr.getValue! ctx) :
    Operation.FieldsInBounds op ctx' (by grind) := by
  constructor
  · intros
    constructor <;> grind
  · grind
  · grind
  · grind
  · intros
    constructor <;> grind
  · grind [IRContext.FieldsInBounds, Operation.FieldsInBounds]
  · intros
    constructor <;> grind

theorem Block.fieldsInBounds_unchanged (block : BlockPtr) (ctx ctx' : IRContext OpInfo)
    (blockInBounds : block.InBounds ctx)
    (blockInBounds': block.InBounds ctx')
    (hh : ctx.FieldsInBounds)
    (_hFIB : Block.FieldsInBounds block ctx blockInBounds)
    (hSameInBoundsOp : ∀ op : OperationPtr, op.InBounds ctx → op.InBounds ctx')
    (hSameInBoundsOpOperand : ∀ opOperand : OpOperandPtr, opOperand.InBounds ctx → opOperand.InBounds ctx')
    (hSameInBoundsBlockOperand : ∀ blockOperand : BlockOperandPtr, blockOperand.InBounds ctx → blockOperand.InBounds ctx')
    (hSameInBoundsBlock : ∀ block : BlockPtr, block.InBounds ctx → block.InBounds ctx')
    (hSameInBoundsBlockArgument : ∀ blockArg : BlockArgumentPtr, blockArg.InBounds ctx ↔ blockArg.InBounds ctx')
    (hSameInBoundsRegion : ∀ region : RegionPtr, region.InBounds ctx → region.InBounds ctx')
    (hSameFirstUse : block.getFirstUse! ctx' = block.getFirstUse! ctx)
    (hSamePrev : block.getPrevBlock! ctx' = block.getPrevBlock! ctx)
    (hSameNext : block.getNextBlock! ctx' = block.getNextBlock! ctx)
    (hSameParent : block.getParent! ctx' = block.getParent! ctx)
    (hSameFirstOp : block.getFirstOp! ctx' = block.getFirstOp! ctx)
    (hSameLastOp : block.getLastOp! ctx' = block.getLastOp! ctx)
    (hSameArgumentFirstUse : ∀ arg : BlockArgumentPtr, arg.block = block → arg.getFirstUse! ctx' = arg.getFirstUse! ctx)
    (hSameArgumentOwner : ∀ arg : BlockArgumentPtr, arg.block = block → arg.getOwner! ctx' = arg.getOwner! ctx) :
    Block.FieldsInBounds block ctx' blockInBounds' := by
  constructor
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · intros
    constructor <;> grind

theorem Region.fieldsInBounds_unchanged (region : RegionPtr) (ctx ctx' : IRContext OpInfo)
    (regionInBounds : region.InBounds ctx)
    (hFIB : Region.FieldsInBounds region ctx)
    (hSameInBoundsOp : ∀ op : OperationPtr, op.InBounds ctx → op.InBounds ctx')
    (hSameInBoundsBlock : ∀ block : BlockPtr, block.InBounds ctx → block.InBounds ctx')
    (hSameFirstBlock : region.getFirstBlock! ctx' = region.getFirstBlock! ctx)
    (hSameLastBlock : region.getLastBlock! ctx' = region.getLastBlock! ctx)
    (hSameParent : region.getParent! ctx' = region.getParent! ctx) :
    Region.FieldsInBounds region ctx' := by
  grind

attribute [local grind] OpResult.FieldsInBounds BlockArgument.FieldsInBounds
  OpOperand.FieldsInBounds BlockOperand.FieldsInBounds Operation.FieldsInBounds
  Block.FieldsInBounds Region.FieldsInBounds BlockOperandPtrPtr.InBounds

macro "prove_fieldsInBounds" : tactic => `(tactic|
  (rintro hctx
   constructor
   · intros op hop
     constructor
     · intros res hres heq
       constructor
       · grind
       · grind
     · grind
     · grind
     · grind
     · intros operand hoperand heq
       constructor <;> grind
     · grind
     · rintro opr hopr heq
       constructor <;> grind
   · intros block blockIn
     constructor
     · grind
     · grind
     · grind
     · grind
     · grind
     · grind
     · intros
       constructor <;> grind (ematch := 20)
   · grind))

macro "prove_fieldsInBounds_operation" ctx:ident : tactic => `(tactic|
  (rintro hctx
   constructor
   · intros op hop
     constructor
     · intros res hres heq
       constructor
       · grind
       · grind
     · grind
     · grind
     · grind
     · intros operand hoperand heq
       constructor <;> grind
     · grind
     · rintro opr hopr heq
       constructor <;> grind
   · intros block blockIn
     apply Block.fieldsInBounds_unchanged (ctx := $ctx) <;> grind
   · grind))

macro "prove_fieldsInBounds_block" ctx:ident: tactic => `(tactic|
  (intros hctx
   constructor
   · intros
     apply Operation.fieldsInBounds_unchanged (ctx := $ctx) <;> grind
   · intros block blockIn
     constructor
     · grind
     · grind
     · grind
     · grind
     · grind
     · grind
     · intros
       constructor <;> grind
   · intros
     apply Region.fieldsInBounds_unchanged (ctx := $ctx) <;> grind))

macro "prove_fieldsInBounds_region" ctx:ident: tactic => `(tactic|
  (intros hctx
   constructor
   · intros
     apply Operation.fieldsInBounds_unchanged (ctx := $ctx) <;> grind
   · intros
     apply Block.fieldsInBounds_unchanged (ctx := $ctx) <;> grind
   · intros
     constructor <;> grind))

@[grind .]
theorem IRContext.empty_fieldsInBounds : (empty OpInfo).FieldsInBounds := by
  constructor <;> grind

@[grind .]
theorem OperationPtr.setNextOp_fieldsInBounds (hnew : newOp.maybe OperationPtr.InBounds ctx) :
    ctx.FieldsInBounds → (setNextOp op ctx newOp h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem OperationPtr.setPrevOp_fieldsInBounds (hnew : newOp.maybe OperationPtr.InBounds ctx) :
    ctx.FieldsInBounds → (setPrevOp op ctx newOp h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem OperationPtr.setParent_fieldsInBounds (hnew : newOp.maybe BlockPtr.InBounds ctx) :
    ctx.FieldsInBounds → (setParent op ctx newOp h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem OperationPtr.setRegions_fieldsInBounds {ctx : IRContext OpInfo} {h} (hnew : ∀ r ∈ newRegions, r.InBounds ctx) :
    ctx.FieldsInBounds → (setRegions op ctx newRegions h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem OperationPtr.pushRegion_fieldsInBounds {ctx : IRContext OpInfo} {h} (hnew : newRegion.InBounds ctx) :
    ctx.FieldsInBounds → (pushRegion op ctx newRegion h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem OperationPtr.pushResult_fieldsInBounds {newResult : OpResult} {op : OperationPtr} h
    (hfirstUse : newResult.firstUse.maybe OpOperandPtr.InBounds (op.pushResult ctx newResult h))
    (howner : newResult.owner.InBounds (op.pushResult ctx newResult h)) :
    ctx.FieldsInBounds → (op.pushResult ctx newResult h).FieldsInBounds := by
  prove_fieldsInBounds

@[grind .]
theorem OperationPtr.setProperties_fieldsInBounds
    {Dialect : Type} [IsOpCode Dialect] [HasDialect OpInfo Dialect]
    {op : OperationPtr} {inBounds : op.InBounds ctx}
    {opCode : Dialect} {newProperties : propertiesOf opCode}
    {hprop : op.getOpType! ctx = opCode} :
    ctx.FieldsInBounds → (setProperties op ctx opCode newProperties inBounds hprop).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem OperationPtr.setAttributes_fieldsInBounds {op : OperationPtr} {opIn : op.InBounds ctx} :
    ctx.FieldsInBounds → (op.setAttributes ctx newAttrs opIn).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem OperationPtr.setOperands_push_fieldsInBounds (newOperand : OpOperand)
    (hnextUse : newOperand.nextUse.maybe OpOperandPtr.InBounds ctx)
    (hback : newOperand.back.InBounds ctx)
    (howner : newOperand.owner.InBounds ctx)
    (hvalue : newOperand.value.InBounds ctx) :
    ctx.FieldsInBounds → (pushOperand op ctx newOperand h).FieldsInBounds := by
  prove_fieldsInBounds

@[grind .]
theorem OperationPtr.pushBlockOperand_push_fieldsInBounds
    (newOperand : BlockOperand)
    (hnextUse : newOperand.nextUse.maybe BlockOperandPtr.InBounds ctx)
    (hback : newOperand.back.InBounds ctx)
    (howner : newOperand.owner.InBounds ctx)
    (hvalue : newOperand.value.InBounds ctx) :
    ctx.FieldsInBounds → (pushBlockOperand op ctx newOperand h).FieldsInBounds := by
  prove_fieldsInBounds

attribute [local grind] Operation.empty in
@[grind .]
theorem OperationPtr.allocEmpty_fieldsInBounds
    {Dialect : Type} [IsOpCode Dialect] [HasDialect OpInfo Dialect]
    {type : Dialect} {prop : propertiesOf type}
    (heq : allocEmpty ctx type prop = some (ctx', ptr')) :
    ctx.FieldsInBounds → ctx'.FieldsInBounds := by
  prove_fieldsInBounds

@[grind .]
theorem BlockOperandPtr.setBack_fieldsInBounds {blockOperand} {ctx : IRContext OpInfo} {h newBack} (hp : newBack.InBounds ctx) :
    ctx.FieldsInBounds → (setBack blockOperand ctx newBack h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem BlockOperandPtr.setOwner_fieldsInBounds {blockOperand} {ctx : IRContext OpInfo} {h newOwner} (hp : newOwner.InBounds ctx) :
    ctx.FieldsInBounds → (setOwner blockOperand ctx newOwner h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem BlockOperandPtr.setNextUse_fieldsInBounds {blockOperand} {ctx : IRContext OpInfo} {h newNextUse} (hp : newNextUse.maybe BlockOperandPtr.InBounds ctx) :
    ctx.FieldsInBounds → (setNextUse blockOperand ctx newNextUse h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem BlockOperandPtr.setValue_fieldsInBounds {blockOperand} {ctx : IRContext OpInfo} {h newValue} (hp : newValue.InBounds ctx) :
    ctx.FieldsInBounds → (setValue blockOperand ctx newValue h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem BlockArgumentPtr.setType_fieldsInBounds :
    ctx.FieldsInBounds → (setType blockArgPtr ctx newType h).FieldsInBounds := by
  prove_fieldsInBounds_block ctx

@[grind .]
theorem BlockArgumentPtr.setFirstUse_fieldsInBounds
    (hnew : newFirstUse.maybe OpOperandPtr.InBounds ctx) :
    ctx.FieldsInBounds → (setFirstUse blockArgPtr ctx newFirstUse h).FieldsInBounds := by
  prove_fieldsInBounds_block ctx

@[grind .]
theorem BlockArgumentPtr.setLoc_fieldsInBounds :
    ctx.FieldsInBounds → (setLoc blockArgPtr ctx newLoc h).FieldsInBounds := by
  prove_fieldsInBounds_block ctx

@[grind .]
theorem BlockPtr.setParent_fieldsInBounds (hp : parent.maybe RegionPtr.InBounds ctx) :
    ctx.FieldsInBounds → (setParent block ctx parent h).FieldsInBounds := by
  prove_fieldsInBounds_block ctx

@[grind .]
theorem BlockPtr.setFirstUse_fieldsInBounds (hp : newFirstUse.maybe BlockOperandPtr.InBounds ctx) :
    ctx.FieldsInBounds → (setFirstUse block ctx newFirstUse h).FieldsInBounds := by
  prove_fieldsInBounds_block ctx

@[grind .]
theorem BlockPtr.setFirstOp_fieldsInBounds (hp : newFirstOp.maybe OperationPtr.InBounds ctx) :
    ctx.FieldsInBounds → (setFirstOp block ctx newFirstOp h).FieldsInBounds := by
  prove_fieldsInBounds_block ctx

@[grind .]
theorem BlockPtr.setLastOp_fieldsInBounds (hp : newLastOp.maybe OperationPtr.InBounds ctx) :
    ctx.FieldsInBounds → (setLastOp block ctx newLastOp h).FieldsInBounds := by
  prove_fieldsInBounds_block ctx

@[grind .]
theorem BlockPtr.setNextBlock_fieldsInBounds (hp : newNextBlock.maybe BlockPtr.InBounds ctx) :
    ctx.FieldsInBounds → (setNextBlock block ctx newNextBlock h).FieldsInBounds := by
  prove_fieldsInBounds_block ctx

@[grind .]
theorem BlockPtr.setPrevBlock_fieldsInBounds (hp : newPrevBlock.maybe BlockPtr.InBounds ctx) :
    ctx.FieldsInBounds → (setPrevBlock block ctx newPrevBlock h).FieldsInBounds := by
  prove_fieldsInBounds_block ctx

attribute [local grind] Block.empty in
@[grind .]
theorem BlockPtr.allocEmpty_fieldsInBounds (heq : allocEmpty ctx = some (ctx', ptr')) :
    ctx.FieldsInBounds → ctx'.FieldsInBounds := by
  prove_fieldsInBounds

attribute [local grind →] Array.getElem_mem in
attribute [local grind] Block.empty in
attribute [local grind =] BlockArgumentPtr.inBounds_def in
@[grind .]
theorem BlockPtr.setArguments_fieldsInBounds
    (hIncreaseSize : block.getNumArguments! ctx ≤ newArguments.size)
    (hfirstUse : ∀ arg ∈ newArguments, arg.firstUse.maybe OpOperandPtr.InBounds ctx)
    (howner : ∀ arg ∈ newArguments, arg.owner.InBounds ctx) :
    ctx.FieldsInBounds → (setArguments block ctx newArguments h).FieldsInBounds := by
  prove_fieldsInBounds

attribute [local grind →] Array.getElem_mem in
attribute [local grind] Block.empty in
attribute [local grind =] BlockArgumentPtr.inBounds_def in
@[grind .]
theorem BlockPtr.pushArgument_fieldsInBounds
    (hfirstUse : newArgument.firstUse.maybe OpOperandPtr.InBounds ctx)
    (howner : newArgument.owner.InBounds ctx) :
    ctx.FieldsInBounds → (pushArgument block ctx newArgument h).FieldsInBounds := by
  prove_fieldsInBounds

@[grind .]
theorem OpOperandPtr.setNextUse_fieldsInBounds (hp : newNextUse.maybe OpOperandPtr.InBounds ctx) :
    ctx.FieldsInBounds → (setNextUse opOperand ctx newNextUse h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem OpOperandPtr.setBack_fieldsInBounds (hp : newBack.InBounds ctx) :
    ctx.FieldsInBounds → (setBack opOperand ctx newBack h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem OpOperandPtr.setOwner_fieldsInBounds (hp : newOwner.InBounds ctx) :
    ctx.FieldsInBounds → (setOwner opOperand ctx newOwner h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem OpOperandPtrPtr.set_fieldsInBounds_maybe (hnew : newPtr.maybe OpOperandPtr.InBounds ctx) :
    ctx.FieldsInBounds → (set opOperandPtr ctx newPtr h).FieldsInBounds := by
  prove_fieldsInBounds

@[grind .]
theorem OpOperandPtr.setValue_fieldsInBounds (hp : newValue.InBounds ctx) :
    ctx.FieldsInBounds → (setValue opOperand ctx newValue h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem OpResultPtr.setType_fieldsInBounds :
    ctx.FieldsInBounds → (setType opOperand ctx newType h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem OpResultPtr.setFirstUse_fieldsInBounds_maybe (hnew : newFirstUse.maybe OpOperandPtr.InBounds ctx) :
    ctx.FieldsInBounds → (setFirstUse opOperand ctx newFirstUse h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem RegionPtr.setParent_fieldsInBounds (hnew : newParent.maybe OperationPtr.InBounds ctx) :
    ctx.FieldsInBounds → (setParent region ctx newParent h).FieldsInBounds := by
  prove_fieldsInBounds_region ctx

@[grind .]
theorem RegionPtr.setFirstBlock_fieldsInBounds (hnew : newFirstBlock.maybe BlockPtr.InBounds ctx) :
    ctx.FieldsInBounds → (setFirstBlock region ctx newFirstBlock h).FieldsInBounds := by
  prove_fieldsInBounds_region ctx

@[grind .]
theorem RegionPtr.setLastBlock_fieldsInBounds (hnew : newLastBlock.maybe BlockPtr.InBounds ctx) :
    ctx.FieldsInBounds → (setLastBlock region ctx newLastBlock h).FieldsInBounds := by
  prove_fieldsInBounds_region ctx

attribute [local grind] Region.empty in
@[grind .]
theorem RegionPtr.allocEmpty_fieldsInBounds (heq : allocEmpty ctx = some (ctx', rg')) :
    ctx.FieldsInBounds → ctx'.FieldsInBounds := by
  prove_fieldsInBounds

@[grind .]
theorem BlockOperandPtrPtr.set_fieldsInBounds_maybe  (hnew : new.maybe BlockOperandPtr.InBounds ctx) :
    ctx.FieldsInBounds → (set blockOperandPtr ctx new h).FieldsInBounds := by
  cases new <;> grind

@[grind .]
theorem ValuePtr.setType_fieldsInBounds :
    ctx.FieldsInBounds → (setType value ctx newType h).FieldsInBounds := by
  cases value <;> simp only [setType_OpResultPtr, setType_BlockArgumentPtr] <;> grind

@[grind .]
theorem ValuePtr.setFirstUse_fieldsInBounds_maybe (hnew : newFirstUse.maybe OpOperandPtr.InBounds ctx) :
    ctx.FieldsInBounds → (setFirstUse value ctx newFirstUse h).FieldsInBounds := by
  cases value <;> simp only [setFirstUse_OpResultPtr, setFirstUse_BlockArgumentPtr] <;> grind
