module

public import Veir.IR.Basic
import Veir.IR.InBounds
import Veir.IR.GetSet

namespace Veir

@[expose] public section

/-
  FieldsInBounds implementation.
  These are the predicates that ensures that all pointers in a program are in bounds.
-/

structure OpResult.FieldsInBounds (res: OpResult) (ctx: IRContext) : Prop where
  firstUse_inBounds : res.firstUse.maybe OpOperandPtr.InBounds ctx
  owner_inBounds: res.owner.InBounds ctx

structure OpOperand.FieldsInBounds (operand: OpOperand) (ctx: IRContext) : Prop where
  nextUse_inBounds : operand.nextUse.maybe OpOperandPtr.InBounds ctx
  back_inBounds: operand.back.InBounds ctx
  owner_inBounds: operand.owner.InBounds ctx
  value_inBounds: operand.value.InBounds ctx

structure BlockOperand.FieldsInBounds (operand: BlockOperand) (ctx: IRContext) : Prop where
  nextUse_inBounds : operand.nextUse.maybe BlockOperandPtr.InBounds ctx
  back_inBounds: operand.back.InBounds ctx
  owner_inBounds: operand.owner.InBounds ctx
  value_inBounds: operand.value.InBounds ctx

structure Operation.FieldsInBounds (operation: OperationPtr) (ctx: IRContext) (hin : operation.InBounds ctx) : Prop where
  results_inBounds (res : OpResultPtr) (hres: res.InBounds ctx) : res.op = operation → (res.get ctx).FieldsInBounds ctx
  prev_inBounds : (operation.get ctx hin).prev.maybe OperationPtr.InBounds ctx
  next_inBounds : (operation.get ctx hin).next.maybe OperationPtr.InBounds ctx
  parent_inBounds : (operation.get ctx hin).parent.maybe BlockPtr.InBounds ctx
  blockOperands_inBounds (operand : BlockOperandPtr) (h : operand.InBounds ctx):
    operand.op = operation → BlockOperand.FieldsInBounds (operand.get ctx h) ctx
  regions_inBounds i (hi: i < operation.getNumRegions ctx hin) :
    (operation.getRegion ctx i hin hi).InBounds ctx
  operands_inBounds (operand : OpOperandPtr) (h : operand.InBounds ctx):
    operand.op = operation → OpOperand.FieldsInBounds (operand.get ctx h) ctx

structure BlockArgument.FieldsInBounds (arg: BlockArgument) (ctx: IRContext) : Prop where
  firstUse_inBounds : arg.firstUse.maybe OpOperandPtr.InBounds ctx
  owner_inBounds: arg.owner.InBounds ctx

@[local grind]
structure Block.FieldsInBounds (block: BlockPtr) (ctx: IRContext) (hin : block.InBounds ctx) : Prop where
  firstUse_inBounds : (block.get ctx hin).firstUse.maybe BlockOperandPtr.InBounds ctx
  prev_inBounds : (block.get ctx hin).prev.maybe BlockPtr.InBounds ctx
  next_inBounds : (block.get ctx hin).next.maybe BlockPtr.InBounds ctx
  parent_inBounds : (block.get ctx hin).parent.maybe RegionPtr.InBounds ctx
  firstOp_inBounds : (block.get ctx hin).firstOp.maybe OperationPtr.InBounds ctx
  lastOp_inBounds : (block.get ctx hin).lastOp.maybe OperationPtr.InBounds ctx
  arguments_inBounds (arg : BlockArgumentPtr) (h : arg.InBounds ctx) :
    arg.block = block → (arg.get ctx h).FieldsInBounds ctx

@[local grind]
structure Region.FieldsInBounds (region: Region) (ctx: IRContext) : Prop where
  firstBlock_inBounds block: region.firstBlock = some block → block.InBounds ctx
  lastBlock_inBounds block: region.lastBlock = some block → block.InBounds ctx
  parent_inBounds parent: region.parent = some parent → parent.InBounds ctx

/--
    Ensures that all pointers referenced by any structure in the context are in bounds.
-/
structure IRContext.FieldsInBounds (ctx: IRContext) : Prop where
  topLevelOp_inBounds: ctx.topLevelOp.InBounds ctx
  operations_inBounds (op: OperationPtr) opIn: Operation.FieldsInBounds op ctx opIn
  blocks_inBounds (block: BlockPtr) blockIn: Block.FieldsInBounds block ctx blockIn
  regions_inBounds (region: RegionPtr) regionIn: (region.get ctx regionIn).FieldsInBounds ctx

attribute [grind .] IRContext.FieldsInBounds.topLevelOp_inBounds

attribute [local grind =] Option.maybe_def

section get

/-
  Theorems combining `get` methods with `IRContext.fieldsInBounds`.
  These should be the only theorems that unfolds the `FieldsInBounds
  structures.
-/

variable {ctx : IRContext}

attribute [local grind] IRContext.FieldsInBounds
  OpOperand.FieldsInBounds BlockOperand.FieldsInBounds
  Operation.FieldsInBounds Block.FieldsInBounds Region.FieldsInBounds

section OpResultPtr

variable {res : OpResultPtr}
attribute [local grind] OpResult.FieldsInBounds

theorem OpResultPtr.firstUse!_inBounds :
    ctx.FieldsInBounds →
    res.InBounds ctx →
    (res.get! ctx).firstUse.maybe OpOperandPtr.InBounds ctx := by
  grind

grind_pattern OpResultPtr.firstUse!_inBounds => (res.get! ctx).firstUse, ctx.FieldsInBounds

theorem OpResultPtr.owner!_inBounds :
    ctx.FieldsInBounds →
    res.InBounds ctx →
    (res.get! ctx).owner.InBounds ctx := by
  grind

grind_pattern OpResultPtr.owner!_inBounds => (res.get! ctx).owner, ctx.FieldsInBounds

end OpResultPtr

section BlockArgument

variable {arg : BlockArgumentPtr}
attribute [local grind] BlockArgument.FieldsInBounds

theorem BlockArgumentPtr.firstUse!_inBounds :
    ctx.FieldsInBounds →
    arg.InBounds ctx →
    (arg.get! ctx).firstUse.maybe OpOperandPtr.InBounds ctx := by
  intros
  have : arg.block.InBounds ctx := by grind
  grind

grind_pattern BlockArgumentPtr.firstUse!_inBounds => (arg.get! ctx).firstUse, ctx.FieldsInBounds

theorem BlockArgumentPtr.owner!_inBounds :
    ctx.FieldsInBounds →
    arg.InBounds ctx →
    (arg.get! ctx).owner.InBounds ctx := by
  intros
  have : arg.block.InBounds ctx := by grind
  grind

grind_pattern BlockArgumentPtr.owner!_inBounds => (arg.get! ctx).owner, ctx.FieldsInBounds

end BlockArgument

section OpOperand

variable {operand : OpOperandPtr}
attribute [local grind] OpOperand.FieldsInBounds

theorem OpOperandPtr.nextUse!_inBounds :
    ctx.FieldsInBounds →
    operand.InBounds ctx →
    (operand.get! ctx).nextUse.maybe OpOperandPtr.InBounds ctx := by
  intros
  have : operand.op.InBounds ctx := by grind
  grind

grind_pattern OpOperandPtr.nextUse!_inBounds => (operand.get! ctx).nextUse, ctx.FieldsInBounds

theorem OpOperandPtr.back!_inBounds :
    ctx.FieldsInBounds →
    operand.InBounds ctx →
    (operand.get! ctx).back.InBounds ctx := by
  intros
  have : operand.op.InBounds ctx := by grind
  grind

grind_pattern OpOperandPtr.back!_inBounds => (operand.get! ctx).back, ctx.FieldsInBounds

theorem OpOperandPtr.owner!_inBounds :
    ctx.FieldsInBounds →
    operand.InBounds ctx →
    (operand.get! ctx).owner.InBounds ctx := by
  intros
  have : operand.op.InBounds ctx := by grind
  grind

grind_pattern OpOperandPtr.owner!_inBounds => (operand.get! ctx).owner, ctx.FieldsInBounds

theorem OpOperandPtr.value!_inBounds :
    ctx.FieldsInBounds →
    operand.InBounds ctx →
    (operand.get! ctx).value.InBounds ctx := by
  intros
  have : operand.op.InBounds ctx := by grind
  grind

grind_pattern OpOperandPtr.value!_inBounds => (operand.get! ctx).value, ctx.FieldsInBounds

end OpOperand

section BlockOperand

variable {operand : BlockOperandPtr}
attribute [local grind] BlockOperand.FieldsInBounds

theorem BlockOperandPtr.nextUse!_inBounds :
    ctx.FieldsInBounds →
    operand.InBounds ctx →
    (operand.get! ctx).nextUse.maybe BlockOperandPtr.InBounds ctx := by
  intros
  have : operand.op.InBounds ctx := by grind
  grind

grind_pattern BlockOperandPtr.nextUse!_inBounds => (operand.get! ctx).nextUse, ctx.FieldsInBounds

theorem BlockOperandPtr.back!_inBounds :
    ctx.FieldsInBounds →
    operand.InBounds ctx →
    (operand.get! ctx).back.InBounds ctx := by
  intros
  have : operand.op.InBounds ctx := by grind
  grind

grind_pattern BlockOperandPtr.back!_inBounds => (operand.get! ctx).back, ctx.FieldsInBounds

theorem BlockOperandPtr.owner!_inBounds :
    ctx.FieldsInBounds →
    operand.InBounds ctx →
    (operand.get! ctx).owner.InBounds ctx := by
  intros
  have : operand.op.InBounds ctx := by grind
  grind

grind_pattern BlockOperandPtr.owner!_inBounds => (operand.get! ctx).owner, ctx.FieldsInBounds

theorem BlockOperandPtr.value!_inBounds :
    ctx.FieldsInBounds →
    operand.InBounds ctx →
    (operand.get! ctx).value.InBounds ctx := by
  intros
  have : operand.op.InBounds ctx := by grind
  grind

grind_pattern BlockOperandPtr.value!_inBounds => (operand.get! ctx).value, ctx.FieldsInBounds

end BlockOperand

section Operation

variable {operation : OperationPtr}
attribute [local grind] Operation.FieldsInBounds

theorem OperationPtr.prev!_inBounds :
    ctx.FieldsInBounds →
    operation.InBounds ctx →
    (operation.get! ctx).prev.maybe OperationPtr.InBounds ctx := by
  intros
  grind

grind_pattern OperationPtr.prev!_inBounds => (operation.get! ctx).prev, ctx.FieldsInBounds

theorem OperationPtr.next!_inBounds :
    ctx.FieldsInBounds →
    operation.InBounds ctx →
    (operation.get! ctx).next.maybe OperationPtr.InBounds ctx := by
  intros
  grind

grind_pattern OperationPtr.next!_inBounds => (operation.get! ctx).next, ctx.FieldsInBounds

theorem OperationPtr.parent!_inBounds :
    ctx.FieldsInBounds →
    operation.InBounds ctx →
    (operation.get! ctx).parent.maybe BlockPtr.InBounds ctx := by
  intros
  grind

grind_pattern OperationPtr.parent!_inBounds => (operation.get! ctx).parent, ctx.FieldsInBounds

theorem OperationPtr.getRegions!_inBounds :
    ctx.FieldsInBounds →
    operation.InBounds ctx →
    i < operation.getNumRegions! ctx →
    (operation.getRegion! ctx i).InBounds ctx := by
  intros
  grind

grind_pattern OperationPtr.getRegions!_inBounds => (operation.getRegion! ctx i), ctx.FieldsInBounds

end Operation

section Block

variable {block : BlockPtr}

attribute [local grind] Block.FieldsInBounds

theorem BlockPtr.firstUse!_inBounds :
    ctx.FieldsInBounds →
    block.InBounds ctx →
    (block.get! ctx).firstUse.maybe BlockOperandPtr.InBounds ctx := by
  grind

grind_pattern BlockPtr.firstUse!_inBounds => (block.get! ctx).firstUse, ctx.FieldsInBounds

theorem BlockPtr.prev!_inBounds :
    ctx.FieldsInBounds →
    block.InBounds ctx →
    (block.get! ctx).prev.maybe BlockPtr.InBounds ctx := by
  grind

grind_pattern BlockPtr.prev!_inBounds => (block.get! ctx).prev, ctx.FieldsInBounds

theorem BlockPtr.next!_inBounds :
    ctx.FieldsInBounds →
    block.InBounds ctx →
    (block.get! ctx).next.maybe BlockPtr.InBounds ctx := by
  grind

grind_pattern BlockPtr.next!_inBounds => (block.get! ctx).next, ctx.FieldsInBounds

theorem BlockPtr.parent!_inBounds :
    ctx.FieldsInBounds →
    block.InBounds ctx →
    (block.get! ctx).parent.maybe RegionPtr.InBounds ctx := by
  grind

grind_pattern BlockPtr.parent!_inBounds => (block.get! ctx).parent, ctx.FieldsInBounds

theorem BlockPtr.firstOp!_inBounds :
    ctx.FieldsInBounds →
    block.InBounds ctx →
    (block.get! ctx).firstOp.maybe OperationPtr.InBounds ctx := by
  grind

grind_pattern BlockPtr.firstOp!_inBounds => (block.get! ctx).firstOp, ctx.FieldsInBounds

theorem BlockPtr.lastOp!_inBounds :
    ctx.FieldsInBounds →
    block.InBounds ctx →
    (block.get! ctx).lastOp.maybe OperationPtr.InBounds ctx := by
  grind

grind_pattern BlockPtr.lastOp!_inBounds => (block.get! ctx).lastOp, ctx.FieldsInBounds

theorem BlockPtr.arguments_inBounds :
    ctx.FieldsInBounds →
    block.InBounds ctx →
    i < block.getNumArguments! ctx →
    (block.getArgument i).InBounds ctx := by
  intros
  grind

grind_pattern BlockPtr.arguments_inBounds => (block.getArgument i), ctx.FieldsInBounds

end Block

section Region

variable {region : RegionPtr}

attribute [local grind] Region.FieldsInBounds

theorem RegionPtr.firstBlock!_inBounds :
    ctx.FieldsInBounds →
    region.InBounds ctx →
    (region.get! ctx).firstBlock.maybe BlockPtr.InBounds ctx := by
  grind

grind_pattern RegionPtr.firstBlock!_inBounds => (region.get! ctx).firstBlock, ctx.FieldsInBounds

theorem RegionPtr.lastBlock!_inBounds :
    ctx.FieldsInBounds →
    region.InBounds ctx →
    (region.get! ctx).lastBlock.maybe BlockPtr.InBounds ctx := by
  grind

grind_pattern RegionPtr.lastBlock!_inBounds => (region.get! ctx).lastBlock, ctx.FieldsInBounds

theorem RegionPtr.parent!_inBounds :
    ctx.FieldsInBounds →
    region.InBounds ctx →
    (region.get! ctx).parent.maybe OperationPtr.InBounds ctx := by
  grind

grind_pattern RegionPtr.parent!_inBounds => (region.get! ctx).parent, ctx.FieldsInBounds

end Region

section ValuePtr

variable {value : ValuePtr}

theorem ValuePtr.getFirstUse!_inBounds :
    ctx.FieldsInBounds →
    value.InBounds ctx →
    (value.getFirstUse! ctx).maybe OpOperandPtr.InBounds ctx := by
  cases value <;> grind

grind_pattern ValuePtr.getFirstUse!_inBounds => (value.getFirstUse! ctx), ctx.FieldsInBounds

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
theorem OperationPtr.get_fieldsInBounds (ctx: IRContext) (ptr: OperationPtr)
    (ctxInBounds: ctx.FieldsInBounds)
    (ptrInBounds: ptr.InBounds ctx) :
    Operation.FieldsInBounds ptr ctx ptrInBounds := by
  grind [IRContext.FieldsInBounds]

@[grind .]
theorem BlockPtr.get_fieldsInBounds (ctx: IRContext) (ptr: BlockPtr)
    (ctxInBounds: ctx.FieldsInBounds)
    (ptrInBounds: ptr.InBounds ctx) :
    Block.FieldsInBounds ptr ctx ptrInBounds := by
  grind [IRContext.FieldsInBounds]

@[grind .]
theorem RegionPtr.get_fieldsInBounds (ctx: IRContext) (ptr: RegionPtr)
    (ctxInBounds: ctx.FieldsInBounds)
    (ptrInBounds: ptr.InBounds ctx) :
    (ptr.get ctx (by grind)).FieldsInBounds ctx := by
  grind [IRContext.FieldsInBounds]

@[grind .]
theorem OpResultPtr.get_fieldsInBounds (ctx: IRContext) (ptr: OpResultPtr)
    (ctxInBounds: ctx.FieldsInBounds)
    (ptrInBounds: ptr.InBounds ctx) :
    (ptr.get ctx).FieldsInBounds ctx := by
  have opInBounds := OperationPtr.get_fieldsInBounds ctx ptr.op ctxInBounds (by grind)
  grind

@[grind .]
theorem OpOperandPtr.get_fieldsInBounds (ctx: IRContext) (ptr: OpOperandPtr)
    (ctxInBounds: ctx.FieldsInBounds)
    (ptrInBounds: ptr.InBounds ctx) :
    OpOperand.FieldsInBounds (ptr.get ctx ptrInBounds) ctx := by
  have opInBounds := OperationPtr.get_fieldsInBounds ctx ptr.op ctxInBounds (by grind)
  grind

@[grind .]
theorem BlockOperandPtr.get_fieldsInBounds (ctx: IRContext) (ptr: BlockOperandPtr)
    (ctxInBounds: ctx.FieldsInBounds)
    (ptrInBounds: ptr.InBounds ctx) :
    BlockOperand.FieldsInBounds (ptr.get ctx ptrInBounds) ctx := by
  have opInBounds := OperationPtr.get_fieldsInBounds ctx ptr.op ctxInBounds (by grind)
  grind

@[grind .]
theorem BlockArgumentPtr.get_fieldsInBounds (ctx: IRContext) (ptr: BlockArgumentPtr)
    (ctxInBounds: ctx.FieldsInBounds)
    (ptrInBounds: ptr.InBounds ctx) :
    (ptr.get ctx (by grind)).FieldsInBounds ctx := by
  have blockInBounds :=
    BlockPtr.get_fieldsInBounds ctx ptr.block ctxInBounds (by grind)
  grind

end get

/- Preservation theorems for FieldsInBounds -/

theorem Operation.fieldsInBounds_unchanged {op: OperationPtr} (ctx ctx' : IRContext)
    (opInBounds: op.InBounds ctx)
    (opInBounds': op.InBounds ctx')
    (hh : ctx.FieldsInBounds)
    (hFIB : Operation.FieldsInBounds op ctx opInBounds)
    (hSameInBounds: ∀ ptr, GenericPtr.InBounds ptr ctx ↔ GenericPtr.InBounds ptr ctx')
    (hSameOps: ∀ op opInBounds, OperationPtr.get op ctx opInBounds = OperationPtr.get op ctx' (by grind)) :
    Operation.FieldsInBounds op ctx' (by grind) := by
  have heq : op.get! ctx = op.get! ctx' := by grind
  constructor
  · intros
    constructor <;> grind [→ OpResultPtr.get!_eq_of_OperationPtr_get!_eq]
  · grind
  · grind
  · grind
  · intros opr hopr heq
    have := @BlockOperandPtr.get!_eq_of_OperationPtr_get!_eq
    constructor <;> grind
  · have ha := OperationPtr.getRegion!_eq_of_OperationPtr_get!_eq heq
    have hb := OperationPtr.getNumRegions!_eq_of_OperationPtr_get!_eq heq
    grind [IRContext.FieldsInBounds, Operation.FieldsInBounds]
  · intros opr hopr heq
    have : opr.op.get! ctx = opr.op.get! ctx' := by grind
    have := @OpOperandPtr.get!_eq_of_OperationPtr_get!_eq
    constructor <;> grind

theorem Block.fieldsInBounds_unchanged (block: BlockPtr) (ctx ctx' : IRContext)
    (blockInBounds: block.InBounds ctx)
    (blockInBounds': block.InBounds ctx')
    (hh : ctx.FieldsInBounds)
    (_hFIB : Block.FieldsInBounds block ctx blockInBounds)
    (hSameInBounds: ∀ ptr, GenericPtr.InBounds ptr ctx ↔ GenericPtr.InBounds ptr ctx')
    (hSameBlocks : ∀ block blockInBounds, BlockPtr.get block ctx blockInBounds = BlockPtr.get block ctx' (by grind)) :
    Block.FieldsInBounds block ctx' blockInBounds' := by
  constructor
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · intros
    constructor <;> grind [BlockArgumentPtr.get!_eq_of_BlockPtr_get!_eq]

theorem Region.fieldsInBounds_unchanged (region: RegionPtr) (ctx ctx' : IRContext)
    (regionInBounds: region.InBounds ctx)
    (regionInBounds': region.InBounds ctx')
    (hFIB : (region.get ctx regionInBounds).FieldsInBounds ctx)
    (hSameInBounds: ∀ ptr, GenericPtr.InBounds ptr ctx → GenericPtr.InBounds ptr ctx')
    (hSameRegions : ∀ region regionInBounds, RegionPtr.get region ctx regionInBounds = RegionPtr.get region ctx' (by grind)) :
    (region.get ctx' (by grind)).FieldsInBounds ctx' := by
  grind

attribute [local grind] OpResult.FieldsInBounds BlockArgument.FieldsInBounds
  OpOperand.FieldsInBounds BlockOperand.FieldsInBounds Operation.FieldsInBounds
  Block.FieldsInBounds Region.FieldsInBounds BlockOperandPtrPtr.InBounds

macro "prove_fieldsInBounds_operation" ctx:ident : tactic => `(tactic|
  (rintro hctx
   constructor
   · grind
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

macro "prove_fieldsInBounds_block" ctx:ident : tactic => `(tactic|
  (intros hctx
   constructor
   · grind
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

macro "prove_fieldsInBounds_region" ctx:ident : tactic => `(tactic|
  (intros hctx
   constructor
   · grind
   · intros
     apply Operation.fieldsInBounds_unchanged (ctx := $ctx) <;> grind
   · intros
     apply Block.fieldsInBounds_unchanged (ctx := $ctx) <;> grind
   · intros
     constructor <;> grind))

-- attribute [local grind] OperationPtr.setNextOp in
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
theorem OperationPtr.setRegions_fieldsInBounds (hnew : ∀ r ∈ newRegions, r.InBounds ctx) :
    ctx.FieldsInBounds → (setRegions op ctx newRegions h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem OperationPtr.pushResult_fieldsInBounds {newResult : OpResult} {op : OperationPtr} h (hres : newResult.FieldsInBounds (op.pushResult ctx newResult h)) :
    ctx.FieldsInBounds → (op.pushResult ctx newResult h).FieldsInBounds := by
  intro hctx
  constructor
  · grind
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
    constructor <;> grind
  · grind

@[grind .]
theorem OperationPtr.setProperties_fieldsInBounds :
    ctx.FieldsInBounds → (setProperties op ctx h newProperties).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem OperationPtr.setOperands_push_fieldsInBounds  (newOperand : OpOperand) (hoperand : newOperand.FieldsInBounds ctx) :
    ctx.FieldsInBounds → (pushOperand op ctx newOperand h).FieldsInBounds := by
  intro hctx
  constructor
  · grind
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
    constructor <;> grind
  · grind

@[grind .]
theorem OperationPtr.pushBlockOperand_push_fieldsInBounds
    (newOperand : BlockOperand) (hoperand : newOperand.FieldsInBounds ctx) :
    ctx.FieldsInBounds → (pushBlockOperand op ctx newOperand h).FieldsInBounds := by
  intro hctx
  constructor
  · grind
  · intro op hop
    constructor
    · intro res hres heq
      constructor <;> grind
    · grind
    · grind
    · grind
    · intro operand hoperand heq
      constructor <;> grind
    · grind
    · intro opr hopr heq
      constructor <;> grind
  · intro block blockIn
    constructor <;> grind
  · grind

attribute [local grind] Operation.empty in
@[grind .]
theorem OperationPtr.allocEmpty_fieldsInBounds (heq : allocEmpty ctx type = some (ctx', ptr')) :
    ctx.FieldsInBounds → ctx'.FieldsInBounds := by
  rintro hctx
  constructor
  · grind
  · intros op hop
    by_cases op = ptr'
    · constructor <;> grind
    · have : op.InBounds ctx := by grind [=> OperationPtr.allocEmpty_genericPtr_iff']
      constructor
      · grind
      · grind
      · grind
      · grind
      · intros operand hoperand heq
        constructor <;> grind
      · grind
      · rintro opr hopr heq
        constructor <;> grind
  · intros bl hbl
    constructor <;> try grind [BlockArgument.FieldsInBounds]
    intros
    constructor
    · grind
    · grind
  · grind

@[grind .]
theorem BlockOperandPtr.setBack_fieldsInBounds {blockOperand ctx h newBack} (hp : newBack.InBounds ctx) :
    ctx.FieldsInBounds → (setBack blockOperand ctx newBack h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem BlockOperandPtr.setOwner_fieldsInBounds {blockOperand ctx h newOwner} (hp : newOwner.InBounds ctx) :
    ctx.FieldsInBounds → (setOwner blockOperand ctx newOwner h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem BlockOperandPtr.setNextUse_fieldsInBounds {blockOperand ctx h newNextUse} (hp : newNextUse.maybe BlockOperandPtr.InBounds ctx) :
    ctx.FieldsInBounds → (setNextUse blockOperand ctx newNextUse h).FieldsInBounds := by
  prove_fieldsInBounds_operation ctx

@[grind .]
theorem BlockOperandPtr.setValue_fieldsInBounds {blockOperand ctx h newValue} (hp : newValue.InBounds ctx) :
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

@[grind .]
theorem BlockPtr.allocEmpty_fieldsInBounds (heq : allocEmpty ctx = some (ctx', ptr')) :
    ctx.FieldsInBounds → ctx'.FieldsInBounds := by
  rintro hctx
  constructor
  · grind
  · intros op hop
    constructor
    · intros
      constructor <;> grind
    · grind
    · grind
    · grind
    · intros operand hoperand heq
      constructor <;> grind
    · grind
    · rintro opr hopr heq
      constructor <;> grind
  · intros bl hbl
    constructor
    case arguments_inBounds =>
      intros
      constructor <;> grind [=> BlockPtr.allocEmpty_genericPtr_iff', Block.empty]
    all_goals grind [=> BlockPtr.allocEmpty_genericPtr_iff', Block.empty]
  · grind

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
  intros hctx
  constructor
  · grind
  · intros
    constructor
    · grind
    · grind
    · grind
    · grind
    · intros
      constructor <;> grind
    · grind
    · intros
      constructor <;> grind
  · intros bl hbl
    constructor
    case arguments_inBounds =>
      intros ba hba heq
      rcases opOperandPtr with _ | val
      · constructor <;> grind
      · cases val <;> grind
    all_goals grind
  · intros
    apply Region.fieldsInBounds_unchanged (ctx := ctx) <;> grind

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
theorem RegionPtr.setParent_fieldsInBounds (hnew : newParent.InBounds ctx) :
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
