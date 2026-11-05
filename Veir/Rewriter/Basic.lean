module

public import Veir.IR.Buffed.AllocateBlock
public import Veir.IR.Buffed.AllocateRegion
public import Veir.IR.Buffed.AllocateOperation
public import Veir.Rewriter.EraseContainers

public import ExArray.CompilerExtras
public import Veir.IR
public import Veir.Rewriter.InsertPoint
public import Veir.Rewriter.LinkedList.Basic
public import Veir.Rewriter.LinkedList.GetSet
public import Veir.Rewriter.RewriterPushOperand
public import Veir.Rewriter.RewriterPushBlockOperand
public import Veir.Rewriter.RewriterPushResult
public import Veir.Rewriter.RewriterPushBlockArgument
public import Veir.Rewriter.RewriterPushRegion

meta import Veir.IR.Buffed.Basic
import Veir.IR.Buffed.RawAccessorsLemmas
import Veir.IR.Buffed.Meta
import Veir.IR.Buffed.InBounds
import Veir.Rewriter.LinkedList.LayoutUnchanged

set_option linter.unusedSectionVars false

@[expose] public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]
variable {ctx : Sim.IRContext OpInfo}

-- TODO: Sim.InsertPoint

-- FIXME: the grindset approach should work, but it does not work...

local grind_pattern Sim.OperationPtr.inBounds_of_optionPtr_inBounds =>
  ptr.InBounds ctx, optr.toOption, some ptr
local grind_pattern Sim.BlockPtr.inBounds_of_optionPtr_inBounds =>
  ptr.InBounds ctx, optr.toOption, some ptr
local grind_pattern Sim.BlockArgumentPtr.inBounds_of_optionPtr_inBounds =>
  ptr.InBounds ctx, optr.toOption, some ptr
local grind_pattern Sim.BlockOperandPtr.inBounds_of_optionPtr_inBounds =>
  ptr.InBounds ctx, optr.toOption, some ptr
local grind_pattern Sim.RegionPtr.inBounds_of_optionPtr_inBounds =>
  ptr.InBounds ctx, optr.toOption, some ptr
local grind_pattern Sim.OpOperandPtr.inBounds_of_optionPtr_inBounds =>
  ptr.InBounds ctx, optr.toOption, some ptr
local grind_pattern Sim.OpResultPtr.inBounds_of_optionPtr_inBounds =>
  ptr.InBounds ctx, optr.toOption, some ptr
local grind_pattern Sim.ValuePtr.inBounds_of_optionPtr_inBounds =>
  ptr.InBounds ctx, optr.toOption, some ptr

/-- Insert an operation at a given location. -/
buffed (inline := true)
def Rewriter.insertOp?Sim (ctx: Sim.IRContext OpInfo) (newOp: Sim.OperationPtr) (insertionPoint: InsertPoint)
    (newOpIn: newOp.InBounds ctx := by grind)
    (insIn : insertionPoint.InBounds ctx.spec := by grind)
    (ctxInBounds: ctx.spec.FieldsInBounds := by grind)
    (insRepr : insertionPoint.IsRepr := by grind) : Option (Sim.IRContext OpInfo) :=
    rlet parent ← (insertionPoint.block ctx).toOption
    let prev := insertionPoint.prev ctx (by grind)
    let next := insertionPoint.next
    newOp.linkBetweenWithParent ctx prev next parent (by grind) (by grind) (by grind) (by grind)

@[grind .]
theorem Rewriter.insertOp?_layoutUnchanged
    (heq : insertOp? ctx newOp ip h₁ h₂ h₃ h₄ = some newCtx) :
    newCtx.spec.LayoutUnchanged ctx.spec := by
  simp only [insertOp?.unfold] at heq
  grind

theorem Rewriter.insertOp?_inBounds_mono (ptr : Sim.GenericPtr)
    (heq : insertOp? ctx newOp ip h₁ h₂ h₃ h₄ = some newCtx) :
    ptr.InBounds newCtx ↔ ptr.InBounds ctx := by
  simp only [insertOp?.unfold] at heq
  grind

grind_pattern Rewriter.insertOp?_inBounds_mono =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, ptr.InBounds newCtx

theorem Rewriter.insertOp?_inBounds_veir_mono (ptr : Veir.GenericPtr)
    (heq : insertOp? ctx newOp ip h₁ h₂ h₃ h₄ = some newCtx) :
    ptr.InBounds newCtx.spec ↔ ptr.InBounds ctx.spec := by
  simp only [insertOp?.unfold] at heq
  grind

grind_pattern Rewriter.insertOp?_inBounds_veir_mono =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, ptr.InBounds newCtx.spec

theorem Rewriter.insertOp?_sim_inBounds_mono (ptr : Sim.GenericPtr)
    (heq : insertOp? ctx newOp ip h₁ h₂ h₃ h₄ = some newCtx) :
    ptr.InBounds newCtx ↔ ptr.InBounds ctx := by
  simp only [insertOp?.unfold] at heq
  grind

grind_pattern Rewriter.insertOp?_sim_inBounds_mono =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, ptr.InBounds newCtx

set_option linter.unusedVariables false in -- spurious
@[grind .]
theorem Rewriter.insertOp?_fieldsInBounds_mono
    (heq : insertOp? ctx newOp ip h₁ h₂ h₃ h₄ = some newCtx) :
    ctx.spec.FieldsInBounds → newCtx.spec.FieldsInBounds := by
  simp only [insertOp?.unfold] at heq
  grind

/-- Set the parent, previous, and next operation pointers of an operation to `none`. -/
buffed (inline := true)
def Rewriter.unsetParentAndNeighborsSim (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr) (hIn : op.InBounds ctx) :=
  let ctx := op.setParent ctx .none (by grind) (by grind)
  let ctx := op.setPrevOp ctx .none (by grind) (by grind)
  op.setNextOp ctx .none (by grind) (by grind)

@[grind =]
theorem Rewriter.unsetParentAndNeighbors_inBounds (ptr : Sim.GenericPtr) :
    ptr.InBounds (unsetParentAndNeighbors ctx op hIn) ↔ ptr.InBounds ctx := by
  simp only [unsetParentAndNeighbors.unfold]
  grind

@[grind . ]
theorem Rewriter.unsetParentAndNeighbors_fieldsInBounds :
    (unsetParentAndNeighbors ctx op hIn).spec.FieldsInBounds := by
  simp only [unsetParentAndNeighbors.unfold]
  grind

buffed (inline := true)
def Rewriter.detachOpSim (ctx: Sim.IRContext OpInfo) (op: Sim.OperationPtr) (hctx : ctx.spec.FieldsInBounds)
    (hIn : op.InBounds ctx) (hasParent: (op.getParent ctx hIn).toOption.isSome) : Sim.IRContext OpInfo :=
  let prevOp := op.getPrevOp ctx (by grind)
  let nextOp := op.getNextOp ctx (by grind)
  let parent := (op.getParent ctx (by grind)).toOption.get hasParent
  let ctx := unsetParentAndNeighbors ctx op hIn
  have : parent.InBounds ctx := by grind [generic_ptr_grind]
  -- I had to duplicate the continuation in each branch, I don't really know why the proofs of the preconditions in, say, `setNextOp` were metavariable... maybe somehow the execution of the tactics is slightly delayed?
  match _ : prevOp.toOption with
    | some prevOp =>
      let ctx := prevOp.setNextOp ctx nextOp (by grind [generic_ptr_grind]) (by
        have : (∀ ptr, nextOp.toOption = some ptr → ptr.InBounds ctx) → nextOp.InBounds ctx := by grind
        grind [generic_ptr_grind])
      match _ : nextOp.toOption with
      | some nextOp => nextOp.setPrevOp ctx prevOp.toO (by grind) (by grind)
      | none => parent.setLastOp ctx prevOp.toO (by grind [generic_ptr_grind]) (by grind)
    | none =>
      let ctx := parent.setFirstOp ctx nextOp (by grind [generic_ptr_grind]) (by
        have : (∀ ptr, nextOp.toOption = some ptr → ptr.InBounds ctx) → nextOp.InBounds ctx := by
          cases h : nextOp.spec <;> grind [Option.get!]
        grind [generic_ptr_grind])
      match _ : nextOp.toOption with
      | some nextOp => nextOp.setPrevOp ctx prevOp (by grind) (by grind)
      | none => parent.setLastOp ctx prevOp (by grind) (by grind)

@[grind .]
theorem Rewriter.detachOp_inBounds (ptr : Sim.GenericPtr) :
    ptr.InBounds (detachOp ctx hctx op hIn hasParent) ↔ ptr.InBounds ctx := by
  grind (gen := 20) [detachOp.unfold]

@[grind .]
theorem Rewriter.detachOp_fieldsInBounds (hctx : ctx.spec.FieldsInBounds) :
    (detachOp ctx op hctx hIn hasParent).spec.FieldsInBounds := by
  grind [detachOp.unfold]

@[grind =]
theorem Rewriter.detachOp_preserves_numOperands (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    op'.getNumOperands! (detachOp ctx op hctx hIn hPar).spec = op'.getNumOperands! ctx.spec := by
  simp [detachOp.unfold]
  split <;> grind [unsetParentAndNeighbors.unfold]

@[grind =]
theorem Rewriter.detachOp_preserves_capOperands (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    (op'.get! (detachOp ctx op hctx hIn hPar).spec).capOperands = (op'.get! ctx.spec).capOperands := by
  simp [detachOp.unfold]
  split <;> grind (instances := 2000) [unsetParentAndNeighbors.unfold]

@[grind =]
theorem Rewriter.detachOp_preserves_numSuccessors (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    op'.getNumSuccessors! (detachOp ctx op hctx hIn hPar).spec = op'.getNumSuccessors! ctx.spec := by
  simp [detachOp.unfold]
  split <;> grind [unsetParentAndNeighbors.unfold]

@[grind =]
theorem Rewriter.detachOp_preserves_capBlockOperands (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    (op'.get! (detachOp ctx op hctx hIn hPar).spec).capBlockOperands = (op'.get! ctx.spec).capBlockOperands := by
  simp [detachOp.unfold]
  split <;> grind (instances := 2000) [unsetParentAndNeighbors.unfold]

/-- Detach an operation from its parent if it has one. -/
buffed (inline := true)
def Rewriter.detachOpIfAttachedSim (ctx: Sim.IRContext OpInfo) (op: Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds := by grind)
    (hop : op.InBounds ctx := by grind) : Sim.IRContext OpInfo :=
  match h: (op.getParent ctx hop).toOption with
  | some _ => Rewriter.detachOp ctx op hctx hop (by grind)
  | none => ctx

@[grind .]
theorem Rewriter.detachOpIfAttached_inBounds (ptr : Sim.GenericPtr) :
    ptr.InBounds (detachOpIfAttached ctx op h₁ h₂) ↔ ptr.InBounds ctx := by
  grind [detachOpIfAttached.unfold]

@[grind .]
theorem Rewriter.detachOpIfAttached_fieldsInBounds (hctx : ctx.spec.FieldsInBounds) :
    (detachOpIfAttached ctx op hctx hIn).spec.FieldsInBounds := by
  grind [detachOpIfAttached.unfold]

@[simp, grind =]
theorem Rewriter.detachOpIfAttached_preserves_numOperands (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    op'.getNumOperands! (detachOpIfAttached ctx op hctx hIn).spec = op'.getNumOperands! ctx.spec := by
  grind [detachOpIfAttached.unfold]

@[simp, grind =]
theorem Rewriter.detachOpIfAttached_preserves_capOperands (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    (op'.get! (detachOpIfAttached ctx op hctx hIn).spec).capOperands = (op'.get! ctx.spec).capOperands := by
  grind [detachOpIfAttached.unfold]

@[simp, grind =]
theorem Rewriter.detachOpIfAttached_preserves_numSuccessors (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    op'.getNumSuccessors! (detachOpIfAttached ctx op hctx hIn).spec = op'.getNumSuccessors! ctx.spec := by
  grind [detachOpIfAttached.unfold]

@[simp, grind =]
theorem Rewriter.detachOpIfAttached_preserves_capBlockOperands (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    (op'.get! (detachOpIfAttached ctx op hctx hIn).spec).capBlockOperands = (op'.get! ctx.spec).capBlockOperands := by
  grind [detachOpIfAttached.unfold]

buffed (inline := true)
def Rewriter.detachOperands.loopSim (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr) (off : Int64) (index : UInt64)
    (hCtx : ctx.spec.FieldsInBounds := by grind)
    (hOp : op.InBounds ctx := by grind)
    (hIndex : index.toNat < op.spec.getNumOperands! ctx.spec := by grind)
    -- `off` is the hoisted operands base offset: computing it per iteration via `getOperandPtr`
    -- costs a boxed `propertySizeOfEncoded` dispatch (two heap allocations) per operand.
    (hoff : off = Buffed.Operation.Offsets.operands op.spec ctx.spec := by grind) : Sim.IRContext OpInfo :=
  let ctx' := (op.getOperandPtrAt ctx off index (by grind) (by grind)).removeFromCurrent ctx (by grind) (by grind)
  if hz : index = 0 then ctx' else
  Rewriter.detachOperands.loopSim ctx' op off (index-1) (by grind) (by grind) (by grind)
    (by grind [Buffed.Operation.Offsets.operands_layoutPreserved])
termination_by index.toNat
decreasing_by
  · have := @UInt64.toNat_inj index 0
    grind

@[grind .]
theorem Rewriter.detachOperands.loop_inBounds (ptr : Sim.GenericPtr) :
    ptr.InBounds (detachOperands.loop ctx op off index hCtx hOp hIndex hoff) ↔ ptr.InBounds ctx := by
  simp only [loop.eq_sim] at *
  fun_induction loopSim <;> grind

@[grind .]
theorem Rewriter.detachOperands.loop_fieldsInBounds :
    ctx.spec.FieldsInBounds → (detachOperands.loop ctx op off index hCtx hOp hIndex hoff).spec.FieldsInBounds := by
  simp only [loop.eq_sim] at *
  fun_induction loopSim <;> grind

@[simp, grind =]
theorem Rewriter.detachOperands.loop_preserves_numSuccessors (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    op'.getNumSuccessors! (detachOperands.loop ctx op off idx hctx hOp hIndex hoff).spec = op'.getNumSuccessors! ctx.spec := by
  simp only [loop.eq_sim] at *
  fun_induction loopSim <;> grind

@[simp, grind =]
theorem Rewriter.detachOperands.loop_preserves_capSuccessors (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    (op'.get! (detachOperands.loop ctx op off idx hctx hOp hIndex hoff).spec).capBlockOperands = (op'.get! ctx.spec).capBlockOperands := by
  simp only [loop.eq_sim] at *
  fun_induction loopSim <;> grind

buffed (inline := true)
def Rewriter.detachOperandsSim (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hCtx : ctx.spec.FieldsInBounds := by grind)
    (hOp : op.InBounds ctx := by grind)
    (hcap : (op.spec.get! ctx.spec).capOperands = op.spec.getNumOperands! ctx.spec) : Sim.IRContext OpInfo :=
  let numOperands := op.getNumOperands ctx (by grind)
  if hz : numOperands = 0 then
    ctx
  else
    Rewriter.detachOperands.loop ctx op (op.getOperandsOffset ctx (by grind)) (numOperands - 1) (by grind) (by grind)
    (by grind [ UInt64.toNat_mod_size, UInt64.toNat_sub, UInt64.le_iff_toNat_le,
    UInt64.toNat_ofNat, UInt64.toNat_ofNat_of_lt, UInt64.toNat_lt])
    (by grind)

@[grind .]
theorem Rewriter.detachOperands_inBounds (ptr : Sim.GenericPtr) :
    ptr.InBounds (detachOperands ctx op hCtx hOp hCap) ↔ ptr.InBounds ctx := by
  grind [detachOperands.unfold]

@[grind .]
theorem Rewriter.detachOperands_fieldsInBounds :
    ctx.spec.FieldsInBounds → (detachOperands ctx op hCtx hOp hCap).spec.FieldsInBounds := by
  grind [detachOperands.unfold]

@[simp, grind =]
theorem Rewriter.detachOperands_preserves_numSuccessors
    (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    op'.getNumSuccessors! (detachOperands ctx op hctx hOp hCap).spec =
      op'.getNumSuccessors! ctx.spec := by
  simp [detachOperands.unfold]
  split <;> grind

@[simp, grind =]
theorem Rewriter.detachOperands_preserves_capSuccessors
    (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    (op'.get! (detachOperands ctx op hctx hOp hCap).spec).capBlockOperands =
      (op'.get! ctx.spec).capBlockOperands := by
  simp [detachOperands.unfold]
  split <;> grind

buffed (inline := true)
def Rewriter.detachBlockOperands.loopSim (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr) (index : UInt64)
    (hCtx : ctx.spec.FieldsInBounds := by grind)
    (hOp : op.InBounds ctx := by grind)
    (hIndex : index.toNat < op.spec.getNumSuccessors! ctx.spec := by grind) : Sim.IRContext OpInfo :=
  let ctx' := (op.getBlockOperandPtr ctx index (by grind)).removeFromCurrent ctx (by grind)
  if hz : index = 0 then ctx' else
  Rewriter.detachBlockOperands.loopSim ctx' op (index - 1) (by grind) (by grind) (by grind)
termination_by index.toNat
decreasing_by grind [UInt64.toNat_mod_size, UInt64.toNat_sub, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat, UInt64.toNat_inj]

@[grind .]
theorem Rewriter.detachBlockOperands.loop_inBounds (ptr : Sim.GenericPtr) :
    ptr.InBounds (detachBlockOperands.loop ctx op index hCtx hOp hIndex) ↔ ptr.InBounds ctx := by
  simp only [loop.eq_sim] at *
  fun_induction loopSim <;> grind

@[grind .]
theorem Rewriter.detachBlockOperands.loop_fieldsInBounds :
    ctx.spec.FieldsInBounds → (detachBlockOperands.loop ctx op index hCtx hOp hIndex).spec.FieldsInBounds := by
  simp only [loop.eq_sim] at *
  fun_induction loopSim <;> grind

buffed (inline := true)
def Rewriter.detachBlockOperandsSim (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hCtx : ctx.spec.FieldsInBounds := by grind)
    (hOp : op.InBounds ctx := by grind)
    (hcap : (op.spec.get! ctx.spec).capBlockOperands = op.spec.getNumSuccessors! ctx.spec) : Sim.IRContext OpInfo :=
  let numOperands := op.getNumSuccessors ctx (by grind)
  if h : numOperands = 0 then
    ctx
  else
    Rewriter.detachBlockOperands.loop ctx op (numOperands - 1) (by grind) (by grind) (by
      grind [UInt64.toNat_mod_size, UInt64.toNat_sub, UInt64.le_iff_toNat_le,
      UInt64.toNat_ofNat, UInt64.toNat_ofNat_of_lt, UInt64.toNat_lt])

@[grind .]
theorem Rewriter.detachBlockOperands_inBounds (ptr : Sim.GenericPtr) :
    ptr.InBounds (detachBlockOperands ctx op hCtx hOp hCap) ↔ ptr.InBounds ctx := by
  grind [detachBlockOperands.unfold]

@[grind .]
theorem Rewriter.detachBlockOperands_fieldsInBounds :
    ctx.spec.FieldsInBounds → (detachBlockOperands ctx op hCtx hOp hCap).spec.FieldsInBounds := by
  grind [detachBlockOperands.unfold]

/-- Proof-only side condition needed to pair `eraseOp`'s unchanged byte buffer with the
specification context in which the erased operation has been deallocated. -/
def Rewriter.EraseOpDeallocFieldsInBounds (ctx : Sim.IRContext OpInfo)
    (op : Sim.OperationPtr) : Prop :=
  ∀ (hCtx : ctx.spec.FieldsInBounds) (hOp : op.InBounds ctx)
    (hOpers : (op.spec.get! ctx.spec).capOperands = op.spec.getNumOperands! ctx.spec)
    (hBlOpers : (op.spec.get! ctx.spec).capBlockOperands = op.spec.getNumSuccessors! ctx.spec),
    let ctx := Rewriter.detachOpIfAttached ctx op
    let ctx := Rewriter.detachOperands ctx op (by grind) (by grind [generic_ptr_grind]) (by grind)
    let ctx := Rewriter.detachBlockOperands ctx op (by grind) (by grind [generic_ptr_grind])
      (by grind [detachOperands.unfold])
    ∀ hOpAfter : op.InBounds ctx,
      (op.spec.dealloc ctx.spec hOpAfter.ib).FieldsInBounds

buffed (inline := false)
def Rewriter.eraseOpSim (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hCtx : ctx.spec.FieldsInBounds := by grind)
    (hOp : op.InBounds ctx := by grind)
    (hOpers : (op.spec.get! ctx.spec).capOperands = op.spec.getNumOperands! ctx.spec)
    (hBlOpers : (op.spec.get! ctx.spec).capBlockOperands = op.spec.getNumSuccessors! ctx.spec)
    (hDealloc : Rewriter.EraseOpDeallocFieldsInBounds ctx op := by grind) : Sim.IRContext OpInfo :=
  let ctx := Rewriter.detachOpIfAttached ctx op
  let ctx := Rewriter.detachOperands ctx op (by grind) (by grind [generic_ptr_grind]) (by grind)
  let ctx := Rewriter.detachBlockOperands ctx op (by grind) (by grind [generic_ptr_grind]) (by grind [detachOperands.unfold])
  have hOpAfter : op.InBounds ctx := by
    apply (Sim.GenericPtr.iff_operation op).mp
    rw [Rewriter.detachBlockOperands_inBounds]
    rw [Rewriter.detachOperands_inBounds]
    rw [Rewriter.detachOpIfAttached_inBounds]
    exact (Sim.GenericPtr.iff_operation op).mpr hOp
  op.dealloc ctx hOpAfter (hDealloc hCtx hOp hOpers hBlOpers hOpAfter)

/- Remark: the fact that `eraseOpSim` preserves `FieldsInBounds` relies on the fact that the context is well formed. -/

/-- Insert a block at a given location. -/
buffed (inline := true)
def Rewriter.insertBlock?Sim (ctx: Sim.IRContext OpInfo) (newBlock: Sim.BlockPtr)
    (insertionPoint: BlockInsertPoint)
    (newBlockIn: newBlock.InBounds ctx := by grind)
    (insIn : insertionPoint.InBounds ctx.spec := by grind)
    (insRepr : insertionPoint.IsRepr := by grind)
    (ctxInBounds: ctx.spec.FieldsInBounds := by grind) : Option (Sim.IRContext OpInfo) :=
    rlet parent ← (insertionPoint.region ctx insIn insRepr).toOption
    let prev := insertionPoint.prev ctx (by grind)
    let next := insertionPoint.next
    newBlock.linkBetweenWithParent ctx prev next parent (by grind) (by grind) (by grind) (by grind)

@[grind .]
theorem Rewriter.insertBlock?_inBounds (ptr : Sim.GenericPtr)
    (heq : insertBlock? ctx newBlock ip h₁ h₂ h₃ h₄ = some newCtx) :
    ptr.InBounds ctx ↔ ptr.InBounds newCtx := by
  simp only [insertBlock?.unfold] at heq
  grind

set_option linter.unusedVariables false in -- bug
@[grind .]
theorem Rewriter.insertBlock?_fieldsInBounds_mono
    (heq : insertBlock? ctx newBlock ip h₁ h₂ h₃ h₄ = some newCtx) :
    ctx.spec.FieldsInBounds → newCtx.spec.FieldsInBounds := by
  simp only [insertBlock?.unfold] at heq
  grind

buffed (inline := true)
def Rewriter.replaceUseSim (ctx: Sim.IRContext OpInfo) (use : Sim.OpOperandPtr) (newValue: Sim.ValuePtr)
    (useIn: use.InBounds ctx := by grind [generic_ptr_grind])
    (newIn: newValue.InBounds ctx := by grind [generic_ptr_grind])
    (ctxIn: ctx.spec.FieldsInBounds := by grind [generic_ptr_grind]) : Sim.IRContext OpInfo :=
  if (use.getValue ctx (by grind)).impl = newValue.impl then
    ctx
  else
    let ctx := use.removeFromCurrent ctx (by grind) (by grind)
    let ctx := use.setValue ctx newValue (by grind [generic_ptr_grind]) (by grind [generic_ptr_grind])
    let ctx := use.insertIntoCurrent ctx (by grind) (by grind)
    ctx

@[grind =]
theorem Rewriter.replaceUse_inBounds (ptr : Sim.GenericPtr) :
    ptr.InBounds (replaceUse ctx use newValue useIn newIn ctxIn) ↔ ptr.InBounds ctx := by
  grind [replaceUse.unfold]

@[grind .]
theorem Rewriter.replaceUse_fieldsInBounds :
     ctx.spec.FieldsInBounds → (replaceUse ctx use newValue useIn newIn ctxIn).spec.FieldsInBounds := by
  grind [replaceUse.unfold]

buffed (inline := false)
def Rewriter.replaceValue?Sim (ctx: Sim.IRContext OpInfo) (oldValue: Sim.ValuePtr) (newValue: Sim.ValuePtr)
    (oldIn : oldValue.InBounds ctx := by grind [generic_ptr_grind])
    (newIn : newValue.InBounds ctx := by grind [generic_ptr_grind])
    (ctxIn : ctx.spec.FieldsInBounds := by grind)
    (depth : UInt64 := 1_000_000) : Option (Sim.IRContext OpInfo) :=
  if depth = 0 then none else
    let depth := depth - 1
    match _ : (oldValue.getFirstUse ctx (by grind)).toOption with
    | none => some ctx
    | some firstUse =>
    let ctx := Rewriter.replaceUse ctx firstUse newValue
    Rewriter.replaceValue?Sim ctx oldValue newValue (by grind [generic_ptr_grind]) (by grind [generic_ptr_grind]) (by grind) depth
termination_by depth.toNat
decreasing_by
  grind [UInt64.toNat_mod_size, UInt64.toNat_sub, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat, UInt64.toNat_inj]

@[grind .]
theorem Rewriter.replaceValue?_veir_inBounds (ptr : Veir.GenericPtr) :
    replaceValue? ctx old new h₁ h₂ h₃ d = some ctx' →
    (ptr.InBounds ctx.spec ↔ ptr.InBounds ctx'.spec) := by
  simp only [replaceValue?.eq_sim] at *
  fun_induction replaceValue?Sim <;> grind [replaceUse.unfold]

@[grind =>]
theorem Rewriter.replaceValue?_inBounds (ptr : Sim.GenericPtr) :
    replaceValue? ctx old new h₁ h₂ h₃ d = some ctx' →
    (ptr.InBounds ctx ↔ ptr.InBounds ctx') := by
  simp only [replaceValue?.eq_sim] at *
  fun_induction replaceValue?Sim <;> grind

@[grind .]
theorem Rewriter.replaceValue?_fieldsInBounds :
     ctx.spec.FieldsInBounds → (replaceValue? ctx old new h₁ h₂ h₃ d).maybe₁ (·.spec.FieldsInBounds) := by
  simp only [replaceValue?.eq_sim] at *
  fun_induction replaceValue?Sim <;> grind

@[grind .]
theorem Rewriter.replaceValue?_preserves_results_size (op : Sim.OperationPtr) (hop : op.InBounds ctx) :
    replaceValue? ctx old new h₁ h₂ h₃ d = some ctx' →
    op.spec.getNumResults! ctx'.spec = op.spec.getNumResults! ctx.spec := by
  simp only [replaceValue?.eq_sim] at *
  fun_induction replaceValue?Sim <;> grind [Rewriter.replaceUse.unfold]

@[grind .]
theorem Rewriter.replaceValue?_preserves_parent' (op : Sim.OperationPtr) (hop : op.InBounds ctx)
    (hctx' : replaceValue? ctx old new h₁ h₂ h₃ d = some ctx') :
    (op.spec.get! ctx'.spec).parent = (op.spec.get! ctx.spec).parent := by
  simp only [replaceValue?.eq_sim] at *
  fun_induction replaceValue?Sim <;> grind [Rewriter.replaceUse.unfold]

@[grind .]
theorem Rewriter.replaceValue?_preserves_parent (op : Sim.OperationPtr) (hop : op.InBounds ctx)
    (hctx' : replaceValue? ctx old new h₁ h₂ h₃ d = some ctx') :
    (op.spec.get! ctx'.spec).parent = (op.spec.get! ctx.spec).parent := by
  simp only [replaceValue?.eq_sim] at *
  fun_induction replaceValue?Sim <;> grind [Rewriter.replaceUse.unfold]

@[grind .]
theorem Rewriter.replaceValue?_preserves_numOperands (op : Sim.OperationPtr) (hop : op.InBounds ctx) :
    replaceValue? ctx old new h₁ h₂ h₃ d = some ctx' →
    op.spec.getNumOperands! ctx'.spec = op.spec.getNumOperands! ctx.spec := by
  simp only [replaceValue?.eq_sim] at *
  fun_induction replaceValue?Sim <;> grind [Rewriter.replaceUse.unfold]

@[grind .]
theorem Rewriter.replaceValue?_preserves_capOperands (op : Sim.OperationPtr) (hop : op.InBounds ctx) :
    replaceValue? ctx old new h₁ h₂ h₃ d = some ctx' →
    (op.spec.get! ctx'.spec).capOperands = (op.spec.get! ctx.spec).capOperands := by
  simp only [replaceValue?.eq_sim] at *
  fun_induction replaceValue?Sim <;> grind [Rewriter.replaceUse.unfold]

@[grind .]
theorem Rewriter.replaceValue?_preserves_numSuccessors (op : Sim.OperationPtr) (hop : op.InBounds ctx) :
    replaceValue? ctx old new h₁ h₂ h₃ d = some ctx' →
    op.spec.getNumSuccessors! ctx'.spec = op.spec.getNumSuccessors! ctx.spec := by
  simp only [replaceValue?.eq_sim] at *
  fun_induction replaceValue?Sim <;> grind [Rewriter.replaceUse.unfold]

@[grind .]
theorem Rewriter.replaceValue?_preserves_capBlockOperands (op : Sim.OperationPtr) (hop : op.InBounds ctx) :
    replaceValue? ctx old new h₁ h₂ h₃ d = some ctx' →
    (op.spec.get! ctx'.spec).capBlockOperands = (op.spec.get! ctx.spec).capBlockOperands := by
  simp only [replaceValue?.eq_sim] at *
  fun_induction replaceValue?Sim <;> grind [Rewriter.replaceUse.unfold]

buffed (inline := true)
def Rewriter.replaceOpResultsSim (ctx: Sim.IRContext OpInfo) (fromOp toOp : Sim.OperationPtr)
    (index : UInt64)
    (fromOpIB : fromOp.InBounds ctx := by grind) (toOpIB : toOp.InBounds ctx := by grind)
    (hNumFrom : index.toNat ≤ fromOp.spec.getNumResults! ctx.spec := by grind)
    (hNumTo : index.toNat ≤ toOp.spec.getNumResults! ctx.spec := by grind)
    (ctxInBounds : ctx.spec.FieldsInBounds := by grind) : Option (Sim.IRContext OpInfo) := do
  if _ : index = 0 then ctx else
  let index := index - 1
  let oldResult := fromOp.getResultPtr ctx index (by grind)
  let newResult := toOp.getResultPtr ctx index (by grind)
  rlet ctx ← Rewriter.replaceValue? ctx (.fromOpResultPtr oldResult) (.fromOpResultPtr newResult)
     (by grind [UInt64.toNat_mod_size, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat, UInt64.toNat_inj])
     (by grind [UInt64.toNat_mod_size, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat, UInt64.toNat_inj])
     (by grind)
  replaceOpResultsSim ctx fromOp toOp index (by grind [generic_ptr_grind]) (by grind [generic_ptr_grind])
    (by simp -failIfUnchanged at *; subst index; rw [Rewriter.replaceValue?_preserves_results_size _ _ (by assumption)] <;> grind)
    (by simp -failIfUnchanged at *; subst index; rw [Rewriter.replaceValue?_preserves_results_size _ _ (by assumption)] <;> grind)
    (by grind [generic_ptr_grind])
termination_by index.toNat
decreasing_by
  grind [UInt64.toNat_mod_size, UInt64.toNat_sub, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat, UInt64.toNat_inj]

theorem Rewriter.replaceOpResults_inBounds {ptr : Sim.GenericPtr} :
    replaceOpResults ctx fromOp toOp index fromOpIB toOpIB hNumFrom hNumTo ctxInBounds = some newCtx →
    (ptr.InBounds ctx ↔ ptr.InBounds newCtx) := by
  simp only [replaceOpResults.eq_sim] at *
  fun_induction replaceOpResultsSim <;> grind [Rewriter.replaceUse.unfold]

grind_pattern Rewriter.replaceOpResults_inBounds =>
  Rewriter.replaceOpResults ctx fromOp toOp index fromOpIB toOpIB hNumFrom hNumTo ctxInBounds,
  some newCtx, ptr.InBounds ctx
grind_pattern Rewriter.replaceOpResults_inBounds =>
  Rewriter.replaceOpResults ctx fromOp toOp index fromOpIB toOpIB hNumFrom hNumTo ctxInBounds,
  some newCtx, ptr.InBounds newCtx

@[grind <=]
theorem Rewriter.replaceOpResults_fieldsInBounds :
    replaceOpResults ctx fromOp toOp index fromOpIB toOpIB hNumFrom hNumTo ctxInBounds = some newCtx →
    newCtx.spec.FieldsInBounds := by
  simp only [replaceOpResults.eq_sim] at *
  fun_induction replaceOpResultsSim <;> grind [Rewriter.replaceUse.unfold]

@[grind .]
theorem Rewriter.replaceOpResults_preserves_numOperands (op : Sim.OperationPtr) (hop : op.InBounds ctx) :
    replaceOpResults ctx fromOp toOp index fromOpIB toOpIB hNumFrom hNumTo ctxInBounds = some newCtx →
    op.spec.getNumOperands! newCtx.spec = op.spec.getNumOperands! ctx.spec := by
  simp only [replaceOpResults.eq_sim] at *
  fun_induction replaceOpResultsSim <;> grind [generic_ptr_grind]

@[grind .]
theorem Rewriter.replaceOpResults_preserves_capOperands (op : Sim.OperationPtr) (hop : op.InBounds ctx) :
    replaceOpResults ctx fromOp toOp index fromOpIB toOpIB hNumFrom hNumTo ctxInBounds = some newCtx →
    (op.spec.get! newCtx.spec).capOperands = (op.spec.get! ctx.spec).capOperands := by
  simp only [replaceOpResults.eq_sim] at *
  fun_induction replaceOpResultsSim <;> grind [generic_ptr_grind]

@[grind .]
theorem Rewriter.replaceOpResults_preserves_numSuccessors (op : Sim.OperationPtr) (hop : op.InBounds ctx) :
    replaceOpResults ctx fromOp toOp index fromOpIB toOpIB hNumFrom hNumTo ctxInBounds = some newCtx →
    op.spec.getNumSuccessors! newCtx.spec = op.spec.getNumSuccessors! ctx.spec := by
  simp only [replaceOpResults.eq_sim] at *
  fun_induction replaceOpResultsSim <;> grind [generic_ptr_grind]

@[grind .]
theorem Rewriter.replaceOpResults_preserves_capBlockOperands (op : Sim.OperationPtr) (hop : op.InBounds ctx) :
    replaceOpResults ctx fromOp toOp index fromOpIB toOpIB hNumFrom hNumTo ctxInBounds = some newCtx →
    (op.spec.get! newCtx.spec).capBlockOperands = (op.spec.get! ctx.spec).capBlockOperands := by
  simp only [replaceOpResults.eq_sim] at *
  fun_induction replaceOpResultsSim <;> grind [generic_ptr_grind]

buffed (inline := true)
def Rewriter.replaceOp?Sim (ctx: Sim.IRContext OpInfo) (oldOp newOp: Sim.OperationPtr)
    (oldIn: oldOp.InBounds ctx := by grind)
    (newIn: newOp.InBounds ctx := by grind)
    (ctxIn: ctx.spec.WellFormed := by grind)
    (_hpar : (oldOp.spec.get! ctx.spec).parent.isSome = true)
    (wf : ctx.spec.WellFormed)
    (hErase : ∀ (index : UInt64)
      (hNumFrom : index.toNat ≤ oldOp.spec.getNumResults! ctx.spec)
      (hNumTo : index.toNat ≤ newOp.spec.getNumResults! ctx.spec)
      (ctxInBounds : ctx.spec.FieldsInBounds) (newCtx : Sim.IRContext OpInfo),
      index.toNat = oldOp.spec.getNumResults! ctx.spec →
      Rewriter.replaceOpResults ctx oldOp newOp index oldIn newIn hNumFrom hNumTo
        ctxInBounds = some newCtx →
      Rewriter.EraseOpDeallocFieldsInBounds newCtx oldOp := by grind) : Option (Sim.IRContext OpInfo) := do
  let numOldResults := oldOp.getNumResults ctx (by grind)
  let numNewResults := newOp.getNumResults ctx (by grind)
  if h : numOldResults ≠ numNewResults then
    none
  else
    rlet hreplace : newCtx ← replaceOpResults ctx oldOp newOp numOldResults (by grind) (by grind) (by grind [
      UInt64.toNat_mod_size, UInt64.toNat_ofNat, UInt64.toNat_ofNat_of_lt, UInt64.toNat_lt]) (by grind [
        UInt64.toNat_mod_size, UInt64.toNat_ofNat, UInt64.toNat_ofNat_of_lt, UInt64.toNat_lt]) (by grind)
    have hNumOld : numOldResults.toNat = oldOp.spec.getNumResults! ctx.spec := by
      have oldWf := wf.operations oldOp.spec oldIn.ib
      have henc := ctx.sim.encoding_op oldOp.spec oldIn.ib
      have hNumResultsLt : oldOp.spec.getNumResults! ctx.spec < UInt64.size := by
        rw [← oldWf.capResults_eq_numResults, henc.numResults]
        exact UInt64.toNat_lt _
      dsimp [numOldResults]
      rw [Sim.OperationPtr.getNumResults_eq_getNumResults! ctx oldOp oldIn,
        Sim.OperationPtr.getNumResults!_spec_of_wf ctx oldOp (ib := oldIn) wf]
      exact UInt64.toNat_ofNat_of_lt hNumResultsLt
    eraseOp newCtx oldOp (by grind) (by grind [generic_ptr_grind]) (by
      have := wf.operations oldOp.spec
      have := replaceOpResults_preserves_capOperands oldOp (by grind) hreplace
      have := replaceOpResults_preserves_numOperands oldOp (by grind) hreplace
      grind) (by
      have := wf.operations oldOp.spec
      have := replaceOpResults_preserves_capBlockOperands oldOp (by grind) hreplace
      have := replaceOpResults_preserves_numSuccessors oldOp (by grind) hreplace
      grind) (hErase numOldResults (by grind [
        UInt64.toNat_mod_size, UInt64.toNat_ofNat, UInt64.toNat_ofNat_of_lt, UInt64.toNat_lt]) (by grind [
        UInt64.toNat_mod_size, UInt64.toNat_ofNat, UInt64.toNat_ofNat_of_lt, UInt64.toNat_lt]) (by grind)
        newCtx hNumOld hreplace)

protected buffed (inline := true)
def Rewriter.pushBlockArgumentAtSim (blockPtr : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo)
    (idx : UInt64) (type : TypeAttr) (ib : blockPtr.InBounds ctx) (hidx : idx.toNat = blockPtr.spec.getNumArguments! ctx.spec)
    (hcap : idx.toNat < (blockPtr.spec.get! ctx.spec).capArguments := by grind) :
    Option (Sim.IRContext OpInfo) :=
  rlet heq : newBuf ← Rewriter.setBlockArgument blockPtr.impl ctx.buf idx (by prove_setLinkBoundsArgumentSlot ctx blockPtr idx) type
  have hsim := Rewriter.setBlockArgument_pushBlockArgument_sim blockPtr ctx idx type ib hidx hcap _ heq
  let inputs : Erased ((s : IRContext OpInfo) × {p : BlockPtr // p.InBounds s}) :=
    .mk ⟨ctx.spec, blockPtr.spec, ib.ib⟩
  some ⟨newBuf, inputs.map (fun ⟨s, p⟩ => Rewriter.pushBlockArgument s p.val type p.property), by
    simpa only [inputs, Erased.map_mk] using hsim⟩

@[grind .]
theorem Rewriter.pushBlockArgumentAt_spec :
    (Rewriter.pushBlockArgumentAt blockPtr ctx idx type ib hidx hcap) = some ctx' →
    ctx'.spec = Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind) := by
  simp [Rewriter.pushBlockArgumentAt.unfold, Sim.IRContext.spec]
  split <;> grind

@[grind =]
theorem Rewriter.pushBlockArgument_inBounds {ptr : Veir.GenericPtr} {blockPtr : Veir.BlockPtr}
    {ctx : IRContext OpInfo} {ib} :
    ptr.InBounds (Rewriter.pushBlockArgument ctx blockPtr type ib) ↔
    match ptr with
    | .blockArgument argPtr =>
      argPtr.InBounds ctx ∨ argPtr = blockPtr.nextArgument ctx
    | .value (.blockArgument argPtr) =>
      argPtr.InBounds ctx ∨ argPtr = blockPtr.nextArgument ctx
    | .opOperandPtr (.valueFirstUse (.blockArgument argPtr)) =>
      argPtr.InBounds ctx ∨ argPtr = blockPtr.nextArgument ctx
    | _ => ptr.InBounds ctx := by
  constructor <;> grind [Rewriter.pushBlockArgument]

@[grind .]
theorem Rewriter.pushBlockArgumentAt_layoutUnchanged {blockPtr : Sim.BlockPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {ib} {hidx} {hcap}
    (heq : Rewriter.pushBlockArgumentAt blockPtr ctx idx type ib hidx hcap = some ctx') :
    ctx'.spec.LayoutUnchanged ctx.spec := by
  grind [pushBlockArgumentAt_spec heq, Rewriter.pushBlockArgument]

@[grind <=]
theorem Rewriter.pushBlockArgumentAt_veir_inBounds {ptr : Veir.GenericPtr} {blockPtr : Sim.BlockPtr}
    {ctx : Sim.IRContext OpInfo} {ib hidx hcap}
    (heq : Rewriter.pushBlockArgumentAt blockPtr ctx idx type ib hidx hcap = some ctx') :
    ptr.InBounds ctx'.spec ↔
    match ptr with
    | .blockArgument argPtr =>
      argPtr.InBounds ctx.spec ∨ argPtr = blockPtr.spec.nextArgument ctx.spec
    | .value (.blockArgument argPtr) =>
      argPtr.InBounds ctx.spec ∨ argPtr = blockPtr.spec.nextArgument ctx.spec
    | .opOperandPtr (.valueFirstUse (.blockArgument argPtr)) =>
      argPtr.InBounds ctx.spec ∨ argPtr = blockPtr.spec.nextArgument ctx.spec
    | _ => ptr.InBounds ctx.spec := by
  grind [pushBlockArgumentAt_spec heq]

set_option linter.unusedVariables false in -- bug
@[grind .]
theorem Rewriter.pushBlockArgumentAt_fieldsInBounds {blockPtr : Sim.BlockPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {ib} {hidx} {hcap}
    (heq : Rewriter.pushBlockArgumentAt blockPtr ctx idx type ib hidx hcap = some ctx') :
    ctx.spec.FieldsInBounds → ctx'.spec.FieldsInBounds := by
  simp [Rewriter.pushBlockArgumentAt.unfold] at heq
  grind

@[grind =]
theorem UInt64.toNat_toUSize_of_lt (i : UInt64) (hi : i.toNat < 2^32) :
    i.toUSize.toNat = i.toNat := by
  grind [UInt64.toNat_toUSize, System.Platform.numBits_eq]

@[grind =]
theorem Array.uget_eq_get_of_lt_uint32_max (i : UInt64) (hi : i.toNat < 2^32) (a : Array α) h :
    a.uget i.toUSize h = a[i.toNat]'(by grind) := by
  grind [Array.uget]

/-! Buffer helpers writing into the preallocated operation arrays. -/

buffed (inline := true)
def Rewriter.initBlockArgumentsLoopSim (blockPtr: Sim.BlockPtr) (ctx: Sim.IRContext OpInfo)
    (types : Array TypeAttr) (index : UInt64 := 0) (hblock : blockPtr.InBounds ctx := by grind)
    (hidx : index.toNat = blockPtr.spec.getNumArguments! ctx.spec := by grind)
    (hcap : types.size ≤ (blockPtr.spec.get! ctx.spec).capArguments := by grind)
    (hsz : types.size < UInt32.size := by grind) : Option (Sim.IRContext OpInfo) := do
  if h : index ≥ types.usize.toUInt64 then
    ctx
  else
    have : index.toNat < 2^32 := by grind [Array.usize_toUInt64_toNat, UInt64.le_iff_toNat_le]
    rlet ctx ← Rewriter.pushBlockArgumentAt blockPtr ctx index
      (types.uget index.toUSize (by grind [Array.usize_toUInt64_toNat, UInt64.le_iff_toNat_le]))
      (by grind) (by grind)
      (by grind [Array.usize_toUInt64_toNat, UInt64.le_iff_toNat_le])
    -- TODO: simplify...
    Rewriter.initBlockArgumentsLoopSim blockPtr ctx types (index + 1) (hidx := by
      rename_i heq
      have := Rewriter.pushBlockArgumentAt_spec heq
      grind [UInt64.le_iff_toNat_le, UInt64.toNat_mod_size, Rewriter.pushBlockArgument]) (by
      rename_i heq
      have := Rewriter.pushBlockArgumentAt_spec heq
      grind [UInt64.le_iff_toNat_le, UInt64.toNat_mod_size, Rewriter.pushBlockArgument])
      (hcap := by
        rename_i heq
        have := Rewriter.pushBlockArgumentAt_spec heq
        grind [Rewriter.pushBlockArgument])
  termination_by types.size - index.toNat
  decreasing_by
    grind only [Array.usize_toUInt64_toNat, UInt64.le_iff_toNat_le, UInt64.toNat_add,
      UInt64.toNat_mod_size]

buffed (inline := true)
def Rewriter.initBlockArgumentsSim (blockPtr: Sim.BlockPtr) (ctx: Sim.IRContext OpInfo)
    (types : Array TypeAttr) (index : UInt64 := 0) (hblock : blockPtr.InBounds ctx := by grind)
    (hidx : index.toNat = blockPtr.spec.getNumArguments! ctx.spec := by grind)
    (hcap : types.size ≤ (blockPtr.spec.get! ctx.spec).capArguments := by grind)
    (hsz : types.size < UInt32.size := by grind) : Option (Sim.IRContext OpInfo) := do
   Rewriter.initBlockArgumentsLoop blockPtr ctx types index hblock hidx hcap hsz

@[grind .]
theorem Rewriter.initBlockArguments_fieldsInBounds {blockPtr : Sim.BlockPtr}
    {ctx : Sim.IRContext OpInfo} {types index h₁ h₂ h₃ h₄}
    (heq : initBlockArguments blockPtr ctx types index h₁ h₂ h₃ h₄ = some newCtx) :
    ctx.spec.FieldsInBounds → newCtx.spec.FieldsInBounds := by
  grind

/-- This theorem is a more general version of `initBlockArguments_inBounds` that is needed for the induction step in the proof of that theorem. -/
theorem Rewriter.initBlockArguments_inBounds' (ptr : Veir.GenericPtr) {blockPtr : Sim.BlockPtr}
    {ctx : Sim.IRContext OpInfo} {types index h₁ h₂ h₃ h₄}
    (heq : initBlockArguments blockPtr ctx types index h₁ h₂ h₃ h₄ = some newCtx) :
    ptr.InBounds newCtx.spec ↔
    match ptr with
    | .blockArgument argPtr
    | .value (.blockArgument argPtr)
    | .opOperandPtr (.valueFirstUse (.blockArgument argPtr)) =>
      if argPtr.block = blockPtr.spec then
        /- We need `argPtr.index < blockPtr.getNumArguments! ctx` because of the case where we call `initBlockArguments` on a block that already has a larger number of arguments as `types.size`. -/
        argPtr.index < types.size ∨ argPtr.index < blockPtr.spec.getNumArguments! ctx.spec
      else
        argPtr.InBounds ctx.spec
    | _ => ptr.InBounds ctx.spec := by
  simp [initBlockArguments.unfold] at heq
  revert heq
  simp only [initBlockArgumentsLoop.eq_sim] at *
  fun_induction initBlockArgumentsLoopSim <;>
    grind (gen := 20) (splits := 20) [BlockArgumentPtr.inBounds_def, → Array.usize_le_toNat]

theorem Rewriter.initBlockArguments_inBounds (ptr : Veir.GenericPtr) {blockPtr : Sim.BlockPtr}
    {ctx : Sim.IRContext OpInfo} {types h₁ h₂ h₃ h₄}
    (heq : initBlockArguments blockPtr ctx types 0 h₁ h₂ h₃ h₄ = some newCtx) :
    ptr.InBounds newCtx.spec ↔
    match ptr with
    | .blockArgument argPtr
    | .value (.blockArgument argPtr)
    | .opOperandPtr (.valueFirstUse (.blockArgument argPtr)) =>
      if argPtr.block = blockPtr.spec then argPtr.index < types.size else argPtr.InBounds ctx.spec
    | _ => ptr.InBounds ctx.spec := by
  grind [Rewriter.initBlockArguments_inBounds']

grind_pattern Rewriter.initBlockArguments_inBounds =>
  Rewriter.initBlockArguments blockPtr ctx types 0 h₁ h₂ h₃ h₄, some newCtx, ptr.InBounds newCtx.spec

@[grind .]
theorem Rewriter.initBlockArguments_inBounds_veir_mono (ptr : Veir.GenericPtr) {blockPtr : Sim.BlockPtr}
    {ctx : Sim.IRContext OpInfo} {types index h₁ h₂ h₃ h₄}
    (heq : initBlockArguments blockPtr ctx types index h₁ h₂ h₃ h₄ = some newCtx) :
    ptr.InBounds ctx.spec → ptr.InBounds newCtx.spec := by
  simp [initBlockArguments.unfold] at heq
  revert heq
  simp only [initBlockArgumentsLoop.eq_sim] at *
  fun_induction initBlockArgumentsLoopSim
  · grind
  · grind
  · grind [initBlockArgumentsLoopSim._proof_6, Rewriter.pushBlockArgument]

@[grind .]
theorem Rewriter.initBlockArguments_inBounds_mono (ptr : Sim.GenericPtr) {blockPtr : Sim.BlockPtr}
    {ctx : Sim.IRContext OpInfo} {types index h₁ h₂ h₃ h₄}
    (heq : initBlockArguments blockPtr ctx types index h₁ h₂ h₃ h₄ = some newCtx) :
    ptr.InBounds ctx → ptr.InBounds newCtx := by
  simp [initBlockArguments.unfold] at heq
  revert heq
  simp only [initBlockArgumentsLoop.eq_sim] at *
  fun_induction initBlockArgumentsLoopSim <;> grind

buffed (inline := true)
def Rewriter.createBlockSim (ctx: Sim.IRContext OpInfo) (argTypes : Array TypeAttr)
    (insertionPoint: Option BlockInsertPoint)
    (hip : insertionPoint.maybe BlockInsertPoint.InBounds ctx.spec)
    (ipRepr : insertionPoint.maybe₁ BlockInsertPoint.IsRepr)
    : Option (Sim.IRContext OpInfo × Sim.BlockPtr) := do
  -- A block whose argument array reaches `countCard` (`2^32`) cannot be laid out without its size overflowing, so it is not creatable; reject it here.
  if hsz : argTypes.size < Buffed.countCard then
  rlet ⟨newBlockPtr, ctx⟩ ← Sim.BlockPtr.allocFresh ctx (numArgs := argTypes.size.toUInt64)
  have : newBlockPtr.InBounds ctx := by grind
  rlet ctx ← Rewriter.initBlockArguments newBlockPtr ctx argTypes 0 (by grind) (by
    rename_i heq
    have ⟨addr, heq'⟩ := Sim.BlockPtr.allocFresh_spec _ heq
    have : newBlockPtr.spec.get! ctx.spec = .empty argTypes.size := by
      have := BlockPtr.get!_BlockPtr_allocEmptyAtAddress (block := newBlockPtr.spec) heq'
      grind [=_ Array.size_toUInt64_toNat]
    grind) (by
    rename_i heq
    have ⟨addr, heq'⟩ := Sim.BlockPtr.allocFresh_spec _ heq
    have : newBlockPtr.spec.get! ctx.spec = .empty argTypes.size := by
      have := BlockPtr.get!_BlockPtr_allocEmptyAtAddress (block := newBlockPtr.spec) heq'
      grind [=_ Array.size_toUInt64_toNat]
    grind [Veir.Block.empty]) (by grind)
  match h : insertionPoint with
  | some insertionPoint => do
    let ctx ← Rewriter.insertBlock? ctx newBlockPtr insertionPoint (by grind [generic_ptr_grind])
      (by grind [cases BlockInsertPoint]) (by grind [cases BlockInsertPoint]) (by grind)
    (ctx, newBlockPtr)
  | none =>
    (ctx, newBlockPtr)
  else
    none

@[grind .]
theorem Rewriter.createBlock_inBounds_mono (ptr : Sim.GenericPtr) (heq : createBlock ctx types ip hip hrep = some ⟨newCtx, newPtr⟩) :
    ptr.InBounds ctx → ptr.InBounds newCtx := by
  simp only [createBlock.unfold] at heq
  split at heq
  case isFalse => grind
  case isTrue =>
    split at heq
    · grind
    · simp at heq
      split at heq
      · grind
      · split at heq
        · simp [Option.bind] at heq
          split at heq
          · grind
          · rename_i h
            grind [Rewriter.insertBlock?_inBounds ptr h]
        · grind

@[grind .]
theorem Rewriter.createBlock_fieldsInBounds_mono
    (_heq : createBlock ctx types ip hip hrep = some ⟨newCtx, newPtr⟩) :
    ctx.spec.FieldsInBounds → newCtx.spec.FieldsInBounds := by
  simp only [createBlock.unfold] at _heq
  grind

buffed (inline := true)
def Rewriter.createRegionSim (ctx: Sim.IRContext OpInfo) : Option (Sim.IRContext OpInfo × Sim.RegionPtr) := do
  rlet ⟨reg, ctx⟩ ← Sim.RegionPtr.allocFresh ctx
  some (ctx, reg)

@[grind .]
theorem Rewriter.createRegion_new_inBounds (h : createRegion ctx = some (ctx', reg)) :
    reg.InBounds ctx' := by
  grind [createRegion.unfold, Option.bind]

@[grind .]
theorem Rewriter.createRegion_new_not_inBounds (h : createRegion ctx = some (ctx', reg)) :
    ¬ reg.InBounds ctx := by
  grind [createRegion.unfold]

@[grind =>]
theorem Rewriter.createRegion_genericPtr_mono (ptr : GenericPtr) (heq : createRegion ctx = some (ctx', ptr')) :
    ptr.InBounds ctx'.spec ↔ (ptr.InBounds ctx.spec ∨ ptr = .region ptr'.spec) := by
  grind [createRegion.unfold]

@[grind .]
theorem Rewriter.createRegion_fieldsInBounds (_h : createRegion ctx = some (ctx', rg)) :
    ctx.spec.FieldsInBounds → ctx'.spec.FieldsInBounds := by
  grind [createRegion.unfold]

buffed (inline := true)
def Rewriter.pushRegionAtSim (opPtr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (idx : UInt64) (region : Sim.RegionPtr)
    (hop : opPtr.InBounds ctx := by grind) (hregion : region.InBounds ctx := by grind)
    (hRegionParent : (region.spec.get! ctx.spec).parent = none := by grind)
    (hidx : idx.toNat = opPtr.spec.getNumRegions! ctx.spec := by grind)
    (hcap : idx.toNat < (opPtr.spec.get! ctx.spec).capRegions := by grind) :
    Sim.IRContext OpInfo :=
  let inputs : Erased ((s : IRContext OpInfo) × {p : OperationPtr × RegionPtr //
    p.1.InBounds s ∧ p.2.InBounds s ∧ (p.2.get! s).parent = none}) :=
    .mk ⟨ctx.spec, (opPtr.spec, region.spec), hop.ib, hregion.ib, hRegionParent⟩
  ⟨Rewriter.setRegion (OpInfo := OpInfo) opPtr.impl ctx.buf idx region.impl (by prove_setLinkBoundsRegion ctx region)
      (by prove_setLinkBoundsOp ctx opPtr) (by prove_setLinkBoundsRegionSlot ctx opPtr idx),
   inputs.map (fun ⟨s, p⟩ => Rewriter.pushRegion s p.val.1 p.val.2
     p.property.1 p.property.2.1 p.property.2.2), by
     simp only [inputs, Erased.map_mk]
     exact
       Rewriter.setRegion_pushRegion_sim opPtr ctx idx region hop hregion hRegionParent hidx hcap _ _ _⟩

@[simp, grind =]
theorem Rewriter.pushRegionAt_inBounds_veir_mono (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx region h₁ h₂ h₃ h₄ h₅} :
    ptr.InBounds (pushRegionAt opPtr ctx idx region h₁ h₂ h₃ h₄ h₅).spec ↔ ptr.InBounds ctx.spec := by
  simp only [pushRegionAt.unfold] <;> grind

@[grind .]
theorem Rewriter.pushRegionAt_layoutUnchanged {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx region h₁ h₂ h₃ h₄ h₅} :
    ctx.spec.LayoutUnchanged (pushRegionAt opPtr ctx idx region h₁ h₂ h₃ h₄ h₅).spec := by
  simp only [pushRegionAt.unfold, pushRegion] <;>
  apply IRContext.LayoutUnchanged.trans (region.spec.setParent ctx.spec opPtr.spec (by grind)) <;> grind

@[simp, grind =]
theorem Rewriter.pushRegionAt_inBounds_mono (ptr : Sim.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx region h₁ h₂ h₃ h₄ h₅} :
    ptr.InBounds (pushRegionAt opPtr ctx idx region h₁ h₂ h₃ h₄ h₅) ↔ ptr.InBounds ctx := by
  grind

@[grind .]
theorem Rewriter.pushRegion_fieldsInBounds {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx region h₁ h₂ h₃ h₄ h₅} (hx : ctx.spec.FieldsInBounds) :
    (pushRegionAt opPtr ctx idx region h₁ h₂ h₃ h₄ h₅).spec.FieldsInBounds := by
  exact (pushRegionAt opPtr ctx idx region h₁ h₂ h₃ h₄ h₅).sim.fieldsInBounds

set_option maxHeartbeats 1600000 in
buffed (inline := true)
def Rewriter.initOpRegionsSim (opPtr: Sim.OperationPtr) (ctx: Sim.IRContext OpInfo)
    (regions : Array Sim.RegionPtr) (index : UInt64 := 0)
    (opPtrInBounds : opPtr.InBounds ctx := by grind)
    (hregionInBounds : (∀ i (hi : i < regions.size), regions[i].InBounds ctx))
    (hctx : ctx.spec.FieldsInBounds := by grind)
    (hn : index.toNat = opPtr.spec.getNumRegions! ctx.spec := by grind)
    (hcap : regions.size ≤ (opPtr.spec.get! ctx.spec).capRegions := by grind) :
    Option (Sim.IRContext OpInfo) := do
  have hsize : regions.size ≤ Buffed.countCard := by
    have := ctx.sim.repr.operations_indices opPtr.spec opPtrInBounds.ib |>.regions
    grind
  if h: index.toNat >= regions.size then
    some ctx
  else
    let region := regions[index.toNat]'(by omega)
    match hParent : (region.getParent ctx (by grind [hregionInBounds index.toNat (by grind [UInt64.le_iff_toNat_le])])).toOption with
    | none =>
      let ctx := Rewriter.pushRegionAt opPtr ctx index region
        (hregion := by grind [hregionInBounds index.toNat (by grind [UInt64.le_iff_toNat_le])])
        (hRegionParent := by grind)
        (hcap := by grind [Array.usize_toUInt64_toNat, UInt64.le_iff_toNat_le])
      Rewriter.initOpRegionsSim opPtr ctx regions (index + 1)
        (opPtrInBounds := by grind [generic_ptr_grind])
        (hregionInBounds := by grind [generic_ptr_grind, Array.sizeU64_toNat])
        (hctx := by grind)
        (hn := by
          have : (index + 1).toNat = index.toNat + 1 := by
            grind [UInt64.le_iff_toNat_le, Array.sizeU64_toNat]
          grind [Rewriter.pushRegionAt.unfold])
        (hcap := by grind [Rewriter.pushRegionAt.unfold, Rewriter.pushRegion])
    | some _ => none
  termination_by regions.size - index.toNat
  decreasing_by grind only [Array.sizeU64_toNat, UInt64.le_iff_toNat_le, UInt64.toNat_add,
    UInt64.toNat_mod_size]

@[grind .]
theorem Rewriter.initOpRegions_fieldsInBounds {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {regions n opPtrInBounds hregions hctx hn hcap} :
    ctx.spec.FieldsInBounds →
    initOpRegions opPtr ctx regions n opPtrInBounds hregions hctx hn hcap = some ctx' →
    ctx'.spec.FieldsInBounds := by
  simp only [initOpRegions.eq_sim] at *
  fun_induction initOpRegionsSim <;> grind

@[grind .]
theorem Rewriter.initOpRegions_inBounds_mono (ptr : Sim.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {regions n opPtrInBounds hregions hctx hn hcap} :
    ptr.InBounds ctx →
    initOpRegions opPtr ctx regions n opPtrInBounds hregions hctx hn hcap = some ctx' →
    ptr.InBounds ctx' := by
  simp only [initOpRegions.eq_sim] at *
  fun_induction initOpRegionsSim <;> grind

@[grind .]
theorem Rewriter.initOpRegions_inBounds_veir_mono (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {regions n opPtrInBounds hregions hctx hn hcap} :
    ptr.InBounds ctx.spec →
    initOpRegions opPtr ctx regions n opPtrInBounds hregions hctx hn hcap = some ctx' →
    ptr.InBounds ctx'.spec := by
  simp only [initOpRegions.eq_sim] at *
  fun_induction initOpRegionsSim <;> grind

@[grind .]
theorem Rewriter.initOpRegions_preserves_numOperands (ptr : Veir.OperationPtr)
    {ctx ctx' : Sim.IRContext OpInfo} {index h₁ h₂ h₃ h₄ h₅}
    (heq : Rewriter.initOpRegions opPtr ctx regions index h₁ h₂ h₃ h₄ h₅ = some ctx') :
    ptr.getNumOperands! ctx'.spec = ptr.getNumOperands! ctx.spec := by
  simp only [initOpRegions.eq_sim] at *
  fun_induction initOpRegionsSim <;> grind (gen := 20) [pushRegionAt.unfold]

@[grind .]
theorem Rewriter.initOpRegions_preserves_numSuccessors (ptr : Veir.OperationPtr)
    {ctx ctx' : Sim.IRContext OpInfo} {index h₁ h₂ h₃ h₄ h₅}
    (heq : Rewriter.initOpRegions opPtr ctx regions index h₁ h₂ h₃ h₄ h₅ = some ctx') :
    ptr.getNumSuccessors! ctx'.spec = ptr.getNumSuccessors! ctx.spec := by
  simp only [initOpRegions.eq_sim] at *
  fun_induction initOpRegionsSim <;> grind (gen := 20) [pushRegionAt.unfold]

/- Region pushes never touch the operand/block-operand capacities (cf. the `initOpResults` capacity-preservation lemmas above). -/
theorem Rewriter.initOpRegions_preserves_capOperands (ptr : Veir.OperationPtr)
    {ctx ctx' : Sim.IRContext OpInfo} {index h₁ h₂ h₃ h₄ h₅}
    (heq : Rewriter.initOpRegions opPtr ctx regions index h₁ h₂ h₃ h₄ h₅ = some ctx') :
    (ptr.get! ctx'.spec).capOperands = (ptr.get! ctx.spec).capOperands := by
  simp only [initOpRegions.eq_sim] at *
  fun_induction initOpRegionsSim <;> grind (gen := 20) [pushRegionAt.unfold]

theorem Rewriter.initOpRegions_preserves_capBlockOperands (ptr : Veir.OperationPtr)
    {ctx ctx' : Sim.IRContext OpInfo} {index h₁ h₂ h₃ h₄ h₅}
    (heq : Rewriter.initOpRegions opPtr ctx regions index h₁ h₂ h₃ h₄ h₅ = some ctx') :
    (ptr.get! ctx'.spec).capBlockOperands = (ptr.get! ctx.spec).capBlockOperands := by
  simp only [initOpRegions.eq_sim] at *
  fun_induction initOpRegionsSim <;> grind (gen := 20) [pushRegionAt.unfold]

buffed (inline := true)
def Rewriter.pushResultAtSim (opPtr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (idx : UInt64) (type : TypeAttr) (hop : opPtr.InBounds ctx := by grind)
    (hidx : idx.toNat = opPtr.spec.getNumResults! ctx.spec := by grind)
    (hcap : idx.toNat < (opPtr.spec.get! ctx.spec).capResults := by grind)
    (hattrs : ctx.buf.attributes.size < UInt64.size := by grind) :
    Sim.IRContext OpInfo :=
  rlet hres : bufctx := Rewriter.setResult opPtr.impl ctx.buf idx (by prove_setLinkBoundsOp ctx opPtr) (by prove_setLinkBoundsResultSlot ctx opPtr idx) type hattrs
  have simres := Rewriter.setResult_pushResult_sim opPtr ctx idx type hop hidx hcap _ _ hattrs hres
  let inputs : Erased ((s : IRContext OpInfo) × {p : OperationPtr // p.InBounds s}) :=
    .mk ⟨ctx.spec, opPtr.spec, by grind⟩
  ⟨bufctx, inputs.map (fun ⟨s, p⟩ => Rewriter.pushResult s p.val type p.property), by
    simpa only [inputs, Erased.map_mk] using simres⟩

@[grind =>]
theorem Rewriter.pushResultAt_spec {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {idx type hop hidx hcap hattrs}
    (heq : Rewriter.pushResultAt opPtr ctx idx type hop hidx hcap hattrs = ctx') :
    ctx'.spec = Rewriter.pushResult ctx.spec opPtr.spec type (by grind) := by
  simp only [pushResultAt.unfold] at heq
  grind

/-- `pushResultAt` appends exactly the result type to the attribute table; used to re-establish
the hoisted capacity bound across the `initOpResults` loop. -/
theorem Rewriter.pushResultAt_attributes {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {idx type hop hidx hcap hattrs}
    (heq : Rewriter.pushResultAt opPtr ctx idx type hop hidx hcap hattrs = ctx') :
    ctx'.buf.attributes = ctx.buf.attributes.push type := by
  simp only [pushResultAt.unfold] at heq
  rw [← heq]
  -- Definitional: the five writes only touch `mem`, and `insertAttrsBounded` pushes `type`.
  rfl

set_option linter.unusedVariables false in -- bug
@[grind .]
theorem Rewriter.pushResultAt_fieldsInBounds {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {idx type hop hidx hcap hattrs}
    (heq : Rewriter.pushResultAt opPtr ctx idx type hop hidx hcap hattrs = ctx') :
    ctx.spec.FieldsInBounds → ctx'.spec.FieldsInBounds := by
  simp only [pushResultAt.unfold] at heq
  grind

@[grind .]
theorem Rewriter.pushResultAt_layoutUnchanged {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {idx type hop hidx hcap hattrs}
    (heq : Rewriter.pushResultAt opPtr ctx idx type hop hidx hcap hattrs = ctx') :
    ctx'.spec.LayoutUnchanged ctx.spec := by
  rw [Rewriter.pushResultAt_spec heq]
  grind [generic_ptr_grind, Rewriter.pushResult]

@[grind .]
theorem Rewriter.pushResultAt_veir_inBounds_mono (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {idx type hop hidx hcap hattrs}
    (heq : Rewriter.pushResultAt opPtr ctx idx type hop hidx hcap hattrs = ctx') :
    ptr.InBounds ctx.spec → ptr.InBounds ctx'.spec := by
  rw [Rewriter.pushResultAt_spec heq]
  grind [generic_ptr_grind, Rewriter.pushResult]

@[grind =>]
theorem Rewriter.pushResultAt_inBounds (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {idx type hop hidx hcap hattrs}
    (heq : Rewriter.pushResultAt opPtr ctx idx type hop hidx hcap hattrs = ctx') :
    ptr.InBounds ctx'.spec ↔
    (ptr.InBounds ctx.spec ∨
      ptr = .opResult (opPtr.spec.nextResult ctx.spec) ∨
      ptr = .value (opPtr.spec.nextResult ctx.spec) ∨
      ptr = .opOperandPtr (.valueFirstUse (opPtr.spec.nextResult ctx.spec)))
    := by
  rw [Rewriter.pushResultAt_spec heq]
  grind [Rewriter.pushResult]

buffed (inline := true)
def Rewriter.initOpResultsSim (opPtr: Sim.OperationPtr) (ctx: Sim.IRContext OpInfo)
    (resultTypes: Array TypeAttr) (index: UInt64 := 0) (hop : opPtr.InBounds ctx := by grind)
    (hidx : index.toNat = opPtr.spec.getNumResults! ctx.spec := by grind)
    (hcap : resultTypes.size ≤ (opPtr.spec.get! ctx.spec).capResults := by grind)
    (hsz : resultTypes.size < UInt32.size := by grind)
    -- Hoisted attribute-table capacity bound covering the remaining pushes: `createOp` checks it
    -- once, so the loop body is `Option`-free (no `some` boxing, no `Nat < 2^64` GMP compare).
    (hattrs : ctx.buf.attributes.size + (resultTypes.size - index.toNat) < UInt64.size := by grind) :
    Sim.IRContext OpInfo :=
  if h: index >= resultTypes.usize.toUInt64 then
    ctx
  else
    have : index.toNat < 2^32 := by grind [Array.usize_toUInt64_toNat, UInt64.le_iff_toNat_le]
    have hlt : index.toNat < resultTypes.size := by
      grind [Array.usize_toUInt64_toNat, UInt64.le_iff_toNat_le]
    let type := resultTypes.uget index.toUSize (by grind [Array.usize_toUInt64_toNat, UInt64.le_iff_toNat_le])
    -- Explicit `match` rather than `rlet … := …`: the `with` keyword delimits the scrutinee, so
    -- the recursive call below is not swallowed as extra application arguments.
    match _ : Rewriter.pushResultAt opPtr ctx index type (by grind) (by grind)
      (by grind [Array.usize_toUInt64_toNat, UInt64.le_iff_toNat_le])
      -- Term-level (not `omega`): in the regenerated recursive impl the goal and `hattrs` spell
      -- `ctx` differently (rebinding `let` vs reconstructed literal), which defeats atom matching.
      (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hattrs) with
    | ctx =>
    Rewriter.initOpResultsSim opPtr ctx resultTypes (index + 1) (by grind [generic_ptr_grind]) (by
      have : (index + 1).toNat = index.toNat + 1 := by grind [Array.usize_toUInt64_toNat]
      rw [Rewriter.pushResultAt_spec (by assumption)]
      grind [Rewriter.pushResult])
      (by
        rw [Rewriter.pushResultAt_spec (by assumption)]
        grind [Rewriter.pushResult])
      (by grind)
      (by
        have hpa := Rewriter.pushResultAt_attributes (by assumption)
        have : (index + 1).toNat = index.toNat + 1 := by grind [Array.usize_toUInt64_toNat]
        grind [Array.size_push])
  termination_by resultTypes.size - index.toNat
  decreasing_by grind only [Array.usize_toUInt64_toNat, UInt64.le_iff_toNat_le, UInt64.toNat_add,
    UInt64.toNat_mod_size, = UInt64.add_toNat_lt]

@[grind .]
theorem Rewriter.initOpResults_fieldsInBounds {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂ h₃ h₄ h₅}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ h₃ h₄ h₅ = ctx') :
    ctx.spec.FieldsInBounds → ctx'.spec.FieldsInBounds := by
  simp only [initOpResults.eq_sim] at *
  fun_induction initOpResultsSim <;> grind

@[grind .]
theorem Rewriter.initOpResults_inBounds_mono (ptr : Sim.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂ h₃ h₄ h₅}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ h₃ h₄ h₅ = ctx') :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  simp only [initOpResults.eq_sim] at *
  fun_induction initOpResultsSim <;> grind

@[grind .]
theorem Rewriter.initOpResults_inBounds_veir_mono (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂ h₃ h₄ h₅}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ h₃ h₄ h₅ = ctx') :
    ptr.InBounds ctx.spec → ptr.InBounds ctx'.spec := by
  simp only [initOpResults.eq_sim] at *
  fun_induction initOpResultsSim <;> grind

/-- Application-form variant (cf. `initOpOperands_inBounds_mono'`): with the non-`Option` return
the call often appears inline rather than behind an equation hypothesis, and `grind` needs the
pattern in the conclusion to fire. -/
@[grind .]
theorem Rewriter.initOpResults_inBounds_veir_mono' (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {resultTypes index h₁ h₂ h₃ h₄ h₅} :
    ptr.InBounds ctx.spec → ptr.InBounds (initOpResults opPtr ctx resultTypes index h₁ h₂ h₃ h₄ h₅).spec :=
  Rewriter.initOpResults_inBounds_veir_mono ptr (heq := rfl)

/-- An in-bounds insertion point stays in bounds across `initOpResults`. Standalone so that
`createOp` applies it in one step: an inline proof would be inlined into the definition's
body term and re-traversed by every `split at heq` in the `createOp_*` lemmas below. -/
theorem Rewriter.initOpResults_insertPoint_inBounds {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂ h₃ h₄ h₅} {ip : Option InsertPoint}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ h₃ h₄ h₅ = ctx')
    (hins : ip.maybe InsertPoint.InBounds ctx.spec) :
    ip.maybe InsertPoint.InBounds ctx'.spec := by
  rw [Option.maybe_def]
  intro p hp
  rw [Option.maybe_def] at hins
  have hprev := hins p hp
  cases p with
  | before op =>
    rw [InsertPoint.inBounds_before, ← GenericPtr.iff_operation] at hprev ⊢
    exact Rewriter.initOpResults_inBounds_veir_mono (.operation op) heq hprev
  | atEnd bl =>
    rw [InsertPoint.inBounds_atEnd, ← GenericPtr.iff_block] at hprev ⊢
    exact Rewriter.initOpResults_inBounds_veir_mono (.block bl) heq hprev

@[grind .]
theorem Rewriter.initOpResults_preserves_numRegions (ptr : Veir.OperationPtr)
    {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂ h₃ h₄ h₅}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ h₃ h₄ h₅ = ctx') :
    ptr.getNumRegions! ctx'.spec = ptr.getNumRegions! ctx.spec := by
  simp only [initOpResults.eq_sim] at *
  fun_induction initOpResultsSim <;> grind [Rewriter.pushResult]

@[grind .]
theorem Rewriter.initOpResults_preserves_numOperands (ptr : Veir.OperationPtr)
    {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂ h₃ h₄ h₅}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ h₃ h₄ h₅ = ctx') :
    ptr.getNumOperands! ctx'.spec = ptr.getNumOperands! ctx.spec := by
  simp only [initOpResults.eq_sim] at *
  fun_induction initOpResultsSim <;> grind [Rewriter.pushResult]

@[grind .]
theorem Rewriter.initOpResults_preserves_numSuccessors (ptr : Veir.OperationPtr)
    {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂ h₃ h₄ h₅}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ h₃ h₄ h₅ = ctx') :
    ptr.getNumSuccessors! ctx'.spec = ptr.getNumSuccessors! ctx.spec := by
  simp only [initOpResults.eq_sim] at *
  fun_induction initOpResultsSim <;> grind [Rewriter.pushResult]

/- Pushing results only grows the `results` array, so every capacity field survives the loop. -/
theorem Rewriter.initOpResults_preserves_capRegions (ptr : Veir.OperationPtr)
    {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂ h₃ h₄ h₅}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ h₃ h₄ h₅ = ctx') :
    (ptr.get! ctx'.spec).capRegions = (ptr.get! ctx.spec).capRegions := by
  simp only [initOpResults.eq_sim] at *
  fun_induction initOpResultsSim <;> grind [Rewriter.pushResult]

theorem Rewriter.initOpResults_preserves_capOperands (ptr : Veir.OperationPtr)
    {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂ h₃ h₄ h₅}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ h₃ h₄ h₅ = ctx') :
    (ptr.get! ctx'.spec).capOperands = (ptr.get! ctx.spec).capOperands := by
  simp only [initOpResults.eq_sim] at *
  fun_induction initOpResultsSim <;> grind [Rewriter.pushResult]

theorem Rewriter.initOpResults_preserves_capBlockOperands (ptr : Veir.OperationPtr)
    {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂ h₃ h₄ h₅}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ h₃ h₄ h₅ = ctx') :
    (ptr.get! ctx'.spec).capBlockOperands = (ptr.get! ctx.spec).capBlockOperands := by
  simp only [initOpResults.eq_sim] at *
  fun_induction initOpResultsSim <;> grind [Rewriter.pushResult]

protected buffed (inline := true)
def Rewriter.pushOperandAtUninsertedSim (opPtr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (off : Int64) (idx : UInt64) (valuePtr : Sim.ValuePtr) (opPtrInBounds : opPtr.InBounds ctx := by grind)
    (valueInBounds : valuePtr.InBounds ctx := by grind)
    (hidx : idx.toNat = opPtr.spec.getNumOperands! ctx.spec := by grind)
    (hcap : idx.toNat < (opPtr.spec.get! ctx.spec).capOperands := by grind)
    -- `off` is the hoisted operands base offset (cf. `detachOperands.loop`): recomputing the slot
    -- per push costs a boxed `propertySizeOfEncoded` dispatch, two heap allocations per operand.
    (hoff : off = Buffed.Operation.Offsets.operands opPtr.spec ctx.spec := by grind) :
    Sim.IRContext OpInfo :=
  let inputs : Erased ((s : IRContext OpInfo) × {p : OperationPtr × ValuePtr //
    p.1.InBounds s ∧ p.2.InBounds s}) :=
    .mk ⟨ctx.spec, (opPtr.spec, valuePtr.spec), opPtrInBounds.ib, valueInBounds.ib⟩
  ⟨Rewriter.setOperand (OpInfo := OpInfo) opPtr.impl (opPtr.impl + (off + Buffed.OpOperand.size * idx)) ctx.buf idx
     (by prove_setLinkBoundsOp ctx opPtr)
     (by simp only [Buffed.OperationMPtr.computeOperandOffset]
         rw [hoff, OperationPtr.computeOperandOffset_eq ctx opPtr opPtrInBounds.ib opPtrInBounds.sim])
     (by prove_setLinkBoundsOperandSlot ctx opPtr idx) valuePtr.impl,
   inputs.map (fun ⟨s, p⟩ => Rewriter.pushOperand s p.val.1 p.val.2 p.property.1 p.property.2), by
     simp only [inputs, Erased.map_mk]
     exact
       Rewriter.setOperand_pushOperand_sim opPtr ctx idx valuePtr opPtrInBounds valueInBounds hidx hcap _ _ _⟩

@[simp, grind =]
theorem Rewriter.pushOperandAtUninserted_spec :
    (Rewriter.pushOperandAtUninserted opPtr ctx off idx valuePtr h₁ h₂ h₃ h₄ h₅).spec =
    Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind) := by
  simp [Rewriter.pushOperandAtUninserted.unfold, Sim.IRContext.spec]

@[grind .]
theorem Rewriter.pushOperandAtUninserted_layoutUnchanged {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {off idx valuePtr h₁ h₂ h₃ h₄ h₅} :
    (Rewriter.pushOperandAtUninserted opPtr ctx off idx valuePtr h₁ h₂ h₃ h₄ h₅).spec.LayoutUnchanged ctx.spec := by
  simp [Rewriter.pushOperandAtUninserted.unfold, Rewriter.pushOperandAtUninserted.unfold, Rewriter.pushOperand]
  grind

@[grind =>]
theorem Rewriter.pushOperandAtUninserted_veir_inBounds (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {off idx valuePtr h₁ h₂ h₃ h₄ h₅} :
    ptr.InBounds (Rewriter.pushOperandAtUninserted opPtr ctx off idx valuePtr h₁ h₂ h₃ h₄ h₅).spec ↔
    (ptr.InBounds ctx.spec ∨
     ptr = .opOperand (opPtr.spec.nextOperand ctx.spec) ∨
     ptr = .opOperandPtr (.operandNextUse (opPtr.spec.nextOperand ctx.spec))) := by
  simp [Rewriter.pushOperandAtUninserted.unfold, Rewriter.pushOperandAtUninserted.unfold, Rewriter.pushOperand]
  grind

protected buffed (inline := true)
def Rewriter.pushOperandAtSim (opPtr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (off : Int64) (idx : UInt64) (valuePtr : Sim.ValuePtr) (opPtrInBounds : opPtr.InBounds ctx := by grind)
    (valueInBounds : valuePtr.InBounds ctx := by grind)
    (hidx : idx.toNat = opPtr.spec.getNumOperands! ctx.spec := by grind)
    (hcap : idx.toNat < (opPtr.spec.get! ctx.spec).capOperands := by grind)
    (hoff : off = Buffed.Operation.Offsets.operands opPtr.spec ctx.spec := by grind) :
    Sim.IRContext OpInfo :=
  let ctx := Rewriter.pushOperandAtUninserted opPtr ctx off idx valuePtr
  let oper := opPtr.getOperandPtrAt ctx off idx (by grind [generic_ptr_grind])
    (by grind [Buffed.Operation.Offsets.operands_layoutPreserved])
  oper.insertIntoCurrent ctx (by grind [Rewriter.pushOperandAtUninserted.unfold,
    Sim.OperationPtr.getOpOperand_inBounds,
    Rewriter.pushOperand]) (by grind [generic_ptr_grind])

@[grind =>]
theorem Rewriter.pushOperandAt_layoutPreserved {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {off idx valuePtr h₁ h₂ h₃ h₄ h₅} :
    ctx.spec.LayoutPreserved (Rewriter.pushOperandAt opPtr ctx off idx valuePtr h₁ h₂ h₃ h₄ h₅).spec := by
  simp [Rewriter.pushOperandAt.unfold]
  apply IRContext.LayoutPreserved.trans (Rewriter.pushOperandAtUninserted opPtr ctx off idx valuePtr (by grind) (by grind)).spec <;>
    grind

@[grind =>]
theorem Rewriter.pushOperandAt_veir_inBounds (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {off idx valuePtr h₁ h₂ h₃ h₄ h₅} :
    ptr.InBounds (Rewriter.pushOperandAt opPtr ctx off idx valuePtr h₁ h₂ h₃ h₄ h₅).spec ↔
    (ptr.InBounds ctx.spec ∨
     ptr = .opOperand (opPtr.spec.nextOperand ctx.spec) ∨
     ptr = .opOperandPtr (.operandNextUse (opPtr.spec.nextOperand ctx.spec))) := by
  simp [Rewriter.pushOperandAt.unfold]
  grind

@[grind .]
theorem Rewriter.pushOperand_inBounds_mono (ptr : Sim.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {off idx valuePtr h₁ h₂ h₃ h₄ h₅} :
    ptr.InBounds ctx → ptr.InBounds (Rewriter.pushOperandAt opPtr ctx off idx valuePtr h₁ h₂ h₃ h₄ h₅) := by
  simp [Rewriter.pushOperandAt.unfold]
  grind

@[grind .]
theorem Rewriter.pushOperand_fieldsInBounds {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {off idx valuePtr h₁ h₂ h₃ h₄ h₅} :
    (Rewriter.pushOperandAt opPtr ctx off idx valuePtr h₁ h₂ h₃ h₄ h₅).spec.FieldsInBounds := by
  simp [Rewriter.pushOperandAt.unfold]
  grind

@[grind .]
theorem Rewriter.pushOperand_preserves_numSuccessors (ptr : Veir.OperationPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {off idx valuePtr h₁ h₂ h₃ h₄ h₅} :
    ptr.getNumSuccessors! (Rewriter.pushOperandAt opPtr ctx off idx valuePtr h₁ h₂ h₃ h₄ h₅).spec = ptr.getNumSuccessors! ctx.spec := by
  simp [Rewriter.pushOperandAt.unfold]
  grind [Rewriter.pushOperand]

theorem Rewriter.pushOperand_preserves_capBlockOperands (ptr : Veir.OperationPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {off idx valuePtr h₁ h₂ h₃ h₄ h₅} :
    (ptr.get! (Rewriter.pushOperandAt opPtr ctx off idx valuePtr h₁ h₂ h₃ h₄ h₅).spec).capBlockOperands = (ptr.get! ctx.spec).capBlockOperands := by
  simp [Rewriter.pushOperandAt.unfold]
  grind [Rewriter.pushOperand]

set_option maxHeartbeats 1600000 in
buffed (inline := true)
def Rewriter.initOpOperands.loopSim (opPtr: Sim.OperationPtr) (ctx: Sim.IRContext OpInfo)
    (opPtrInBounds : opPtr.InBounds ctx) (operands : Array Sim.ValuePtr)
    (hoperands : (∀ i (hi : i < operands.size), operands[i].InBounds ctx))
    (off : Int64)
    (index : UInt64 := 0) (hidx : index.toNat = opPtr.spec.getNumOperands! ctx.spec := by grind)
    (hcap : operands.size ≤ (opPtr.spec.get! ctx.spec).capOperands := by grind)
    -- Hoisted operands base offset (the wrapper computes it once per op); recomputing it per push
    -- costs two boxed `propertySizeOfEncoded` dispatches per operand.
    (hoff : off = Buffed.Operation.Offsets.operands opPtr.spec ctx.spec := by grind) :
    Sim.IRContext OpInfo :=
  have hsize : operands.size ≤ Buffed.countCard := by
    have := ctx.sim.repr.operations_indices opPtr.spec opPtrInBounds.ib |>.operands
    grind
  if h : index.toNat >= operands.size then
    ctx
  else
    let valuePtr := operands[index.toNat]'(by omega)
    let ctx := Rewriter.pushOperandAt opPtr ctx off index valuePtr
      (valueInBounds := by grind [hoperands index.toNat (by grind [UInt64.le_iff_toNat_le])])
      (hcap := by grind [Array.usize_toUInt64_toNat, UInt64.le_iff_toNat_le])
    Rewriter.initOpOperands.loopSim opPtr ctx (by grind [generic_ptr_grind]) operands
      (by grind [generic_ptr_grind, Array.sizeU64_toNat]) off (index + 1) (by
      grind [Rewriter.pushOperandAt.unfold, Rewriter.pushOperandAt.unfold, Sim.IRContext.isRepr, Rewriter.pushOperand])
      (by
        grind [Rewriter.pushOperandAt.unfold, Rewriter.pushOperandAt.unfold, Rewriter.pushOperand])
      (by
        grind [Rewriter.pushOperandAt.unfold, Rewriter.pushOperandAt.unfold,
          Rewriter.pushOperand, Buffed.Operation.Offsets.operands_layoutPreserved])
  termination_by operands.size - index.toNat
  decreasing_by grind only [Array.usize_toUInt64_toNat, unfold_pointers, UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_mod_size]

buffed (inline := true)
def Rewriter.initOpOperandsSim (opPtr: Sim.OperationPtr) (ctx: Sim.IRContext OpInfo)
    (opPtrInBounds : opPtr.InBounds ctx) (operands : Array Sim.ValuePtr)
    (hoperands : (∀ i (hi : i < operands.size), operands[i].InBounds ctx))
    (index : UInt64 := 0) (hidx : index.toNat = opPtr.spec.getNumOperands! ctx.spec := by grind)
    (hcap : operands.size ≤ (opPtr.spec.get! ctx.spec).capOperands := by grind) :
    Sim.IRContext OpInfo :=
  -- Early exit before `getOperandsOffset`: operand-less ops (e.g. constants) skip the
  -- `propertySizeOfEncoded` dispatch entirely.
  if h : index.toNat >= operands.size then
    ctx
  else
    Rewriter.initOpOperands.loop opPtr ctx opPtrInBounds operands hoperands
      (opPtr.getOperandsOffset ctx opPtrInBounds) index hidx hcap (by grind)

set_option linter.unusedVariables false in -- bug
@[grind .]
theorem Rewriter.initOpOperands.loop_fieldsInBounds {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {h₁ operands h₂ off index hidx hcap hoff}
    (heq : initOpOperands.loop opPtr ctx h₁ operands h₂ off index hidx hcap hoff = ctx') :
    ctx.spec.FieldsInBounds → ctx'.spec.FieldsInBounds := by
  intro _
  exact ctx'.sim.fieldsInBounds

@[grind .]
theorem Rewriter.initOpOperands.loop_inBounds_mono (ptr : Sim.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {h₁ operands h₂ off index hidx hcap hoff}
    (heq : initOpOperands.loop opPtr ctx h₁ operands h₂ off index hidx hcap hoff = ctx') :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  simp only [initOpOperands.loop.eq_sim] at *
  fun_induction initOpOperands.loopSim <;> grind

@[grind .]
theorem Rewriter.initOpOperands.loop_inBounds_mono' (ptr : Sim.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {h₁ operands h₂ off index hidx hcap hoff} :
    ptr.InBounds ctx → ptr.InBounds (initOpOperands.loop opPtr ctx h₁ operands h₂ off index hidx hcap hoff) := by
  simp only [initOpOperands.loop.eq_sim] at *
  fun_induction initOpOperands.loopSim <;> grind

@[grind .]
theorem Rewriter.initOpOperands.loop_inBounds_veir_mono (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {h₁ operands h₂ off index hidx hcap hoff} :
    ptr.InBounds ctx.spec → ptr.InBounds (initOpOperands.loop opPtr ctx h₁ operands h₂ off index hidx hcap hoff).spec := by
  simp only [initOpOperands.loop.eq_sim] at *
  fun_induction initOpOperands.loopSim <;> grind

@[grind .]
theorem Rewriter.initOpOperands.loop_preserves_numSuccessors! (ptr : Veir.OperationPtr)
    {ctx ctx' : Sim.IRContext OpInfo} {h₁ operands h₂ off index hidx hcap hoff}
    (heq : initOpOperands.loop opPtr ctx h₁ operands h₂ off index hidx hcap hoff = ctx') :
    ptr.getNumSuccessors! ctx'.spec = ptr.getNumSuccessors! ctx.spec := by
  simp only [initOpOperands.loop.eq_sim] at *
  fun_induction initOpOperands.loopSim <;> grind

theorem Rewriter.initOpOperands.loop_preserves_capBlockOperands (ptr : Veir.OperationPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {h₁ operands h₂ off index hidx hcap hoff} :
    (ptr.get! (initOpOperands.loop opPtr ctx h₁ operands h₂ off index hidx hcap hoff).spec).capBlockOperands
      = (ptr.get! ctx.spec).capBlockOperands := by
  simp only [initOpOperands.loop.eq_sim] at *
  fun_induction initOpOperands.loopSim <;> grind [Rewriter.pushOperand_preserves_capBlockOperands]

/-! Wrapper lemmas: the original `initOpOperands` statements, proved by case-splitting the
early-exit and delegating to the loop lemmas. -/

set_option linter.unusedVariables false in -- bug
@[grind .]
theorem Rewriter.initOpOperands_fieldsInBounds {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {h₁ operands h₂ index hidx hcap}
    (heq : initOpOperands opPtr ctx h₁ operands h₂ index hidx hcap = ctx') :
    ctx.spec.FieldsInBounds → ctx'.spec.FieldsInBounds := by
  grind

@[grind .]
theorem Rewriter.initOpOperands_inBounds_mono (ptr : Sim.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {h₁ operands h₂ index hidx hcap}
    (heq : initOpOperands opPtr ctx h₁ operands h₂ index hidx hcap = ctx') :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  grind [Rewriter.initOpOperands.unfold]

@[grind .]
theorem Rewriter.initOpOperands_inBounds_mono' (ptr : Sim.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {h₁ operands h₂ index hidx hcap} :
    ptr.InBounds ctx → ptr.InBounds (initOpOperands opPtr ctx h₁ operands h₂ index hidx hcap) := by
  grind

@[grind .]
theorem Rewriter.initOpOperands_inBounds_veir_mono (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {h₁ operands h₂ index hidx hcap} :
    ptr.InBounds ctx.spec → ptr.InBounds (initOpOperands opPtr ctx h₁ operands h₂ index hidx hcap).spec := by
  grind [Rewriter.initOpOperands.unfold]

@[grind .]
theorem Rewriter.initOpOperands_preserves_numSuccessors! (ptr : Veir.OperationPtr)
    {ctx ctx' : Sim.IRContext OpInfo} {h₁ operands h₂ index hidx hcap}
    (heq : initOpOperands opPtr ctx h₁ operands h₂ index hidx hcap = ctx') :
    ptr.getNumSuccessors! ctx'.spec = ptr.getNumSuccessors! ctx.spec := by
  grind [Rewriter.initOpOperands.unfold]

/- Operand pushes never touch the block-operand capacity (cf. the `initOpResults` capacity-preservation lemmas above). -/
theorem Rewriter.initOpOperands_preserves_capBlockOperands (ptr : Veir.OperationPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {h₁ operands h₂ index hidx hcap} :
    (ptr.get! (initOpOperands opPtr ctx h₁ operands h₂ index hidx hcap).spec).capBlockOperands
      = (ptr.get! ctx.spec).capBlockOperands := by
  simp only [Rewriter.initOpOperands.unfold]
  split
  · rfl
  · exact Rewriter.initOpOperands.loop_preserves_capBlockOperands ptr

protected buffed (inline := true)
def Rewriter.pushBlockOperandAtUnattachedSim (opPtr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (idx : UInt64) (blockPtr : Sim.BlockPtr) (opPtrInBounds : opPtr.InBounds ctx := by grind)
    (blockInBounds : blockPtr.InBounds ctx := by grind)
    (hidx : idx.toNat = opPtr.spec.getNumSuccessors! ctx.spec := by grind)
    (hcap : idx.toNat < (opPtr.spec.get! ctx.spec).capBlockOperands := by grind) :
    Sim.IRContext OpInfo :=
  let inputs : Erased ((s : IRContext OpInfo) × {p : OperationPtr × BlockPtr //
    p.1.InBounds s ∧ p.2.InBounds s}) :=
    .mk ⟨ctx.spec, (opPtr.spec, blockPtr.spec), opPtrInBounds.ib, blockInBounds.ib⟩
  ⟨Rewriter.setBlockOperand (OpInfo := OpInfo) opPtr.impl ctx.buf idx (by prove_setLinkBoundsOp ctx opPtr) (by prove_setLinkBoundsBlockOperandSlot ctx opPtr idx) blockPtr.impl,
    inputs.map (fun ⟨s, p⟩ => Rewriter.pushBlockOperand s p.val.1 p.val.2 p.property.1 p.property.2), by
      simp only [inputs, Erased.map_mk]
      exact
        Rewriter.setBlockOperand_pushBlockOperand_sim opPtr ctx idx blockPtr opPtrInBounds blockInBounds hidx hcap _ _⟩

@[grind .]
theorem Rewriter.pushBlockOperandAtUnattached_spec {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx blockPtr h₁ h₂ h₃ h₄} :
    (Rewriter.pushBlockOperandAtUnattached opPtr ctx idx blockPtr h₁ h₂ h₃ h₄).spec =
    Rewriter.pushBlockOperand ctx.spec opPtr.spec blockPtr.spec (by grind) (by grind) := by
  simp [Rewriter.pushBlockOperandAtUnattached.unfold, Sim.IRContext.spec]

@[grind .]
theorem Rewriter.pushBlockOperandAtUnattached_layoutUnchanged {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx blockPtr h₁ h₂ h₃ h₄} :
    (Rewriter.pushBlockOperandAtUnattached opPtr ctx idx blockPtr h₁ h₂ h₃ h₄).spec.LayoutUnchanged ctx.spec := by
  simp [Rewriter.pushBlockOperandAtUnattached.unfold]
  grind [Rewriter.pushBlockOperand]

@[grind =>]
theorem Rewriter.pushBlockOperandAtUnattached_veir_inBounds (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx blockPtr h₁ h₂ h₃ h₄} :
    ptr.InBounds (Rewriter.pushBlockOperandAtUnattached opPtr ctx idx blockPtr h₁ h₂ h₃ h₄).spec ↔
    (ptr.InBounds ctx.spec ∨
      ptr = .blockOperand (opPtr.spec.nextBlockOperand ctx.spec) ∨
      ptr = .blockOperandPtr (.blockOperandNextUse (opPtr.spec.nextBlockOperand ctx.spec))) := by
  simp [Rewriter.pushBlockOperandAtUnattached.unfold]
  grind [Rewriter.pushBlockOperand]

protected buffed (inline := true)
def Rewriter.pushBlockOperandAtSim (opPtr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (idx : UInt64) (blockPtr : Sim.BlockPtr) (opPtrInBounds : opPtr.InBounds ctx := by grind)
    (blockInBounds : blockPtr.InBounds ctx := by grind)
    (hidx : idx.toNat = opPtr.spec.getNumSuccessors! ctx.spec := by grind)
    (hcap : idx.toNat < (opPtr.spec.get! ctx.spec).capBlockOperands := by grind) :
    Sim.IRContext OpInfo :=
  let ctx := Rewriter.pushBlockOperandAtUnattached opPtr ctx idx blockPtr
  Sim.BlockOperandPtr.insertIntoCurrent ctx (opPtr.getBlockOperandPtr ctx idx (by grind))
    (by grind [Rewriter.pushBlockOperand]) (by grind)

@[grind =>]
theorem Rewriter.pushBlockOperandAt_inBounds (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx blockPtr h₁ h₂ h₃ h₄} :
    ptr.InBounds (Rewriter.pushBlockOperandAt opPtr ctx idx blockPtr h₁ h₂ h₃ h₄).spec ↔
    (ptr.InBounds ctx.spec ∨
      ptr = .blockOperand (opPtr.spec.nextBlockOperand ctx.spec) ∨
      ptr = .blockOperandPtr (.blockOperandNextUse (opPtr.spec.nextBlockOperand ctx.spec))) := by
  simp [Rewriter.pushBlockOperandAt.unfold]
  grind

@[grind .]
theorem Rewriter.pushBlockOperand_inBounds_mono (ptr : Sim.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx blockPtr h₁ h₂ h₃ h₄} :
    ptr.InBounds ctx → ptr.InBounds (Rewriter.pushBlockOperandAt opPtr ctx idx blockPtr h₁ h₂ h₃ h₄) := by
  simp [Rewriter.pushBlockOperandAt.unfold]
  grind

@[grind .]
theorem Rewriter.pushBlockOperand_fieldsInBounds {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx blockPtr h₁ h₂ h₃ h₄} :
    (Rewriter.pushBlockOperandAt opPtr ctx idx blockPtr h₁ h₂ h₃ h₄).spec.FieldsInBounds := by
  simp [Rewriter.pushBlockOperandAt.unfold]
  grind

set_option maxHeartbeats 1600000 in
buffed (inline := true)
def Rewriter.initBlockOperandsSim (opPtr: Sim.OperationPtr) (ctx: Sim.IRContext OpInfo)
    (operands : Array Sim.BlockPtr) (index : UInt64 := 0) (opPtrInBounds : opPtr.InBounds ctx := by grind)
    (hoperands : (∀ i (hi : i < operands.size), operands[i].InBounds ctx))
    (hidx : index.toNat = opPtr.spec.getNumSuccessors! ctx.spec := by grind)
    (hcap : operands.size ≤ (opPtr.spec.get! ctx.spec).capBlockOperands := by grind) :
    Sim.IRContext OpInfo :=
  have hsize : operands.size ≤ Buffed.countCard := by
    have := ctx.sim.repr.operations_indices opPtr.spec opPtrInBounds.ib |>.blockOperands
    grind
  if h : index.toNat >= operands.size then
    ctx
  else
    let valuePtr := operands[index.toNat]'(by omega)
    let ctx := Rewriter.pushBlockOperandAt opPtr ctx index valuePtr (by grind)
      (by grind [hoperands index.toNat (by grind [UInt64.le_iff_toNat_le])]) (by grind)
      (by grind [Array.usize_toUInt64_toNat, UInt64.le_iff_toNat_le])
    Rewriter.initBlockOperandsSim opPtr ctx operands (index + 1) (by grind [generic_ptr_grind])
      (by grind [generic_ptr_grind, Array.sizeU64_toNat]) (by
      have : (index + 1).toNat = index.toNat + 1 := by
        grind [unfold_pointers, UInt64.le_iff_toNat_le, Array.sizeU64_toNat]
      grind [Rewriter.pushBlockOperandAt.unfold, Rewriter.pushBlockOperand])
      (by
        grind [Rewriter.pushBlockOperandAt.unfold, Rewriter.pushBlockOperand])
  termination_by operands.size - index.toNat
  decreasing_by grind [Array.sizeU64_toNat, unfold_pointers, UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_inj, UInt64.toNat_mod_size]

@[grind .]
theorem Rewriter.initBlockOperands_fieldsInBounds {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {operands index h₁ h₂ h₃ h₄}
    (heq : initBlockOperands opPtr ctx operands index h₁ h₂ h₃ h₄ = ctx') :
    ctx.spec.FieldsInBounds → ctx'.spec.FieldsInBounds := by
  simp only [Rewriter.initBlockOperands.eq_sim] at *
  fun_induction Rewriter.initBlockOperandsSim <;> grind

@[grind .]
theorem Rewriter.initBlockOperands_inBounds_mono (ptr : Sim.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {operands index h₁ h₂ h₃ h₄}
    (heq : initBlockOperands opPtr ctx operands index h₁ h₂ h₃ h₄ = ctx') :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  simp only [Rewriter.initBlockOperands.eq_sim] at *
  fun_induction Rewriter.initBlockOperandsSim <;> grind

@[grind .]
theorem Rewriter.initBlockOperands_inBounds_mono' (ptr : Sim.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {operands index h₁ h₂ h₃ h₄} :
    ptr.InBounds ctx → ptr.InBounds (initBlockOperands opPtr ctx operands index h₁ h₂ h₃ h₄) := by
  simp only [Rewriter.initBlockOperands.eq_sim] at *
  fun_induction Rewriter.initBlockOperandsSim <;> grind

@[grind .]
theorem Rewriter.initBlockOperands_inBounds_veir_mono (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {operands index h₁ h₂ h₃ h₄} :
    ptr.InBounds ctx.spec → ptr.InBounds (initBlockOperands opPtr ctx operands index h₁ h₂ h₃ h₄).spec := by
  simp only [Rewriter.initBlockOperands.eq_sim] at *
  fun_induction Rewriter.initBlockOperandsSim <;> grind


set_option maxHeartbeats 4000000 in
buffed (inline := true)
def Rewriter.createOpSim (ctx: Sim.IRContext OpInfo) (opType: OpInfo)
    (resultTypes: Array TypeAttr) (operands: Array Sim.ValuePtr) (blockOperands : Array Sim.BlockPtr)
    (regions: Array Sim.RegionPtr) (properties: HasOpInfo.propertiesOf opType)
    (insertionPoint: Option InsertPoint)
    (hoper : (∀ i (hi : i < operands.size), operands[i].InBounds ctx))
    (hblockOperands : (∀ i (hi : i < blockOperands.size), blockOperands[i].InBounds ctx))
    (hregions : (∀ i (hi : i < regions.size), regions[i].InBounds ctx))
    (hins : insertionPoint.maybe InsertPoint.InBounds ctx.spec := by grind)
    (hrep : insertionPoint.maybe₁ InsertPoint.IsRepr := by grind)
    (htypes : resultTypes.size < 2^32)
    (_hx : ctx.spec.FieldsInBounds := by grind) : Option (Sim.IRContext OpInfo × Sim.OperationPtr) := do
    -- Pass the sizes via `Array.sizeU64` (an opaque, `@[irreducible]` `size.toUInt64` alias) so `grind` treats them (and their `.toNat`) as atoms rather than e-matching the `init*` lemmas at each `UInt64.ofNat _`/`size % 2^64` size, which otherwise cross-multiplies into a step-budget blow-up in the `insertionPoint`/`hcap` obligations below.
  let bound := 4294967295
  if hsize : operands.size ≥ bound ∨ blockOperands.size ≥ bound ∨ regions.size ≥ bound then none else
  rlet halloc : ⟨newOpPtr, ctx⟩ ← Sim.OperationPtr.allocFresh ctx opType properties
    resultTypes.sizeU64 operands.sizeU64 blockOperands.sizeU64 regions.sizeU64
    (by (try clear hoper hblockOperands hregions); grind [Array.sizeU64_toNat]) (by (try clear hoper hblockOperands hregions); grind [Array.sizeU64_toNat])
    (by (try clear hoper hblockOperands hregions); grind [Array.sizeU64_toNat]) (by (try clear hoper hblockOperands hregions); grind [Array.sizeU64_toNat])
  -- One attribute-table capacity check covers every result push below, so `initOpResults` runs
  -- `Option`-free; comparing against `attrTableMaxSize` keeps the check scalar (no GMP).
  if hattrs : Sim.OperationPtr.attrTableMaxSize < ctx.buf.attributes.size + resultTypes.size then none else
  have : newOpPtr.spec.getNumOperands! ctx.spec = 0 := by (try clear hoper hblockOperands hregions); grind
  have : newOpPtr.spec.getNumSuccessors! ctx.spec = 0 := by (try clear hoper hblockOperands hregions); grind
  have : newOpPtr.spec.getNumRegions! ctx.spec = 0 := by (try clear hoper hblockOperands hregions); grind
  have hins1 : insertionPoint.maybe InsertPoint.InBounds ctx.spec := by
    (try clear hoper hblockOperands hregions); grind [cases InsertPoint, Option.maybe_def]
  -- The freshly allocated operation records each array's size as its capacity; these named facts feed the `hcap` arguments of the `initOp*` calls below and are re-established (via the `initOp*_preserves_cap*` lemmas) after each call.
  have hcapResults : resultTypes.size ≤ (newOpPtr.spec.get! ctx.spec).capResults := by
    (try clear hoper hblockOperands hregions); grind [Array.sizeU64_toNat, Veir.Operation.empty]
  have hcapRegions : regions.size ≤ (newOpPtr.spec.get! ctx.spec).capRegions := by
    (try clear hoper hblockOperands hregions); grind [Array.sizeU64_toNat, Veir.Operation.empty]
  have hcapOperands : operands.size ≤ (newOpPtr.spec.get! ctx.spec).capOperands := by
    (try clear hoper hblockOperands hregions); grind [Array.sizeU64_toNat, Veir.Operation.empty]
  have hcapBlockOperands : blockOperands.size ≤ (newOpPtr.spec.get! ctx.spec).capBlockOperands := by
    (try clear hoper hblockOperands hregions); grind [Array.sizeU64_toNat, Veir.Operation.empty]
  -- Named obligations keep the `initOpResults` equation hypothesis small (fvar arguments instead
  -- of inlined proof terms), which the downstream `grind`s depend on to stay within budget.
  have hopN : newOpPtr.InBounds ctx := by (try clear hoper hblockOperands hregions); grind
  have hidxN : (0 : UInt64).toNat = newOpPtr.spec.getNumResults! ctx.spec := by (try clear hoper hblockOperands hregions); grind
  have hszN : resultTypes.size < UInt32.size := by (try clear hoper hblockOperands hregions); grind
  have hattrsN : ctx.buf.attributes.size + (resultTypes.size - (0 : UInt64).toNat) < UInt64.size := by
    (try clear hoper hblockOperands hregions); grind [Sim.OperationPtr.attrTableMaxSize_eq]
  rlet hResEq : ctx := (Rewriter.initOpResults newOpPtr ctx resultTypes 0 hopN hidxN hcapResults hszN hattrsN)
  have : newOpPtr.spec.getNumOperands! ctx.spec = 0 := by
    rw [Rewriter.initOpResults_preserves_numOperands newOpPtr.spec hResEq]
    (try clear hoper hblockOperands hregions); grind
  have : newOpPtr.spec.getNumSuccessors! ctx.spec = 0 := by
    rw [Rewriter.initOpResults_preserves_numSuccessors newOpPtr.spec hResEq]
    (try clear hoper hblockOperands hregions); grind
  have hins2 : insertionPoint.maybe InsertPoint.InBounds ctx.spec :=
    Rewriter.initOpResults_insertPoint_inBounds hResEq hins1
  have hcapRegions : regions.size ≤ (newOpPtr.spec.get! ctx.spec).capRegions := by
    have := Rewriter.initOpResults_preserves_capRegions newOpPtr.spec hResEq
    (try clear hoper hblockOperands hregions); grind
  have hcapOperands : operands.size ≤ (newOpPtr.spec.get! ctx.spec).capOperands := by
    have := Rewriter.initOpResults_preserves_capOperands newOpPtr.spec hResEq
    (try clear hoper hblockOperands hregions); grind
  have hcapBlockOperands : blockOperands.size ≤ (newOpPtr.spec.get! ctx.spec).capBlockOperands := by
    have := Rewriter.initOpResults_preserves_capBlockOperands newOpPtr.spec hResEq
    (try clear hoper hblockOperands hregions); grind
  have hopR : newOpPtr.InBounds ctx := by
    apply (Sim.GenericPtr.iff_operation _).mp
    exact Rewriter.initOpResults_inBounds_mono _ hResEq ((Sim.GenericPtr.iff_operation _).mpr hopN)
  rlet hRegEq : ctx ← Rewriter.initOpRegions newOpPtr ctx regions 0 (by (try clear hoper hblockOperands hregions); grind [generic_ptr_grind]) (by
    intro i hi
    have hp := hregions i hi
    clear hoper hblockOperands hregions
    (try clear hoper hblockOperands hregions); grind [generic_ptr_grind]) (by (try clear hoper hblockOperands hregions); grind) (by (try clear hoper hblockOperands hregions); grind) hcapRegions
  have : newOpPtr.spec.getNumSuccessors! ctx.spec = 0 := by
    rw [Rewriter.initOpRegions_preserves_numSuccessors _ hRegEq]
    assumption
  have hins3 : insertionPoint.maybe InsertPoint.InBounds ctx.spec := by
    rw [Option.maybe_def] at hins2 ⊢
    intro ip hip
    have hp := hins2 ip hip
    cases ip with
    | before op =>
      rw [InsertPoint.inBounds_before, ← GenericPtr.iff_operation] at hp ⊢
      exact Rewriter.initOpRegions_inBounds_veir_mono _ hp hRegEq
    | atEnd bl =>
      rw [InsertPoint.inBounds_atEnd, ← GenericPtr.iff_block] at hp ⊢
      exact Rewriter.initOpRegions_inBounds_veir_mono _ hp hRegEq
  have hcapOperands : operands.size ≤ (newOpPtr.spec.get! ctx.spec).capOperands := by
    have := Rewriter.initOpRegions_preserves_capOperands newOpPtr.spec (heq := by assumption)
    (try clear hoper hblockOperands hregions); grind
  have hcapBlockOperands : blockOperands.size ≤ (newOpPtr.spec.get! ctx.spec).capBlockOperands := by
    have := Rewriter.initOpRegions_preserves_capBlockOperands newOpPtr.spec (heq := by assumption)
    (try clear hoper hblockOperands hregions); grind
  -- One `getOperandsOffset` (a single `propertySizeOfEncoded` dispatch) per op; the operand loop
  -- then runs dispatch-free.
  have hNewOpInB : newOpPtr.InBounds ctx := by
    apply (Sim.GenericPtr.iff_operation _).mp
    exact Rewriter.initOpRegions_inBounds_mono _ ((Sim.GenericPtr.iff_operation _).mpr hopR) hRegEq
  rlet hOpOperands : ctx := Rewriter.initOpOperands newOpPtr ctx hNewOpInB operands (by
    intro i hi
    apply (Sim.GenericPtr.iff_value _).mp
    exact Rewriter.initOpRegions_inBounds_mono _
      (Rewriter.initOpResults_inBounds_mono _ hResEq
        (Sim.OperationPtr.allocFresh_genericPtr_mono _ halloc
          ((Sim.GenericPtr.iff_value _).mpr (hoper i hi)))) hRegEq) 0 (by
      rw [Rewriter.initOpRegions_preserves_numOperands _ hRegEq]
      grind only) hcapOperands
  -- Carry insertion-point bounds forward explicitly instead of re-exploring every intermediate context.
  have hins4 : insertionPoint.maybe InsertPoint.InBounds ctx.spec := by
    rw [Option.maybe_def]
    intro ip hip
    have hthis := hins3
    rw [Option.maybe_def] at hthis
    have hprev := hthis ip hip
    rw [← hOpOperands]
    cases ip with
    | before op =>
      rw [InsertPoint.inBounds_before, ← GenericPtr.iff_operation] at hprev ⊢
      exact Rewriter.initOpOperands_inBounds_veir_mono (.operation op) hprev
    | atEnd bl =>
      rw [InsertPoint.inBounds_atEnd, ← GenericPtr.iff_block] at hprev ⊢
      exact Rewriter.initOpOperands_inBounds_veir_mono (.block bl) hprev
  have : newOpPtr.spec.getNumSuccessors! ctx.spec = 0 := by
    rw [Rewriter.initOpOperands_preserves_numSuccessors! _ hOpOperands]
    assumption
  have hcapBlockOperands : blockOperands.size ≤ (newOpPtr.spec.get! ctx.spec).capBlockOperands := by
    (try clear hoper hblockOperands hregions); grind [Rewriter.initOpOperands_preserves_capBlockOperands]
  rlet hBlockOperands : ctx := Rewriter.initBlockOperands newOpPtr ctx blockOperands 0 (by (try clear hoper hblockOperands hregions); grind [generic_ptr_grind]) (by
    intro i hi
    apply (Sim.GenericPtr.iff_block _).mp
    exact Rewriter.initOpOperands_inBounds_mono _ hOpOperands
      (Rewriter.initOpRegions_inBounds_mono _
        (Rewriter.initOpResults_inBounds_mono _ hResEq
          (Sim.OperationPtr.allocFresh_genericPtr_mono _ halloc
            ((Sim.GenericPtr.iff_block _).mpr (hblockOperands i hi)))) hRegEq)) (by grind only) hcapBlockOperands
  have : insertionPoint.maybe InsertPoint.InBounds ctx.spec := by
    rw [Option.maybe_def]
    intro ip hip
    have hthis := hins4
    rw [Option.maybe_def] at hthis
    have hprev := hthis ip hip
    rw [← hBlockOperands]
    cases ip with
    | before op =>
      rw [InsertPoint.inBounds_before, ← GenericPtr.iff_operation] at hprev ⊢
      exact Rewriter.initBlockOperands_inBounds_veir_mono (.operation op) hprev
    | atEnd bl =>
      rw [InsertPoint.inBounds_atEnd, ← GenericPtr.iff_block] at hprev ⊢
      exact Rewriter.initBlockOperands_inBounds_veir_mono (.block bl) hprev
  match _ : insertionPoint with
  | some insertionPoint => do
    let ctx ← Rewriter.insertOp? ctx newOpPtr insertionPoint (by (try clear hoper hblockOperands hregions); grind [generic_ptr_grind]) (by (try clear hoper hblockOperands hregions); grind) (by (try clear hoper hblockOperands hregions); grind) (by (try clear hoper hblockOperands hregions); grind)
    some (ctx, newOpPtr)
  | none =>
    some (ctx, newOpPtr)


-- The `createOpSim` split-cascade proofs unfold the whole `createOpSim` body into `heq`, so their
-- cost scales with the body's (proof-)term size; they need more than the default budget.
set_option maxHeartbeats 4000000 in
@[grind .]
theorem Rewriter.createOp_inBounds_mono (ptr : GenericPtr)
    (heq : createOp ctx opType numResults operands blockOperands regions props ip h₁ h₂ h₃ h₄ h₅ h₆ = some (newCtx, newOp)) :
    ptr.InBounds ctx.spec → ptr.InBounds newCtx.spec := by
  intro hp
  simp only [createOp.unfold] at heq
  split at heq
  · contradiction
  ·
    split at heq
    · grind
    · rename_i newOpPtr ctx1 hAlloc
      split at heq
      -- Second split is now the hoisted attribute-capacity guard (`initOpResults` itself is
      -- `Option`-free, so its match reduces away).
      · grind
      · rename_i hattrs2
        have hp1 := (Veir.OperationPtr.allocEmptyAt_genericPtr_iff ptr
          (Sim.OperationPtr.allocFresh_spec' hAlloc)).mpr (.inl hp)
        split at heq
        · contradiction
        · rename_i ctx3 hReg
          have hp3 := Rewriter.initOpRegions_inBounds_veir_mono ptr
            (Rewriter.initOpResults_inBounds_veir_mono' ptr hp1) hReg
          split at heq
          · simp only [Option.bind_eq_bind, Option.bind] at heq
            split at heq
            · contradiction
            · rename_i ctxFinal hInsert
              obtain ⟨rfl, rfl⟩ := Option.some.inj heq
              apply (Rewriter.insertOp?_inBounds_veir_mono ptr hInsert).mpr
              exact Rewriter.initBlockOperands_inBounds_veir_mono ptr
                (Rewriter.initOpOperands_inBounds_veir_mono ptr hp3)
          · obtain ⟨rfl, rfl⟩ := Option.some.inj heq
            exact Rewriter.initBlockOperands_inBounds_veir_mono ptr
              (Rewriter.initOpOperands_inBounds_veir_mono ptr hp3)

-- The `createOp` split-cascade proofs unfold the whole `createOp createOpInner createOpSim` body into `heq`, so their
-- cost scales with the body's (proof-)term size; they need more than the default budget.
set_option maxHeartbeats 800000 in
@[grind .]
theorem Rewriter.createOp_new_inBounds (ptr : Sim.OperationPtr)
    (heq : createOp ctx opType numResults operands blockOperands regions props ip h₁ h₂ h₃ h₄ h₅ h₆ = some (newCtx, ptr)) :
    ptr.InBounds newCtx := by
  simp only [createOp.unfold] at heq
  split at heq
  · contradiction
  ·
    split at heq
    · grind
    · split at heq
      · grind
      · split at heq
        · grind
        · split at heq
          · simp only [Option.bind_eq_bind, Option.bind] at heq
            split at heq <;> grind
          · grind

-- The `createOp` split-cascade proofs unfold the whole `createOp createOpInner createOpSim` body into `heq`, so their
-- cost scales with the body's (proof-)term size; they need more than the default budget.
set_option maxHeartbeats 800000 in
@[grind .]
theorem Rewriter.createOp_new_not_inBounds (ptr : Sim.OperationPtr)
    (heq : createOp ctx opType numResults operands blockOperands regions props ip h₁ h₂ h₃ h₄ h₅ h₆ = some (newCtx, ptr)) :
    ¬ ptr.spec.InBounds ctx.spec := by
  simp only [createOp.unfold] at heq
  split at heq
  · contradiction
  · split at heq
    · grind
    · rename_i newOpPtr ctx1 hAlloc
      split at heq
      · grind
      · split at heq
        · grind
        · split at heq
          · simp only [Option.bind_eq_bind, Option.bind] at heq
            grind
          · grind

-- The `createOp` split-cascade proofs unfold the whole `createOp createOpInner createOpSim` body into `heq`, so their
-- cost scales with the body's (proof-)term size; they need more than the default budget.
set_option maxHeartbeats 800000 in
@[grind .]
theorem Rewriter.createOp_fieldsInBounds
    (_heq : createOp ctx opType numResults operands blockOperands numRegions props ip h₁ h₂ h₃ h₄ h₅ h₆ = some (newCtx, newOp)) :
    ctx.spec.FieldsInBounds → newCtx.spec.FieldsInBounds := by
  intro _
  exact newCtx.sim.fieldsInBounds

buffed (inline := true)
def Sim.IRContext.emptySim : Sim.IRContext OpInfo :=
  -- Slot 0 of the attribute table is reserved for the emptySim dictionary (see `Sim.attr_empty`).
  ⟨⟨.emptyWithCapacity (256 * 1024 * 1024), #[.dictionaryAttr DictionaryAttr.empty]⟩, .mk (Veir.IRContext.empty OpInfo), by
    constructor <;> grind [TopLevelPtr]⟩

buffed (inline := true)
def IRContext.createSim OpInfo [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo] : Option (Sim.IRContext OpInfo × Sim.OperationPtr) := do
  rlet ⟨ctx, region⟩ ← Rewriter.createRegion .empty
  have regionIb : region.InBounds ctx := by grind
  have regionRepr : region.spec.IsRepr := by grind
  rlet hCreateOp : ⟨ctx, operation⟩ ← Rewriter.createOp ctx HasOpInfo.moduleOpCode #[] #[]
    #[] #[region]
    default none (by simp)
    (by simp)
    (by simpa using regionIb)
    (by grind) (by grind) (by grind)
  have regionIb : region.InBounds ctx :=
    ⟨regionIb.sim, Rewriter.createOp_inBounds_mono (.region region.spec) hCreateOp regionIb.ib⟩
  rlet ⟨ctx, block⟩ ← Rewriter.createBlock ctx #[] (some (.atEnd ⟨region.impl.toNat⟩)) (by
    simp only [Option.maybe_def, Veir.BlockInsertPoint.inBounds_def]
    rw [← regionIb.sim.out]
    simp only [RegionPtr.toM]
    simp [show region.spec.toFlat.toUInt64.toNat = region.spec.toFlat by grind]
    exact regionIb.ib) (by grind [Veir.RegionPtr.toFlat, Veir.RegionPtr.toM])
  some (ctx, operation)

@[grind →]
theorem IRContext.create_fieldsInBounds {op: Sim.OperationPtr} (_h : IRContext.create OpInfo = some (ctx, op)) :
    ctx.spec.FieldsInBounds := by
  simp only [IRContext.create.unfold] at _h; grind

@[grind →]
theorem IRContext.create_inBounds {op: Sim.OperationPtr} (h : IRContext.create OpInfo = some (ctx, op)) :
    op.InBounds ctx := by
  simp only [IRContext.create.unfold] at h
  split at h
  · grind
  · split at h
    · grind
    · rename_i operation hOp
      split at h
      · grind
      · rename_i hBlock
        have hop := Rewriter.createOp_new_inBounds operation hOp
        have hb := Rewriter.createBlock_inBounds_mono (.fromOperation operation) hBlock
          ((Sim.GenericPtr.iff_operation _).mpr hop)
        obtain ⟨rfl, rfl⟩ := Option.some.inj h
        exact (Sim.GenericPtr.iff_operation _).mp hb

-- Only the base Lean axioms are used:
#print axioms Rewriter.createOp
#print axioms IRContext.create
#print axioms Rewriter.replaceOp?
#print axioms Rewriter.replaceValue?
