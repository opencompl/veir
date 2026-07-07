module

public import ExArray.CompilerExtras
public import Veir.IR
public import Veir.Rewriter.InsertPoint
public import Veir.Rewriter.LinkedList.Basic
public import Veir.Rewriter.LinkedList.GetSet

meta import Veir.IR.Buffed.Basic
import Veir.IR.Buffed.RawAccessorsLemmas
import Veir.IR.Buffed.Meta
import Veir.IR.Buffed.InBounds
import Veir.Rewriter.LinkedList.LayoutUnchanged
import all Veir.Rewriter.LinkedList.Basic

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
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

/--
- Insert an operation at a given location.
-/
buffed
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
  simp only [insertOp?_def, insertOp?Sim] at heq
  grind

theorem Rewriter.insertOp?_inBounds_mono (ptr : Sim.GenericPtr)
    (heq : insertOp? ctx newOp ip h₁ h₂ h₃ h₄ = some newCtx) :
    ptr.InBounds newCtx ↔ ptr.InBounds ctx := by
  simp only [insertOp?_def, insertOp?Sim] at heq
  grind

grind_pattern Rewriter.insertOp?_inBounds_mono =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, ptr.InBounds newCtx

theorem Rewriter.insertOp?_sim_inBounds_mono (ptr : Sim.GenericPtr)
    (heq : insertOp? ctx newOp ip h₁ h₂ h₃ h₄ = some newCtx) :
    ptr.InBounds newCtx ↔ ptr.InBounds ctx := by
  simp only [insertOp?_def, insertOp?Sim] at heq
  grind

grind_pattern Rewriter.insertOp?_sim_inBounds_mono =>
  Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃, some newCtx, ptr.InBounds newCtx

set_option linter.unusedVariables false in -- spurious
@[grind .]
theorem Rewriter.insertOp?_fieldsInBounds_mono
    (heq : insertOp? ctx newOp ip h₁ h₂ h₃ h₄ = some newCtx) :
    ctx.spec.FieldsInBounds → newCtx.spec.FieldsInBounds := by
  simp only [insertOp?_def, insertOp?Sim] at heq
  grind

/--
  Set the parent, previous, and next operation pointers of an operation to `none`.
  This method should not be used from outside the rewriter, and is only used to
  make proofs easier for grind.
-/
buffed
def Rewriter.unsetParentAndNeighborsSim (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr) (hIn : op.InBounds ctx) :=
  let ctx := op.setParent ctx .none (by grind) (by grind)
  let ctx := op.setPrevOp ctx .none (by grind) (by grind)
  op.setNextOp ctx .none (by grind) (by grind)

@[grind =]
theorem Rewriter.unsetParentAndNeighbors_inBounds (ptr : Sim.GenericPtr) :
    ptr.InBounds (unsetParentAndNeighbors ctx op hIn) ↔ ptr.InBounds ctx := by
  simp only [unsetParentAndNeighbors_def, unsetParentAndNeighborsSim]
  grind

@[grind . ]
theorem Rewriter.unsetParentAndNeighbors_fieldsInBounds :
    (unsetParentAndNeighbors ctx op hIn).spec.FieldsInBounds := by
  simp only [unsetParentAndNeighbors_def, unsetParentAndNeighborsSim]
  grind

buffed
def Rewriter.detachOpSim (ctx: Sim.IRContext OpInfo) (op: Sim.OperationPtr) (hctx : ctx.spec.FieldsInBounds)
    (hIn : op.InBounds ctx) (hasParent: (op.getParent ctx hIn).toOption.isSome) : Sim.IRContext OpInfo :=
  let prevOp := op.getPrevOp ctx (by grind)
  let nextOp := op.getNextOp ctx (by grind)
  let parent := (op.getParent ctx (by grind)).toOption.get hasParent
  let ctx := unsetParentAndNeighbors ctx op hIn
  have : parent.InBounds ctx := by grind [generic_ptr_grind]
  -- I had to duplicate the continuation in each branch, I don't really
  -- know why the proofs of the preconditions in, say, `setNextOp` were
  -- metavariable... maybe somehow the execution of the tactics is slightly
  -- delayed?
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
        have : (∀ ptr, nextOp.toOption = some ptr → ptr.InBounds ctx) → nextOp.InBounds ctx := by grind
        grind [generic_ptr_grind])
      match _ : nextOp.toOption with
      | some nextOp => nextOp.setPrevOp ctx prevOp (by grind) (by grind)
      | none => parent.setLastOp ctx prevOp (by grind) (by grind)

@[grind .]
theorem Rewriter.detachOp_inBounds (ptr : Sim.GenericPtr) :
    ptr.InBounds (detachOp ctx hctx op hIn hasParent) ↔ ptr.InBounds ctx := by
  grind (gen := 20) [detachOp_def, detachOpSim]

@[grind .]
theorem Rewriter.detachOp_fieldsInBounds (hctx : ctx.spec.FieldsInBounds) :
    (detachOp ctx op hctx hIn hasParent).spec.FieldsInBounds := by
  grind [detachOp_def, detachOpSim]

@[grind =]
theorem Rewriter.detachOp_preserves_numOperands (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    op'.getNumOperands! (detachOp ctx op hctx hIn hPar).spec = op'.getNumOperands! ctx.spec := by
  simp [detachOp_def, detachOpSim]
  split <;> grind [unsetParentAndNeighbors_def, unsetParentAndNeighborsSim]

@[grind =]
theorem Rewriter.detachOp_preserves_capOperands (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    (op'.get! (detachOp ctx op hctx hIn hPar).spec).capOperands = (op'.get! ctx.spec).capOperands := by
  simp [detachOp_def, detachOpSim]
  split <;> grind (instances := 2000) [unsetParentAndNeighbors_def, unsetParentAndNeighborsSim]

@[grind =]
theorem Rewriter.detachOp_preserves_numSuccessors (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    op'.getNumSuccessors! (detachOp ctx op hctx hIn hPar).spec = op'.getNumSuccessors! ctx.spec := by
  simp [detachOp_def, detachOpSim]
  split <;> grind [unsetParentAndNeighbors_def, unsetParentAndNeighborsSim]

@[grind =]
theorem Rewriter.detachOp_preserves_capBlockOperands (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    (op'.get! (detachOp ctx op hctx hIn hPar).spec).capBlockOperands = (op'.get! ctx.spec).capBlockOperands := by
  simp [detachOp_def, detachOpSim]
  split <;> grind (instances := 2000) [unsetParentAndNeighbors_def, unsetParentAndNeighborsSim]

/--
  Detach an operation from its parent if it has one.
  If it has no parent, return the context unchanged.
-/
buffed
def Rewriter.detachOpIfAttachedSim (ctx: Sim.IRContext OpInfo) (op: Sim.OperationPtr)
    (hctx : ctx.spec.FieldsInBounds := by grind)
    (hop : op.InBounds ctx := by grind) : Sim.IRContext OpInfo :=
  match h: (op.getParent ctx hop).toOption with
  | some _ => Rewriter.detachOp ctx op hctx hop (by grind)
  | none => ctx

@[grind .]
theorem Rewriter.detachOpIfAttached_inBounds (ptr : Sim.GenericPtr) :
    ptr.InBounds (detachOpIfAttached ctx op h₁ h₂) ↔ ptr.InBounds ctx := by
  grind [detachOpIfAttached_def, detachOpIfAttachedSim]

@[grind .]
theorem Rewriter.detachOpIfAttached_fieldsInBounds (hctx : ctx.spec.FieldsInBounds) :
    (detachOpIfAttached ctx op hctx hIn).spec.FieldsInBounds := by
  grind [detachOpIfAttached_def, detachOpIfAttachedSim]

@[simp, grind =]
theorem Rewriter.detachOpIfAttached_preserves_numOperands (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    op'.getNumOperands! (detachOpIfAttached ctx op hctx hIn).spec = op'.getNumOperands! ctx.spec := by
  grind [detachOpIfAttached_def, detachOpIfAttachedSim]

@[simp, grind =]
theorem Rewriter.detachOpIfAttached_preserves_capOperands (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    (op'.get! (detachOpIfAttached ctx op hctx hIn).spec).capOperands = (op'.get! ctx.spec).capOperands := by
  grind [detachOpIfAttached_def, detachOpIfAttachedSim]

@[simp, grind =]
theorem Rewriter.detachOpIfAttached_preserves_numSuccessors (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    op'.getNumSuccessors! (detachOpIfAttached ctx op hctx hIn).spec = op'.getNumSuccessors! ctx.spec := by
  grind [detachOpIfAttached_def, detachOpIfAttachedSim]

@[simp, grind =]
theorem Rewriter.detachOpIfAttached_preserves_capBlockOperands (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    (op'.get! (detachOpIfAttached ctx op hctx hIn).spec).capBlockOperands = (op'.get! ctx.spec).capBlockOperands := by
  grind [detachOpIfAttached_def, detachOpIfAttachedSim]

buffed
def Rewriter.detachOperands.loopSim (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr) (index : UInt64)
    (hCtx : ctx.spec.FieldsInBounds := by grind)
    (hOp : op.InBounds ctx := by grind)
    (hIndex : index.toNat < op.spec.getNumOperands! ctx.spec := by grind) : Sim.IRContext OpInfo :=
  let ctx' := (op.getOperandPtr ctx index (by grind)).removeFromCurrent ctx (by grind) (by grind)
  if hz : index = 0 then ctx' else
  Rewriter.detachOperands.loopSim ctx' op (index-1) (by grind) (by grind) (by grind)
termination_by index.toNat
decreasing_by
  · have := @UInt64.toNat_inj index 0
    grind

@[grind .]
theorem Rewriter.detachOperands.loop_inBounds (ptr : Sim.GenericPtr) :
    ptr.InBounds (detachOperands.loop ctx op index hCtx hOp hIndex) ↔ ptr.InBounds ctx := by
  simp [loop_def]
  fun_induction loopSim <;> grind

@[grind .]
theorem Rewriter.detachOperands.loop_fieldsInBounds :
    ctx.spec.FieldsInBounds → (detachOperands.loop ctx op index hCtx hOp hIndex).spec.FieldsInBounds := by
  simp [loop_def]
  fun_induction loopSim <;> grind

@[simp, grind =]
theorem Rewriter.detachOperands.loop_preserves_numSuccessors (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    op'.getNumSuccessors! (detachOperands.loop ctx op idx hctx hOp hIndex).spec = op'.getNumSuccessors! ctx.spec := by
  simp [loop_def]
  fun_induction loopSim <;> grind

@[simp, grind =]
theorem Rewriter.detachOperands.loop_preserves_capSuccessors (hctx : ctx.spec.FieldsInBounds) {op' : Veir.OperationPtr} :
    (op'.get! (detachOperands.loop ctx op idx hctx hOp hIndex).spec).capBlockOperands = (op'.get! ctx.spec).capBlockOperands := by
  simp [loop_def]
  fun_induction loopSim <;> grind

buffed
def Rewriter.detachOperandsSim (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hCtx : ctx.spec.FieldsInBounds := by grind)
    (hOp : op.InBounds ctx := by grind)
    (hcap : (op.spec.get! ctx.spec).capOperands = op.spec.getNumOperands! ctx.spec) : Sim.IRContext OpInfo :=
  let numOperands := op.getNumOperands ctx (by grind)
  if hz : numOperands = 0 then
    ctx
  else
    Rewriter.detachOperands.loop ctx op (numOperands - 1) (by grind) (by grind)
    (by grind [ UInt64.toNat_mod_size, UInt64.toNat_sub, UInt64.le_iff_toNat_le,
    UInt64.toNat_ofNat, UInt64.toNat_ofNat_of_lt, UInt64.toNat_lt])

@[grind .]
theorem Rewriter.detachOperands_inBounds (ptr : Sim.GenericPtr) :
    ptr.InBounds (detachOperands ctx op hCtx hOp hCap) ↔ ptr.InBounds ctx := by
  grind [detachOperands_def, detachOperandsSim]

@[grind .]
theorem Rewriter.detachOperands_fieldsInBounds :
    ctx.spec.FieldsInBounds → (detachOperands ctx op hCtx hOp hCap).spec.FieldsInBounds := by
  grind [detachOperands_def, detachOperandsSim]

buffed
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
  simp [loop_def]
  fun_induction loopSim <;> grind

@[grind .]
theorem Rewriter.detachBlockOperands.loop_fieldsInBounds :
    ctx.spec.FieldsInBounds → (detachBlockOperands.loop ctx op index hCtx hOp hIndex).spec.FieldsInBounds := by
  simp [loop_def]
  fun_induction loopSim <;> grind

buffed
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
  grind [detachBlockOperands_def, detachBlockOperandsSim]

@[grind .]
theorem Rewriter.detachBlockOperands_fieldsInBounds :
    ctx.spec.FieldsInBounds → (detachBlockOperands ctx op hCtx hOp hCap).spec.FieldsInBounds := by
  grind [detachBlockOperands_def, detachBlockOperandsSim]

buffed
def Rewriter.eraseOpSim (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr)
    (hCtx : ctx.spec.FieldsInBounds := by grind)
    (hOp : op.InBounds ctx := by grind)
    (hOpers : (op.spec.get! ctx.spec).capOperands = op.spec.getNumOperands! ctx.spec)
    (hBlOpers : (op.spec.get! ctx.spec).capBlockOperands = op.spec.getNumSuccessors! ctx.spec) : Sim.IRContext OpInfo :=
  let ctx := Rewriter.detachOpIfAttached ctx op
  let ctx := Rewriter.detachOperands ctx op (by grind) (by grind [generic_ptr_grind]) (by grind)
  let ctx := Rewriter.detachBlockOperands ctx op (by grind) (by grind [generic_ptr_grind]) (by grind [detachOperands_def, detachOperandsSim])
  ctx
  -- op.dealloc ctx

/-
Remark: the fact that `eraseOp` preserves `FieldsInBounds` relies on the fact
that the context is well formed.  Indeed, it is true because the only pointers
to the operands are in the doubly linked list that we patch.  I think in
addition we need to know that the results of the operation we are removing are
never used, which is ensured in the call to `eraseOp` in `replaceOp?` below for
example.
-/

/--
- Insert a block at a given location.
-/
buffed
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
  simp only [insertBlock?_def, insertBlock?Sim] at heq
  grind

@[grind .]
theorem Rewriter.insertBlock?_fieldsInBounds_mono
    (heq : insertBlock? ctx newBlock ip h₁ h₂ h₃ h₄ = some newCtx) :
    ctx.spec.FieldsInBounds → newCtx.spec.FieldsInBounds := by
  simp only [insertBlock?_def, insertBlock?Sim] at heq
  grind

buffed
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
  grind [replaceUse_def, replaceUseSim]

@[grind .]
theorem Rewriter.replaceUse_fieldsInBounds :
     ctx.spec.FieldsInBounds → (replaceUse ctx use newValue useIn newIn ctxIn).spec.FieldsInBounds := by
  grind [replaceUse_def, replaceUseSim]

buffed
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
  simp [replaceValue?_def]
  fun_induction replaceValue?Sim <;> grind [replaceUse, replaceUseSim, replaceUseSpec]

@[grind =>]
theorem Rewriter.replaceValue?_inBounds (ptr : Sim.GenericPtr) :
    replaceValue? ctx old new h₁ h₂ h₃ d = some ctx' →
    (ptr.InBounds ctx ↔ ptr.InBounds ctx') := by
  simp [replaceValue?_def]
  fun_induction replaceValue?Sim <;> grind

@[grind .]
theorem Rewriter.replaceValue?_fieldsInBounds :
     ctx.spec.FieldsInBounds → (replaceValue? ctx old new h₁ h₂ h₃ d).maybe₁ (·.spec.FieldsInBounds) := by
  simp [replaceValue?_def]
  fun_induction replaceValue?Sim <;> grind

@[grind .]
theorem Rewriter.replaceValue?_preserves_results_size (op : Sim.OperationPtr) (hop : op.InBounds ctx) :
    replaceValue? ctx old new h₁ h₂ h₃ d = some ctx' →
    op.spec.getNumResults! ctx'.spec = op.spec.getNumResults! ctx.spec := by
  simp [replaceValue?_def]
  fun_induction replaceValue?Sim <;> grind [Rewriter.replaceUse_def, Rewriter.replaceUseSim]

@[grind .]
theorem Rewriter.replaceValue?_preserves_parent' (op : Sim.OperationPtr) (hop : op.InBounds ctx)
    (hctx' : replaceValue? ctx old new h₁ h₂ h₃ d = some ctx') :
    (op.spec.get! ctx'.spec).parent = (op.spec.get! ctx.spec).parent := by
  simp [replaceValue?_def] at hctx'
  fun_induction replaceValue?Sim <;> grind [Rewriter.replaceUse_def, Rewriter.replaceUseSim]

@[grind .]
theorem Rewriter.replaceValue?_preserves_parent (op : Sim.OperationPtr) (hop : op.InBounds ctx)
    (hctx' : replaceValue? ctx old new h₁ h₂ h₃ d = some ctx') :
    (op.spec.get! ctx'.spec).parent = (op.spec.get! ctx.spec).parent := by
  simp [replaceValue?_def] at hctx'
  fun_induction replaceValue?Sim <;> grind [Rewriter.replaceUse_def, Rewriter.replaceUseSim]

@[grind .]
theorem Rewriter.replaceValue?_preserves_numOperands (op : Sim.OperationPtr) (hop : op.InBounds ctx) :
    replaceValue? ctx old new h₁ h₂ h₃ d = some ctx' →
    op.spec.getNumOperands! ctx'.spec = op.spec.getNumOperands! ctx.spec := by
  simp [replaceValue?_def]
  fun_induction replaceValue?Sim <;> grind [Rewriter.replaceUse_def, Rewriter.replaceUseSim]

@[grind .]
theorem Rewriter.replaceValue?_preserves_capOperands (op : Sim.OperationPtr) (hop : op.InBounds ctx) :
    replaceValue? ctx old new h₁ h₂ h₃ d = some ctx' →
    (op.spec.get! ctx'.spec).capOperands = (op.spec.get! ctx.spec).capOperands := by
  simp [replaceValue?_def]
  fun_induction replaceValue?Sim <;> grind [Rewriter.replaceUse_def, Rewriter.replaceUseSim]

@[grind .]
theorem Rewriter.replaceValue?_preserves_numSuccessors (op : Sim.OperationPtr) (hop : op.InBounds ctx) :
    replaceValue? ctx old new h₁ h₂ h₃ d = some ctx' →
    op.spec.getNumSuccessors! ctx'.spec = op.spec.getNumSuccessors! ctx.spec := by
  simp [replaceValue?_def]
  fun_induction replaceValue?Sim <;> grind [Rewriter.replaceUse_def, Rewriter.replaceUseSim]

@[grind .]
theorem Rewriter.replaceValue?_preserves_capBlockOperands (op : Sim.OperationPtr) (hop : op.InBounds ctx) :
    replaceValue? ctx old new h₁ h₂ h₃ d = some ctx' →
    (op.spec.get! ctx'.spec).capBlockOperands = (op.spec.get! ctx.spec).capBlockOperands := by
  simp [replaceValue?_def]
  fun_induction replaceValue?Sim <;> grind [Rewriter.replaceUse_def, Rewriter.replaceUseSim]

buffed
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
  simp [replaceOpResults_def]
  fun_induction replaceOpResultsSim <;> grind [Rewriter.replaceUse_def, Rewriter.replaceUseSim]

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
  simp [replaceOpResults_def]
  fun_induction replaceOpResultsSim <;> grind [Rewriter.replaceUse_def, Rewriter.replaceUseSim]

@[grind .]
theorem Rewriter.replaceOpResults_preserves_numOperands (op : Sim.OperationPtr) (hop : op.InBounds ctx) :
    replaceOpResults ctx fromOp toOp index fromOpIB toOpIB hNumFrom hNumTo ctxInBounds = some newCtx →
    op.spec.getNumOperands! newCtx.spec = op.spec.getNumOperands! ctx.spec := by
  simp [replaceOpResults_def]
  fun_induction replaceOpResultsSim <;> grind [generic_ptr_grind]

@[grind .]
theorem Rewriter.replaceOpResults_preserves_capOperands (op : Sim.OperationPtr) (hop : op.InBounds ctx) :
    replaceOpResults ctx fromOp toOp index fromOpIB toOpIB hNumFrom hNumTo ctxInBounds = some newCtx →
    (op.spec.get! newCtx.spec).capOperands = (op.spec.get! ctx.spec).capOperands := by
  simp [replaceOpResults_def]
  fun_induction replaceOpResultsSim <;> grind [generic_ptr_grind]

@[grind .]
theorem Rewriter.replaceOpResults_preserves_numSuccessors (op : Sim.OperationPtr) (hop : op.InBounds ctx) :
    replaceOpResults ctx fromOp toOp index fromOpIB toOpIB hNumFrom hNumTo ctxInBounds = some newCtx →
    op.spec.getNumSuccessors! newCtx.spec = op.spec.getNumSuccessors! ctx.spec := by
  simp [replaceOpResults_def]
  fun_induction replaceOpResultsSim <;> grind [generic_ptr_grind]

@[grind .]
theorem Rewriter.replaceOpResults_preserves_capBlockOperands (op : Sim.OperationPtr) (hop : op.InBounds ctx) :
    replaceOpResults ctx fromOp toOp index fromOpIB toOpIB hNumFrom hNumTo ctxInBounds = some newCtx →
    (op.spec.get! newCtx.spec).capBlockOperands = (op.spec.get! ctx.spec).capBlockOperands := by
  simp [replaceOpResults_def]
  fun_induction replaceOpResultsSim <;> grind [generic_ptr_grind]

buffed
def Rewriter.replaceOp?Sim (ctx: Sim.IRContext OpInfo) (oldOp newOp: Sim.OperationPtr)
    (oldIn: oldOp.InBounds ctx := by grind)
    (newIn: newOp.InBounds ctx := by grind)
    (ctxIn: ctx.spec.WellFormed := by grind)
    (_hpar : (oldOp.spec.get! ctx.spec).parent.isSome = true)
    (wf : ctx.spec.WellFormed) : Option (Sim.IRContext OpInfo) := do
  let numOldResults := oldOp.getNumResults ctx (by grind)
  let numNewResults := newOp.getNumResults ctx (by grind)
  if h : numOldResults ≠ numNewResults then
    none
  else
    rlet newCtx ← replaceOpResults ctx oldOp newOp numOldResults (by grind) (by grind) (by grind [
      UInt64.toNat_mod_size, UInt64.toNat_ofNat, UInt64.toNat_ofNat_of_lt, UInt64.toNat_lt]) (by grind [
        UInt64.toNat_mod_size, UInt64.toNat_ofNat, UInt64.toNat_ofNat_of_lt, UInt64.toNat_lt]) (by grind)
    eraseOp newCtx oldOp (by grind) (by grind [generic_ptr_grind]) (by
      rename_i h
      have := wf.operations oldOp.spec
      have := replaceOpResults_preserves_capOperands oldOp (by grind) h
      have := replaceOpResults_preserves_numOperands oldOp (by grind) h
      grind) (by
      rename_i h
      have := wf.operations oldOp.spec
      have := replaceOpResults_preserves_capBlockOperands oldOp (by grind) h
      have := replaceOpResults_preserves_numSuccessors oldOp (by grind) h
      grind)

-- TODO: for now `pushBlockArgument` only works in the specification world,
-- because the buffed implementation does not handle changing the size of the
-- argument array.
protected def Rewriter.pushBlockArgument (ctx : IRContext OpInfo) (blockPtr : BlockPtr) (type : TypeAttr)
    (blockPtrInBounds : blockPtr.InBounds ctx := by grind) : IRContext OpInfo :=
  let index := blockPtr.getNumArguments ctx (by grind)
  let argument := { type := type, firstUse := none, index := index, loc := (), owner := blockPtr : BlockArgument }
  blockPtr.pushArgument ctx argument (by grind)

@[inline]
protected def Rewriter.setBlockArgument (blockPtr : Buffed.BlockMPtr) (ctx₀ : Buffed.IRBufContext OpInfo) (idx : UInt64)
    (hslot : (blockPtr.getArgumentPtr idx).toNat + Buffed.BlockArgument.size.toNat ≤ ctx₀.size)
    (type : TypeAttr) : Option (Buffed.IRBufContext OpInfo) :=
  let arg := blockPtr.getArgumentPtr idx
  rlet hattr : (ctx, typeIdx) ← ctx₀.insertAttrs type
  have hsz : ctx.size = ctx₀.size := ctx₀.insertAttrs_size hattr
  let ctx := arg.writeType ctx typeIdx (by prove_setSlotBounds ctx₀)
  let ctx := arg.writeFirstUse ctx .none (by prove_setSlotBounds ctx₀)
  let ctx := arg.writeIndex ctx idx (by prove_setSlotBounds ctx₀)
  let ctx := arg.writeOwner ctx blockPtr (by prove_setSlotBounds ctx₀)
  some ctx

protected buffed
def Rewriter.pushBlockArgumentAtSim (blockPtr : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo)
    (idx : UInt64) (type : TypeAttr) (ib : blockPtr.InBounds ctx) (hidx : idx.toNat = blockPtr.spec.getNumArguments! ctx.spec) :
    Option (Sim.IRContext OpInfo) := do
  some ⟨← Rewriter.setBlockArgument blockPtr.impl ctx.buf idx (by sorry) type, Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind), admitted_sim ib⟩

@[grind .]
theorem Rewriter.pushBlockArgumentAt_spec :
    (Rewriter.pushBlockArgumentAt blockPtr ctx idx type ib hidx) = some ctx' →
    ctx'.spec = Rewriter.pushBlockArgument ctx.spec blockPtr.spec type (by grind) := by
  simp [pushBlockArgumentAt_def, Rewriter.pushBlockArgumentAtSim, Option.bind]
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
    {ctx ctx' : Sim.IRContext OpInfo} {ib} {hidx}
    (heq : Rewriter.pushBlockArgumentAt blockPtr ctx idx type ib hidx = some ctx') :
    ctx'.spec.LayoutUnchanged ctx.spec := by
  grind [pushBlockArgumentAt_spec heq, Rewriter.pushBlockArgument]

@[grind <=]
theorem Rewriter.pushBlockArgumentAt_veir_inBounds {ptr : Veir.GenericPtr} {blockPtr : Sim.BlockPtr}
    {ctx : Sim.IRContext OpInfo} {ib hidx}
    (heq : Rewriter.pushBlockArgumentAt blockPtr ctx idx type ib hidx = some ctx') :
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

@[grind .]
theorem Rewriter.pushBlockArgumentAt_fieldsInBounds {blockPtr : Sim.BlockPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {ib} {hidx}
    (heq : Rewriter.pushBlockArgumentAt blockPtr ctx idx type ib hidx = some ctx') :
    ctx.spec.FieldsInBounds → ctx'.spec.FieldsInBounds := by
  simp [Rewriter.pushBlockArgumentAt] at heq
  grind

/-! ## Buffer helpers writing into the preallocated operation arrays.

Like `setBlockArgument`, these write a single entry into the (already allocated) result/operand/
block-operand array of an operation, at a given index. They do not grow the array. -/

@[inline]
protected def Rewriter.setResult (opPtr : Buffed.OperationMPtr) (ctx₀ : Buffed.IRBufContext OpInfo) (idx : UInt64)
    (hnum : (opPtr + Buffed.Operation.Offsets.numResults).toInt + Buffed.Operation.Sizes.numResults.toInt ≤ ctx₀.size)
    (hslot : (opPtr.getResultPtr ctx₀ idx hnum).toNat + Buffed.OpResult.size.toNat ≤ ctx₀.size)
    (type : TypeAttr) : Option (Buffed.IRBufContext OpInfo) :=
  let res := opPtr.getResultPtr ctx₀ idx hnum
  rlet hattr : (ctx, typeIdx) ← ctx₀.insertAttrs type
  have hsz : ctx.size = ctx₀.size := ctx₀.insertAttrs_size hattr
  let ctx := res.writeType ctx typeIdx (by prove_setSlotBounds ctx₀)
  let ctx := res.writeFirstUse ctx .none (by prove_setSlotBounds ctx₀)
  let ctx := res.writeIndex ctx idx (by prove_setSlotBounds ctx₀)
  let ctx := res.writeOwner ctx opPtr (by prove_setSlotBounds ctx₀)
  some ctx

@[inline]
protected def Rewriter.setOperand (opPtr : Buffed.OperationMPtr) (ctx₀ : Buffed.IRBufContext OpInfo) (idx : UInt64)
    (hnum : (opPtr + Buffed.Operation.Offsets.opType).toInt + Buffed.Operation.Sizes.opType.toInt ≤ ctx₀.size)
    (hslot : (opPtr + opPtr.computeOperandOffset ctx₀ idx hnum).toNat + Buffed.OpOperand.size.toNat ≤ ctx₀.size)
    (value : Buffed.ValueImplMPtr) : Buffed.IRBufContext OpInfo :=
  let oper : Buffed.OpOperandMPtr := opPtr + opPtr.computeOperandOffset ctx₀ idx hnum
  let ctx := oper.writeNextUse ctx₀ .none (by prove_setSlotBounds ctx₀)
  let ctx := oper.writeBack ctx 0 (by prove_setSlotBounds ctx₀)
  let ctx := oper.writeOwner ctx opPtr (by prove_setSlotBounds ctx₀)
  let ctx := oper.writeValue ctx value (by prove_setSlotBounds ctx₀)
  ctx

@[inline]
protected def Rewriter.setBlockOperand (opPtr : Buffed.OperationMPtr) (ctx₀ : Buffed.IRBufContext OpInfo) (idx : UInt64)
    (hnum : (opPtr + Buffed.Operation.Offsets.numOperands).toInt + Buffed.Operation.Sizes.numOperands.toInt ≤ ctx₀.size)
    (hslot : (opPtr + opPtr.computeBlockOperandOffset ctx₀ idx hnum).toNat + Buffed.BlockOperand.size.toNat ≤ ctx₀.size)
    (value : Buffed.BlockMPtr) : Buffed.IRBufContext OpInfo :=
  let oper : Buffed.BlockOperandMPtr := opPtr + opPtr.computeBlockOperandOffset ctx₀ idx hnum
  let ctx := oper.writeNextUse ctx₀ .none (by prove_setSlotBounds ctx₀)
  let ctx := oper.writeBack ctx 0 (by prove_setSlotBounds ctx₀)
  let ctx := oper.writeOwner ctx opPtr (by prove_setSlotBounds ctx₀)
  let ctx := oper.writeValue ctx value (by prove_setSlotBounds ctx₀)
  ctx

@[inline]
protected def Rewriter.setRegion (opPtr : Buffed.OperationMPtr) (ctx₀ : Buffed.IRBufContext OpInfo) (idx : UInt64)
    (region : Buffed.RegionMPtr)
    (hregion : (region + Buffed.Region.Offsets.parent).toInt + Buffed.Region.Sizes.parent.toInt ≤ ctx₀.size)
    (hnum : (opPtr + Buffed.Operation.Offsets.numOperands).toInt + Buffed.Operation.Sizes.numOperands.toInt ≤ ctx₀.size)
    (hslot : (opPtr + opPtr.computeRegionOffset ctx₀ idx hnum).toNat + Buffed.ptrSize.toNat ≤ ctx₀.size) :
    Buffed.IRBufContext OpInfo :=
  -- Compute the region slot from `ctx₀` (the region-`writeParent` below touches the region, not
  -- the operation's count fields, so the offset is the same), then write the parent link and
  -- blit the region pointer into the slot. `hregion` bounds the (independent) region pointer.
  let slot := opPtr + opPtr.computeRegionOffset ctx₀ idx hnum
  let ctx := region.writeParent ctx₀ opPtr hregion
  let mem := ctx.mem.blit64 slot region (by
    have hb := ctx₀.mem.fits_in_memory
    simp only [Buffed.IRBufContext.size_def] at *
    grind [UInt64.uint64_add_int64_toInt_lt, Buffed.RegionMPtr.writeParent_range,
      Buffed.RegionMPtr.writeParent_size])
  { ctx with mem := mem }

buffed
def Rewriter.initBlockArgumentsLoopSim (blockPtr: Sim.BlockPtr) (ctx: Sim.IRContext OpInfo)
    (types : Array TypeAttr) (index : UInt64 := 0) (hblock : blockPtr.InBounds ctx := by grind)
    (hidx : index.toNat = blockPtr.spec.getNumArguments! ctx.spec := by grind) : Option (Sim.IRContext OpInfo) := do
  if h : index ≥ types.usize.toUInt64 then
    ctx
  else
    rlet ctx ← Rewriter.pushBlockArgumentAt blockPtr ctx index
      (types[index.toNat]'(by grind only [Array.usize_size, UInt64.le_iff_toNat_le]))
      (by grind) (by grind)
    -- TODO: simplify...
    Rewriter.initBlockArgumentsLoopSim blockPtr ctx types (index + 1) (hidx := by
      rename_i heq
      have := Rewriter.pushBlockArgumentAt_spec heq
      grind [UInt64.le_iff_toNat_le, UInt64.toNat_mod_size, Rewriter.pushBlockArgument]) (by
      rename_i heq
      have := Rewriter.pushBlockArgumentAt_spec heq
      grind [UInt64.le_iff_toNat_le, UInt64.toNat_mod_size, Rewriter.pushBlockArgument])
  termination_by types.usize.toNat - index.toNat
  decreasing_by
    have := @Array.usize_size
    rw [show types.usize.toNat = types.size by solve_by_elim]
    grind only [UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_mod_size]

buffed
def Rewriter.initBlockArgumentsSim (blockPtr: Sim.BlockPtr) (ctx: Sim.IRContext OpInfo)
    (types : Array TypeAttr) (index : UInt64 := 0) (hblock : blockPtr.InBounds ctx := by grind)
    (hidx : index.toNat = blockPtr.spec.getNumArguments! ctx.spec := by grind) : Option (Sim.IRContext OpInfo) := do
   Rewriter.initBlockArgumentsLoop blockPtr ctx types index hblock hidx

@[grind .]
theorem Rewriter.initBlockArguments_fieldsInBounds {blockPtr : Sim.BlockPtr}
    {ctx : Sim.IRContext OpInfo} {types index h₁ h₂}
    (heq : initBlockArguments blockPtr ctx types index h₁ h₂ = some newCtx) :
    ctx.spec.FieldsInBounds → newCtx.spec.FieldsInBounds := by
  simp [initBlockArguments_def, initBlockArgumentsSim, initBlockArgumentsLoop_def] at heq
  revert heq
  fun_induction initBlockArgumentsLoopSim <;> grind

/--
This theorem is a more general version of `initBlockArguments_inBounds` that is needed for the
induction step in the proof of that theorem.
-/
theorem Rewriter.initBlockArguments_inBounds' (ptr : Veir.GenericPtr) {blockPtr : Sim.BlockPtr}
    {ctx : Sim.IRContext OpInfo} {types index h₁ h₂}
    (heq : initBlockArguments blockPtr ctx types index h₁ h₂ = some newCtx) :
    ptr.InBounds newCtx.spec ↔
    match ptr with
    | .blockArgument argPtr
    | .value (.blockArgument argPtr)
    | .opOperandPtr (.valueFirstUse (.blockArgument argPtr)) =>
      if argPtr.block = blockPtr.spec then
        /-
          We need `argPtr.index < blockPtr.getNumArguments! ctx` because of the case where we
          call `initBlockArguments` on a block that already has a larger number of arguments as
          `types.size`.
        -/
        argPtr.index < types.size ∨ argPtr.index < blockPtr.spec.getNumArguments! ctx.spec
      else
        argPtr.InBounds ctx.spec
    | _ => ptr.InBounds ctx.spec := by
  simp [initBlockArguments_def, initBlockArgumentsSim, initBlockArgumentsLoop_def] at heq
  revert heq
  fun_induction initBlockArgumentsLoopSim <;>
    grind (gen := 20) (splits := 20) [BlockArgumentPtr.inBounds_def, → Array.size_le_toNat]

theorem Rewriter.initBlockArguments_inBounds (ptr : Veir.GenericPtr) {blockPtr : Sim.BlockPtr}
    {ctx : Sim.IRContext OpInfo} {types h₁ h₂}
    (heq : initBlockArguments blockPtr ctx types 0 h₁ h₂ = some newCtx) :
    ptr.InBounds newCtx.spec ↔
    match ptr with
    | .blockArgument argPtr
    | .value (.blockArgument argPtr)
    | .opOperandPtr (.valueFirstUse (.blockArgument argPtr)) =>
      if argPtr.block = blockPtr.spec then argPtr.index < types.size else argPtr.InBounds ctx.spec
    | _ => ptr.InBounds ctx.spec := by
  grind [Rewriter.initBlockArguments_inBounds']

grind_pattern Rewriter.initBlockArguments_inBounds =>
  Rewriter.initBlockArguments blockPtr ctx types 0 h₁ h₂, some newCtx, ptr.InBounds newCtx.spec

@[grind .]
theorem Rewriter.initBlockArguments_inBounds_veir_mono (ptr : Veir.GenericPtr) {blockPtr : Sim.BlockPtr}
    {ctx : Sim.IRContext OpInfo} {types index h₁ h₂}
    (heq : initBlockArguments blockPtr ctx types index h₁ h₂ = some newCtx) :
    ptr.InBounds ctx.spec → ptr.InBounds newCtx.spec := by
  simp [initBlockArguments_def, initBlockArgumentsSim, initBlockArgumentsLoop_def] at heq
  revert heq
  fun_induction initBlockArgumentsLoopSim
  · grind
  · grind
  · grind [initBlockArgumentsLoopSim._proof_6, Rewriter.pushBlockArgument]

@[grind .]
theorem Rewriter.initBlockArguments_inBounds_mono (ptr : Sim.GenericPtr) {blockPtr : Sim.BlockPtr}
    {ctx : Sim.IRContext OpInfo} {types index h₁ h₂}
    (heq : initBlockArguments blockPtr ctx types index h₁ h₂ = some newCtx) :
    ptr.InBounds ctx → ptr.InBounds newCtx := by
  simp [initBlockArguments_def, initBlockArgumentsSim, initBlockArgumentsLoop_def] at heq
  revert heq
  fun_induction initBlockArgumentsLoopSim <;> grind

buffed
def Rewriter.createBlockSim (ctx: Sim.IRContext OpInfo) (argTypes : Array TypeAttr)
    (insertionPoint: Option BlockInsertPoint)
    (hctx : ctx.spec.FieldsInBounds) (hip : insertionPoint.maybe BlockInsertPoint.InBounds ctx.spec)
    (ipRepr : insertionPoint.maybe₁ BlockInsertPoint.IsRepr)
    : Option (Sim.IRContext OpInfo × Sim.BlockPtr) := do
  rlet ⟨newBlockPtr, ctx⟩ ← Sim.BlockPtr.allocEmpty ctx (numArgs := argTypes.size.toUInt64)
  have : newBlockPtr.InBounds ctx := by grind
  rlet ctx ← Rewriter.initBlockArguments newBlockPtr ctx argTypes 0 (by grind) (by
    rename_i heq
    have ⟨addr, heq'⟩ := Sim.BlockPtr.allocEmpty_spec _ heq
    have : newBlockPtr.spec.get! ctx.spec = .empty argTypes.size := by
      have := BlockPtr.get!_BlockPtr_allocEmptyAtAddress (block := newBlockPtr.spec) heq'
      grind [=_ Array.usize_size]
    grind)
  match h : insertionPoint with
  | some insertionPoint => do
    let ctx ← Rewriter.insertBlock? ctx newBlockPtr insertionPoint (by grind [generic_ptr_grind])
      (by grind [cases BlockInsertPoint]) (by grind [cases BlockInsertPoint]) (by grind)
    (ctx, newBlockPtr)
  | none =>
    (ctx, newBlockPtr)

@[grind .]
theorem Rewriter.createBlock_inBounds_mono (ptr : Sim.GenericPtr) (heq : createBlock ctx types ip hctx hip hrep = some ⟨newCtx, newPtr⟩) :
    ptr.InBounds ctx → ptr.InBounds newCtx := by
  simp only [createBlock] at heq
  split at heq
  · grind
  · split at heq
    · simp [Option.bind] at heq
      split at heq <;> grind
    · grind

@[grind .]
theorem Rewriter.createBlock_fieldsInBounds_mono
    (heq : createBlock ctx types ip hctx hip hrep = some ⟨newCtx, newPtr⟩) :
    ctx.spec.FieldsInBounds → newCtx.spec.FieldsInBounds := by
  simp only [createBlock] at heq
  split at heq
  · grind
  · split at heq
    · simp [Option.bind] at heq
      split at heq <;> grind
    · grind

-- def Rewriter.setBlockArguments (ctx : IRContext OpInfo) (blockPtr : BlockPtr)
--     (types : Array TypeAttr) (hblock : blockPtr.InBounds ctx := by grind) : IRContext OpInfo :=
--   let numArgs := blockPtr.getNumArguments ctx (by grind)
--   if _ : numArgs = 0 then
--     Rewriter.initBlockArguments ctx blockPtr types
--   else
--     let ctx := blockPtr.setArguments ctx #[]
--     Rewriter.initBlockArguments ctx blockPtr types

-- @[grind =]
-- theorem Rewriter.setBlockArguments_inBounds (ptr : GenericPtr) :
--     ptr.InBounds (Rewriter.setBlockArguments ctx blockPtr types hblock) ↔
--     match ptr with
--     | .blockArgument argPtr
--     | .value (.blockArgument argPtr)
--     | .opOperandPtr (.valueFirstUse (.blockArgument argPtr)) =>
--       if argPtr.block = blockPtr then argPtr.index < types.size else argPtr.InBounds ctx
--     | _ => ptr.InBounds ctx := by
--   grind [Rewriter.setBlockArguments]

/-!
`Rewriter.setBlockArguments` preserves `FieldsInBounds` only if the context is well-formed and no
previous block argument is used. Otherwise, another pointer could point to one of the block arguments.
-/

buffed
def Rewriter.createRegionSim (ctx: Sim.IRContext OpInfo) : Option (Sim.IRContext OpInfo × Sim.RegionPtr) := do
  let ⟨reg, ctx⟩ ← Sim.RegionPtr.allocEmpty ctx
  some (ctx, reg)

@[grind .]
theorem Rewriter.createRegion_new_inBounds (h : createRegion ctx = some (ctx', reg)) :
    reg.InBounds ctx' := by
  grind [createRegion]

@[grind .]
theorem Rewriter.createRegion_new_not_inBounds (h : createRegion ctx = some (ctx', reg)) :
    ¬ reg.InBounds ctx := by
  grind [createRegion]

@[grind =>]
theorem Rewriter.createRegion_genericPtr_mono (ptr : Sim.GenericPtr) (heq : createRegion ctx = some (ctx', ptr')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr.spec = .region ptr'.spec) := by
  grind [createRegion]

@[grind .]
theorem Rewriter.createRegion_fieldsInBounds (h : createRegion ctx = some (ctx', rg)) :
    ctx.spec.FieldsInBounds → ctx'.spec.FieldsInBounds := by
  grind [createRegion]

@[grind]
def Rewriter.pushRegion (ctx : IRContext OpInfo) (op : OperationPtr) (region : RegionPtr)
    (hop : op.InBounds ctx := by grind) (hregion : region.InBounds ctx := by grind)
    (hRegionParent : (region.get! ctx).parent = none := by grind) :
    IRContext OpInfo :=
  let ctx := region.setParent ctx op
  op.pushRegion ctx region

buffed
def Rewriter.pushRegionAtSim (opPtr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (idx : UInt64) (region : Sim.RegionPtr)
    (hop : opPtr.InBounds ctx := by grind) (hregion : region.InBounds ctx := by grind)
    (hRegionParent : (region.spec.get! ctx.spec).parent = none := by grind) :
    Sim.IRContext OpInfo :=
  ⟨Rewriter.setRegion opPtr.impl ctx.buf idx region.impl sorry sorry sorry,
   Rewriter.pushRegion ctx.spec opPtr.spec region.spec (by grind) (by grind) (by grind), admitted_sim ctx⟩

@[simp, grind =]
theorem Rewriter.pushRegionAt_inBounds_veir_mono (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx region h₁ h₂ h₃} :
    ptr.InBounds (pushRegionAt opPtr ctx idx region h₁ h₂ h₃).spec ↔ ptr.InBounds ctx.spec := by
  simp only [pushRegionAt_def, pushRegionAtSim] <;> grind

@[grind .]
theorem Rewriter.pushRegionAt_layoutUnchanged {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx region h₁ h₂ h₃} :
    ctx.spec.LayoutUnchanged (pushRegionAt opPtr ctx idx region h₁ h₂ h₃).spec := by
  simp only [pushRegionAt_def, pushRegionAtSim, pushRegion] <;>
  apply IRContext.LayoutUnchanged.trans (region.spec.setParent ctx.spec opPtr.spec (by grind)) <;> grind

@[simp, grind =]
theorem Rewriter.pushRegionAt_inBounds_mono (ptr : Sim.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx region h₁ h₂ h₃} :
    ptr.InBounds (pushRegionAt opPtr ctx idx region h₁ h₂ h₃) ↔ ptr.InBounds ctx := by
  grind

@[grind .]
theorem Rewriter.pushRegion_fieldsInBounds {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx region h₁ h₂ h₃} (hx : ctx.spec.FieldsInBounds) :
    (pushRegionAt opPtr ctx idx region h₁ h₂ h₃).spec.FieldsInBounds := by
  simp only [pushRegionAt]
  apply OperationPtr.pushRegion_fieldsInBounds <;> grind

buffed
def Rewriter.initOpRegionsSim (opPtr: Sim.OperationPtr) (ctx: Sim.IRContext OpInfo)
    (regions : Array Sim.RegionPtr) (index : UInt64 := 0)
    (opPtrInBounds : opPtr.InBounds ctx := by grind)
    (hregionInBounds : ∀ region ∈ regions, region.InBounds ctx := by grind)
    (hctx : ctx.spec.FieldsInBounds := by grind)
    (hn : index.toNat = opPtr.spec.getNumRegions! ctx.spec := by grind) :
    Option (Sim.IRContext OpInfo) := do
  if h: index >= regions.usize.toUInt64 then
    some ctx
  else
    let region := regions[index.toNat]'(by grind [Array.usize_size, UInt64.le_iff_toNat_le])
    match hParent : (region.getParent ctx (by grind)).toOption with
    | none =>
      let ctx := Rewriter.pushRegionAt opPtr ctx index region (hregion := by grind) (hRegionParent := by grind)
      Rewriter.initOpRegionsSim opPtr ctx regions (index + 1)
        (opPtrInBounds := by grind [generic_ptr_grind])
        (hregionInBounds := by grind [generic_ptr_grind])
        (hctx := by grind)
        (hn := by
          have : (index + 1).toNat = index.toNat + 1 := by grind [Array.size_le_uint64_size]
          grind [Rewriter.pushRegionAt_def, Rewriter.pushRegionAtSim])
    | some _ => none
  termination_by regions.size - index.toNat
  decreasing_by grind only [UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_mod_size]

@[grind .]
theorem Rewriter.initOpRegions_fieldsInBounds {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {regions n opPtrInBounds hregions hctx hn} :
    ctx.spec.FieldsInBounds →
    initOpRegions opPtr ctx regions n opPtrInBounds hregions hctx hn = some ctx' →
    ctx'.spec.FieldsInBounds := by
  simp [initOpRegions_def]
  fun_induction initOpRegionsSim <;> grind

@[grind .]
theorem Rewriter.initOpRegions_inBounds_mono (ptr : Sim.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {regions n opPtrInBounds hregions hctx hn} :
    ptr.InBounds ctx →
    initOpRegions opPtr ctx regions n opPtrInBounds hregions hctx hn = some ctx' →
    ptr.InBounds ctx' := by
  simp [initOpRegions_def]
  fun_induction initOpRegionsSim <;> grind

@[grind .]
theorem Rewriter.initOpRegions_preserves_numOperands (ptr : Veir.OperationPtr)
    {ctx ctx' : Sim.IRContext OpInfo} {index h₁ h₂ h₃ h₄}
    (heq : Rewriter.initOpRegions opPtr ctx regions index h₁ h₂ h₃ h₄ = some ctx') :
    ptr.getNumOperands! ctx'.spec = ptr.getNumOperands! ctx.spec := by
  simp [initOpRegions_def] at heq
  fun_induction initOpRegionsSim <;> grind (gen := 20) [pushRegionAt_def, pushRegionAtSim]

@[grind .]
theorem Rewriter.initOpRegions_preserves_numSuccessors (ptr : Veir.OperationPtr)
    {ctx ctx' : Sim.IRContext OpInfo} {index h₁ h₂ h₃ h₄}
    (heq : Rewriter.initOpRegions opPtr ctx regions index h₁ h₂ h₃ h₄ = some ctx') :
    ptr.getNumSuccessors! ctx'.spec = ptr.getNumSuccessors! ctx.spec := by
  simp [initOpRegions_def] at heq
  fun_induction initOpRegionsSim <;> grind (gen := 20) [pushRegionAt_def, pushRegionAtSim]

def Rewriter.pushResult (ctx : IRContext OpInfo) (op : OperationPtr) (type : TypeAttr)
    (hop : op.InBounds ctx := by grind)
    : IRContext OpInfo :=
  let index := op.getNumResults! ctx
  let result : OpResult := { type := type, firstUse := none, index := index, owner := op }
  op.pushResult ctx result (by grind)

buffed
def Rewriter.pushResultAtSim (opPtr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (idx : UInt64) (type : TypeAttr) (hop : opPtr.InBounds ctx := by grind)
    (hidx : idx.toNat = opPtr.spec.getNumResults! ctx.spec := by grind) :
    Option (Sim.IRContext OpInfo) := do
  some ⟨← Rewriter.setResult opPtr.impl ctx.buf idx sorry sorry type, Rewriter.pushResult ctx.spec opPtr.spec type (by grind), admitted_sim hidx⟩

@[grind =>]
theorem Rewriter.pushResultAt_spec {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {idx type hop hidx}
    (heq : Rewriter.pushResultAt opPtr ctx idx type hop hidx = some ctx') :
    ctx'.spec = Rewriter.pushResult ctx.spec opPtr.spec type (by grind) := by
  simp only [pushResultAt_def, pushResultAtSim, Option.bind_eq_bind, Option.bind] at heq
  grind

@[grind .]
theorem Rewriter.pushResultAt_fieldsInBounds {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {idx type hop hidx}
    (heq : Rewriter.pushResultAt opPtr ctx idx type hop hidx = some ctx') :
    ctx.spec.FieldsInBounds → ctx'.spec.FieldsInBounds := by
  simp only [pushResultAt_def, pushResultAtSim] at heq
  grind

@[grind .]
theorem Rewriter.pushResultAt_layoutUnchanged {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {idx type hop hidx}
    (heq : Rewriter.pushResultAt opPtr ctx idx type hop hidx = some ctx') :
    ctx'.spec.LayoutUnchanged ctx.spec := by
  rw [Rewriter.pushResultAt_spec heq]
  grind [generic_ptr_grind, Rewriter.pushResult]

@[grind .]
theorem Rewriter.pushResultAt_veir_inBounds_mono (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {idx type hop hidx}
    (heq : Rewriter.pushResultAt opPtr ctx idx type hop hidx = some ctx') :
    ptr.InBounds ctx.spec → ptr.InBounds ctx'.spec := by
  rw [Rewriter.pushResultAt_spec heq]
  grind [generic_ptr_grind, Rewriter.pushResult]

@[grind =>]
theorem Rewriter.pushResultAt_inBounds (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {idx type hop hidx}
    (heq : Rewriter.pushResultAt opPtr ctx idx type hop hidx = some ctx') :
    ptr.InBounds ctx'.spec ↔
    (ptr.InBounds ctx.spec ∨
      ptr = .opResult (opPtr.spec.nextResult ctx.spec) ∨
      ptr = .value (opPtr.spec.nextResult ctx.spec) ∨
      ptr = .opOperandPtr (.valueFirstUse (opPtr.spec.nextResult ctx.spec)))
    := by
  rw [Rewriter.pushResultAt_spec heq]
  grind [Rewriter.pushResult]

buffed
def Rewriter.initOpResultsSim (opPtr: Sim.OperationPtr) (ctx: Sim.IRContext OpInfo)
    (resultTypes: Array TypeAttr) (index: UInt64 := 0) (hop : opPtr.InBounds ctx := by grind)
    (hidx : index.toNat = opPtr.spec.getNumResults! ctx.spec := by grind) :
    Option (Sim.IRContext OpInfo) := do
  if h: index >= resultTypes.usize.toUInt64 then
    some ctx
  else
    rlet ctx ← Rewriter.pushResultAt opPtr ctx index (resultTypes[index.toNat]'(by grind [Array.usize_size, UInt64.le_iff_toNat_le])) (by grind) (by grind)
    Rewriter.initOpResultsSim opPtr ctx resultTypes (index + 1) (by grind [generic_ptr_grind]) (by
      have : (index + 1).toNat = index.toNat + 1 := by grind [Array.size_le_uint64_size]
      rw [Rewriter.pushResultAt_spec (by assumption)]
      grind [Rewriter.pushResult])
  termination_by resultTypes.size - index.toNat
  decreasing_by grind only [UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_mod_size,
    = UInt64.add_toNat_lt]

@[grind .]
theorem Rewriter.initOpResults_fieldsInBounds {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ = some ctx') :
    ctx.spec.FieldsInBounds → ctx'.spec.FieldsInBounds := by
  simp [initOpResults_def] at heq
  fun_induction initOpResultsSim <;> grind

@[grind .]
theorem Rewriter.initOpResults_inBounds_mono (ptr : Sim.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ = some ctx') :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  simp [initOpResults_def] at heq
  fun_induction initOpResultsSim <;> grind

@[grind .]
theorem Rewriter.initOpResults_preserves_numRegions (ptr : Veir.OperationPtr)
    {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ = some ctx') :
    ptr.getNumRegions! ctx'.spec = ptr.getNumRegions! ctx.spec := by
  simp [initOpResults_def] at heq
  fun_induction initOpResultsSim <;> grind [Rewriter.pushResult]

@[grind .]
theorem Rewriter.initOpResults_preserves_numOperands (ptr : Veir.OperationPtr)
    {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ = some ctx') :
    ptr.getNumOperands! ctx'.spec = ptr.getNumOperands! ctx.spec := by
  simp [initOpResults_def] at heq
  fun_induction initOpResultsSim <;> grind [Rewriter.pushResult]

@[grind .]
theorem Rewriter.initOpResults_preserves_numSuccessors (ptr : Veir.OperationPtr)
    {ctx ctx' : Sim.IRContext OpInfo} {resultTypes index h₁ h₂}
    (heq : initOpResults opPtr ctx resultTypes index h₁ h₂ = some ctx') :
    ptr.getNumSuccessors! ctx'.spec = ptr.getNumSuccessors! ctx.spec := by
  simp [initOpResults_def] at heq
  fun_induction initOpResultsSim <;> grind [Rewriter.pushResult]

@[irreducible]
protected def Rewriter.pushOperand (ctx : IRContext OpInfo) (opPtr : OperationPtr) (valuePtr : ValuePtr)
    (opPtrInBounds : opPtr.InBounds ctx := by grind) (valueInBounds : valuePtr.InBounds ctx := by grind) : IRContext OpInfo :=
  let op := (opPtr.get ctx (by grind))
  let index := opPtr.getNumOperands ctx (by grind)
  let operand := { value := valuePtr, owner := opPtr, back := OpOperandPtrPtr.valueFirstUse valuePtr, nextUse := none : OpOperand}
  have : operand.FieldsInBounds ctx := by constructor <;> grind
  opPtr.pushOperand ctx operand (by grind)

protected buffed
def Rewriter.pushOperandAtUninsertedSim (opPtr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (idx : UInt64) (valuePtr : Sim.ValuePtr) (opPtrInBounds : opPtr.InBounds ctx := by grind)
    (valueInBounds : valuePtr.InBounds ctx := by grind) (hctx : ctx.spec.FieldsInBounds := by grind)
    (hidx : idx.toNat = opPtr.spec.getNumOperands! ctx.spec := by grind) :
    Sim.IRContext OpInfo :=
  ⟨Rewriter.setOperand opPtr.impl ctx.buf idx sorry sorry valuePtr.impl,
   Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind), admitted_sim hidx⟩

@[simp, grind =]
theorem Rewriter.pushOperandAtUninserted_spec :
    (pushOperandAtUninserted opPtr ctx idx valuePtr h₁ h₂ h₃ h₄).spec =
    Rewriter.pushOperand ctx.spec opPtr.spec valuePtr.spec (by grind) (by grind) := by
  simp [pushOperandAtUninserted_def, Rewriter.pushOperandAtUninsertedSim]

@[grind .]
theorem Rewriter.pushOperandAtUninserted_layoutUnchanged {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx valuePtr h₁ h₂ h₃ h₄} :
    (Rewriter.pushOperandAtUninserted opPtr ctx idx valuePtr h₁ h₂ h₃ h₄).spec.LayoutUnchanged ctx.spec := by
  simp [pushOperandAtUninserted_def, Rewriter.pushOperandAtUninsertedSim, Rewriter.pushOperand]
  grind

@[grind =>]
theorem Rewriter.pushOperandAtUninserted_veir_inBounds (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx valuePtr h₁ h₂ h₃ h₄} :
    ptr.InBounds (Rewriter.pushOperandAtUninserted opPtr ctx idx valuePtr h₁ h₂ h₃ h₄).spec ↔
    (ptr.InBounds ctx.spec ∨
     ptr = .opOperand (opPtr.spec.nextOperand ctx.spec) ∨
     ptr = .opOperandPtr (.operandNextUse (opPtr.spec.nextOperand ctx.spec))) := by
  simp [pushOperandAtUninserted_def, Rewriter.pushOperandAtUninsertedSim, Rewriter.pushOperand]
  grind

protected buffed
def Rewriter.pushOperandAtSim (opPtr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (idx : UInt64) (valuePtr : Sim.ValuePtr) (opPtrInBounds : opPtr.InBounds ctx := by grind)
    (valueInBounds : valuePtr.InBounds ctx := by grind) (hctx : ctx.spec.FieldsInBounds := by grind)
    (hidx : idx.toNat = opPtr.spec.getNumOperands! ctx.spec := by grind) :
    Sim.IRContext OpInfo :=
  let ctx := Rewriter.pushOperandAtUninserted opPtr ctx idx valuePtr
  let oper := opPtr.getOperandPtr ctx idx (by grind [generic_ptr_grind]) -- TODO: add std lemmas for ...Uninserted
  oper.insertIntoCurrent ctx (by grind [pushOperandAtUninserted,
    Sim.OperationPtr.getOpOperand_inBounds, pushOperandAtUninsertedSpec,
    Rewriter.pushOperand]) (by grind [generic_ptr_grind])

@[grind =>]
theorem Rewriter.pushOperandAt_layoutPreserved {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx valuePtr h₁ h₂ h₃ h₄} :
    ctx.spec.LayoutPreserved (Rewriter.pushOperandAt opPtr ctx idx valuePtr h₁ h₂ h₃ h₄).spec := by
  simp [Rewriter.pushOperandAt_def, Rewriter.pushOperandAtSim]
  apply IRContext.LayoutPreserved.trans (pushOperandAtUninserted opPtr ctx idx valuePtr (by grind) (by grind)).spec <;>
    grind

@[grind =>]
theorem Rewriter.pushOperandAt_veir_inBounds (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx valuePtr h₁ h₂ h₃ h₄} :
    ptr.InBounds (Rewriter.pushOperandAt opPtr ctx idx valuePtr h₁ h₂ h₃ h₄).spec ↔
    (ptr.InBounds ctx.spec ∨
     ptr = .opOperand (opPtr.spec.nextOperand ctx.spec) ∨
     ptr = .opOperandPtr (.operandNextUse (opPtr.spec.nextOperand ctx.spec))) := by
  simp [Rewriter.pushOperandAt_def, Rewriter.pushOperandAtSim]
  grind

@[grind .]
theorem Rewriter.pushOperand_inBounds_mono (ptr : Sim.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx valuePtr h₁ h₂ h₃ h₄} :
    ptr.InBounds ctx → ptr.InBounds (Rewriter.pushOperandAt opPtr ctx idx valuePtr h₁ h₂ h₃ h₄) := by
  simp [Rewriter.pushOperandAt_def, Rewriter.pushOperandAtSim]
  grind

@[grind .]
theorem Rewriter.pushOperand_fieldsInBounds {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx valuePtr h₁ h₂ h₃ h₄} :
    (Rewriter.pushOperandAt opPtr ctx idx valuePtr h₁ h₂ h₃ h₄).spec.FieldsInBounds := by
  simp [Rewriter.pushOperandAt_def, Rewriter.pushOperandAtSim]
  grind

@[grind .]
theorem Rewriter.pushOperand_preserves_numSuccessors (ptr : Veir.OperationPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx valuePtr h₁ h₂ h₃ h₄} :
    ptr.getNumSuccessors! (Rewriter.pushOperandAt opPtr ctx idx valuePtr h₁ h₂ h₃ h₄).spec = ptr.getNumSuccessors! ctx.spec := by
  simp [Rewriter.pushOperandAt_def, Rewriter.pushOperandAtSim]
  grind [Rewriter.pushOperand]

buffed
def Rewriter.initOpOperandsSim (opPtr: Sim.OperationPtr) (ctx: Sim.IRContext OpInfo)
    (opPtrInBounds : opPtr.InBounds ctx) (operands : Array Sim.ValuePtr)
    (hoperands : ∀ oper, oper ∈ operands → oper.InBounds ctx) (hctx : ctx.spec.FieldsInBounds)
    (index : UInt64 := 0) (hidx : index.toNat = opPtr.spec.getNumOperands! ctx.spec := by grind) :
    Sim.IRContext OpInfo :=
  if h : index >= operands.usize.toUInt64 then
    ctx
  else
    let valuePtr := operands[index.toNat]'(by grind [Array.usize_size, UInt64.le_iff_toNat_le])
    let ctx := Rewriter.pushOperandAt opPtr ctx index valuePtr
    Rewriter.initOpOperandsSim opPtr ctx (by grind [generic_ptr_grind]) operands (by grind [generic_ptr_grind]) (by grind) (index + 1) (by
      grind [Rewriter.pushOperandAt_def, Rewriter.pushOperandAtSpec, Rewriter.pushOperandAtSim, Sim.IRContext.isRepr, Rewriter.pushOperand])
  termination_by operands.size - index.toNat
  decreasing_by grind only [unfold_pointers, UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_mod_size]

@[grind .]
theorem Rewriter.initOpOperands_fieldsInBounds {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {h₁ operands h₂ h₃ index hidx}
    (heq : initOpOperands opPtr ctx h₁ operands h₂ h₃ index hidx = some ctx') :
    ctx.spec.FieldsInBounds → ctx'.spec.FieldsInBounds := by
  simp [Rewriter.initOpOperands_def] at heq
  grind

@[grind .]
theorem Rewriter.initOpOperands_inBounds_mono (ptr : Sim.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {h₁ operands h₂ h₃ index hidx}
    (heq : initOpOperands opPtr ctx h₁ operands h₂ h₃ index hidx = some ctx') :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  simp [Rewriter.initOpOperands_def] at heq
  fun_induction initOpOperandsSim <;> grind

@[grind .]
theorem Rewriter.initOpOperands_preserves_numSuccessors! (ptr : Veir.OperationPtr)
    {ctx ctx' : Sim.IRContext OpInfo} {h₁ operands h₂ h₃ index hidx}
    (heq : initOpOperands opPtr ctx h₁ operands h₂ h₃ index hidx = some ctx') :
    ptr.getNumSuccessors! ctx'.spec = ptr.getNumSuccessors! ctx.spec := by
  simp [Rewriter.initOpOperands_def] at heq
  fun_induction initOpOperandsSim <;> grind

@[irreducible]
protected def Rewriter.pushBlockOperand (ctx : IRContext OpInfo) (opPtr : OperationPtr) (blockPtr : BlockPtr)
    (opPtrInBounds : opPtr.InBounds ctx := by grind) (blockInBounds : blockPtr.InBounds ctx := by grind)
    (hctx : ctx.FieldsInBounds := by grind) : IRContext OpInfo :=
  let op := (opPtr.get ctx (by grind))
  let index := opPtr.getNumSuccessors ctx (by grind)
  let operand := { value := blockPtr, owner := opPtr, back := BlockOperandPtrPtr.blockFirstUse blockPtr, nextUse := none : BlockOperand}
  have : operand.FieldsInBounds ctx := by constructor <;> grind
  let ctx := opPtr.pushBlockOperand ctx operand (by grind)
  ctx

protected buffed
def Rewriter.pushBlockOperandAtUnattachedSim (opPtr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (idx : UInt64) (blockPtr : Sim.BlockPtr) (opPtrInBounds : opPtr.InBounds ctx := by grind)
    (blockInBounds : blockPtr.InBounds ctx := by grind) (hctx : ctx.spec.FieldsInBounds := by grind)
    (hidx : idx.toNat = opPtr.spec.getNumSuccessors! ctx.spec := by grind) :
    Sim.IRContext OpInfo :=
  ⟨Rewriter.setBlockOperand opPtr.impl ctx.buf idx sorry sorry blockPtr.impl,
    Rewriter.pushBlockOperand ctx.spec opPtr.spec blockPtr.spec (by grind) (by grind) (by grind),
    admitted_sim hidx⟩

@[grind .]
theorem Rewriter.pushBlockOperandAtUnattached_spec {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx blockPtr h₁ h₂ h₃ h₄} :
    (Rewriter.pushBlockOperandAtUnattached opPtr ctx idx blockPtr h₁ h₂ h₃ h₄).spec =
    Rewriter.pushBlockOperand ctx.spec opPtr.spec blockPtr.spec (by grind) (by grind) (by grind) := by
  simp [Rewriter.pushBlockOperandAtUnattached_def, Rewriter.pushBlockOperandAtUnattachedSim]

@[grind .]
theorem Rewriter.pushBlockOperandAtUnattached_layoutUnchanged {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx blockPtr h₁ h₂ h₃ h₄} :
    (Rewriter.pushBlockOperandAtUnattached opPtr ctx idx blockPtr h₁ h₂ h₃ h₄).spec.LayoutUnchanged ctx.spec := by
  simp [Rewriter.pushBlockOperandAtUnattached_def, Rewriter.pushBlockOperandAtUnattachedSim]
  grind [Rewriter.pushBlockOperand]

@[grind =>]
theorem Rewriter.pushBlockOperandAtUnattached_veir_inBounds (ptr : Veir.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx blockPtr h₁ h₂ h₃ h₄} :
    ptr.InBounds (Rewriter.pushBlockOperandAtUnattached opPtr ctx idx blockPtr h₁ h₂ h₃ h₄).spec ↔
    (ptr.InBounds ctx.spec ∨
      ptr = .blockOperand (opPtr.spec.nextBlockOperand ctx.spec) ∨
      ptr = .blockOperandPtr (.blockOperandNextUse (opPtr.spec.nextBlockOperand ctx.spec))) := by
  simp [Rewriter.pushBlockOperandAtUnattached_def, Rewriter.pushBlockOperandAtUnattachedSim]
  grind [Rewriter.pushBlockOperand]

protected buffed
def Rewriter.pushBlockOperandAtSim (opPtr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (idx : UInt64) (blockPtr : Sim.BlockPtr) (opPtrInBounds : opPtr.InBounds ctx := by grind)
    (blockInBounds : blockPtr.InBounds ctx := by grind) (hctx : ctx.spec.FieldsInBounds := by grind)
    (hidx : idx.toNat = opPtr.spec.getNumSuccessors! ctx.spec := by grind) :
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
  simp [Rewriter.pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim]
  grind

@[grind .]
theorem Rewriter.pushBlockOperand_inBounds_mono (ptr : Sim.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx blockPtr h₁ h₂ h₃ h₄} :
    ptr.InBounds ctx → ptr.InBounds (Rewriter.pushBlockOperandAt opPtr ctx idx blockPtr h₁ h₂ h₃ h₄) := by
  simp [Rewriter.pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim]
  grind

@[grind .]
theorem Rewriter.pushBlockOperand_fieldsInBounds {opPtr : Sim.OperationPtr}
    {ctx : Sim.IRContext OpInfo} {idx blockPtr h₁ h₂ h₃ h₄} :
    (Rewriter.pushBlockOperandAt opPtr ctx idx blockPtr h₁ h₂ h₃ h₄).spec.FieldsInBounds := by
  simp [Rewriter.pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim]
  grind

buffed
def Rewriter.initBlockOperandsSim (opPtr: Sim.OperationPtr) (ctx: Sim.IRContext OpInfo)
    (operands : Array Sim.BlockPtr) (index : UInt64 := 0) (opPtrInBounds : opPtr.InBounds ctx := by grind)
    (hctx : ctx.spec.FieldsInBounds := by grind) (hoperands : ∀ oper, oper ∈ operands → oper.InBounds ctx := by grind)
    (hidx : index.toNat = opPtr.spec.getNumSuccessors! ctx.spec := by grind) :
    Sim.IRContext OpInfo :=
  if h : index >= operands.usize.toUInt64 then
    ctx
  else
    let valuePtr := operands[index.toNat]'(by grind [Array.usize_size, UInt64.le_iff_toNat_le])
    let ctx := Rewriter.pushBlockOperandAt opPtr ctx index valuePtr (by grind) (by grind) (by grind) (by grind)
    Rewriter.initBlockOperandsSim opPtr ctx operands (index + 1) (by grind [generic_ptr_grind]) (by grind) (by grind [generic_ptr_grind]) (by
      have : (index + 1).toNat = index.toNat + 1 := by grind [unfold_pointers, Array.size_le_uint64_size]
      grind [Rewriter.pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim, Rewriter.pushBlockOperand])
  termination_by operands.size - index.toNat
  decreasing_by grind [unfold_pointers, UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_inj, UInt64.toNat_mod_size]

@[grind .]
theorem Rewriter.initBlockOperands_fieldsInBounds {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {operands index h₁ h₂ h₃ h₄}
    (heq : initBlockOperands opPtr ctx operands index h₁ h₂ h₃ h₄ = some ctx') :
    ctx.spec.FieldsInBounds → ctx'.spec.FieldsInBounds := by
  simp [Rewriter.initBlockOperands_def] at heq
  fun_induction Rewriter.initBlockOperandsSim <;> grind

@[grind .]
theorem Rewriter.initBlockOperands_inBounds_mono (ptr : Sim.GenericPtr) {opPtr : Sim.OperationPtr}
    {ctx ctx' : Sim.IRContext OpInfo} {operands index h₁ h₂ h₃ h₄}
    (heq : initBlockOperands opPtr ctx operands index h₁ h₂ h₃ h₄ = some ctx') :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  simp [Rewriter.initBlockOperands_def] at heq
  fun_induction Rewriter.initBlockOperandsSim <;> grind

-- buffed
-- def Rewriter.createEmptyOpSim (ctx : Sim.IRContext OpInfo) (opType : OpInfo) (properties : HasOpInfo.propertiesOf opType)
--     (numResults numOperands numBlockOperands numRegions : UInt64) :
--     Option (Sim.OperationPtr × Sim.IRContext OpInfo) := do
--   let ⟨op, ctx⟩ ← Sim.OperationPtr.allocEmpty ctx opType properties numResults numOperands numBlockOperands numRegions
--   pure ⟨op, ctx⟩

-- theorem Rewriter.createEmptyOp_new_inBounds {op : Sim.OperationPtr}
--     {ctx' : Sim.IRContext OpInfo}
--     (h : createEmptyOp ctx opType properties nr no nb nrg = some ⟨op, ctx'⟩) :
--     op.InBounds ctx' := by
--   -- grind [createEmptyOp]
--   sorry

-- theorem Rewriter.createEmptyOp_new_not_inBounds {op : Sim.OperationPtr}
--     {ctx' : Sim.IRContext OpInfo}
--     (h : createEmptyOp ctx opType properties nr no nb nrg = some ⟨op, ctx'⟩) :
--     ¬ op.InBounds ctx := by
--   -- grind [createEmptyOp]
--   sorry

-- theorem Rewriter.createEmptyOp_genericPtr_mono (ptr : Sim.GenericPtr) {ptr' : Sim.OperationPtr}
--     {ctx' : Sim.IRContext OpInfo}
--     (heq : createEmptyOp ctx type properties nr no nb nrg = some ⟨ptr', ctx'⟩) :
--     ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr.spec = .operation ptr'.spec) := by
--   -- grind [createEmptyOp]
--   sorry

-- theorem Rewriter.createEmptyOp_fieldsInBounds {op : Sim.OperationPtr}
--     {ctx' : Sim.IRContext OpInfo}
--     (h : createEmptyOp ctx opType properties nr no nb nrg = some ⟨op, ctx'⟩) :
--     ctx.spec.FieldsInBounds → ctx'.spec.FieldsInBounds := by
--   -- grind [createEmptyOp]
--   sorry

buffed (inline := false)
def Rewriter.createOpSim (ctx: Sim.IRContext OpInfo) (opType: OpInfo)
    (resultTypes: Array TypeAttr) (operands: Array Sim.ValuePtr) (blockOperands : Array Sim.BlockPtr)
    (regions: Array Sim.RegionPtr) (properties: HasOpInfo.propertiesOf opType)
    (insertionPoint: Option InsertPoint)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds ctx := by grind)
    (hblockOperands : ∀ oper, oper ∈ blockOperands → oper.InBounds ctx := by grind)
    (hregions : ∀ reg, reg ∈ regions → reg.InBounds ctx := by grind)
    (hins : insertionPoint.maybe InsertPoint.InBounds ctx.spec := by grind)
    (hrep : insertionPoint.maybe₁ InsertPoint.IsRepr := by grind)
    (hx : ctx.spec.FieldsInBounds := by grind) : Option (Sim.IRContext OpInfo × Sim.OperationPtr) := do
  rlet ⟨newOpPtr, ctx⟩ ← Sim.OperationPtr.allocEmpty ctx opType properties
    resultTypes.usize.toUInt64 operands.usize.toUInt64 blockOperands.usize.toUInt64 regions.usize.toUInt64
    sorry sorry sorry sorry
  have : newOpPtr.spec.getNumOperands! ctx.spec = 0 := by grind
  have : newOpPtr.spec.getNumSuccessors! ctx.spec = 0 := by grind
  have : newOpPtr.spec.getNumRegions! ctx.spec = 0 := by grind
  have : insertionPoint.maybe InsertPoint.InBounds ctx.spec := by
    grind [cases InsertPoint, Option.maybe_def]
  rlet ctx ← Rewriter.initOpResults newOpPtr ctx resultTypes 0 (by grind) (by grind)
  have : newOpPtr.spec.getNumOperands! ctx.spec = 0 := by grind
  have : newOpPtr.spec.getNumSuccessors! ctx.spec = 0 := by grind
  have : insertionPoint.maybe InsertPoint.InBounds ctx.spec := by
    grind [cases InsertPoint, Option.maybe_def, generic_ptr_grind,
      _=_ Veir.OperationPtr.toSim_inBounds_iff_inBounds, _=_ Veir.BlockPtr.toSim_inBounds_iff_inBounds]
  rlet ctx ← Rewriter.initOpRegions newOpPtr ctx regions 0 (by grind [generic_ptr_grind]) (by grind [generic_ptr_grind]) (by grind) (by grind)
  have : newOpPtr.spec.getNumSuccessors! ctx.spec = 0 := by grind
  have : insertionPoint.maybe InsertPoint.InBounds ctx.spec := by
    grind [cases InsertPoint, Option.maybe_def, generic_ptr_grind,
      _=_ Veir.OperationPtr.toSim_inBounds_iff_inBounds, _=_ Veir.BlockPtr.toSim_inBounds_iff_inBounds]
  rlet ctx := Rewriter.initOpOperands newOpPtr ctx (by grind [generic_ptr_grind]) operands (by grind [generic_ptr_grind]) (by grind) 0 (by grind)
  have : insertionPoint.maybe InsertPoint.InBounds ctx.spec := by
    grind [cases InsertPoint, Option.maybe_def, generic_ptr_grind,
      _=_ Veir.OperationPtr.toSim_inBounds_iff_inBounds, _=_ Veir.BlockPtr.toSim_inBounds_iff_inBounds]
  have : newOpPtr.spec.getNumSuccessors! ctx.spec = 0 := by grind
  rlet ctx := Rewriter.initBlockOperands newOpPtr ctx blockOperands 0 (by grind [generic_ptr_grind]) (by grind) (by grind [generic_ptr_grind]) (by grind)
  have : insertionPoint.maybe InsertPoint.InBounds ctx.spec := by
    grind (instances := 2000) [cases InsertPoint, Option.maybe_def, generic_ptr_grind,
      _=_ Veir.OperationPtr.toSim_inBounds_iff_inBounds, _=_ Veir.BlockPtr.toSim_inBounds_iff_inBounds]
  match _ : insertionPoint with
  | some insertionPoint => do
    let ctx ← Rewriter.insertOp? ctx newOpPtr insertionPoint (by grind [generic_ptr_grind]) (by grind) (by grind) (by grind)
    some (ctx, newOpPtr)
  | none =>
    some (ctx, newOpPtr)

@[grind .]
theorem Rewriter.createOp_inBounds_mono (ptr : Sim.GenericPtr)
    (heq : createOp ctx opType numResults operands blockOperands regions props ip h₁ h₂ h₃ h₄ h₅ = some (newCtx, newOp)) :
    ptr.InBounds ctx → ptr.InBounds newCtx := by
  simp only [createOp] at heq; grind (gen := 10)

@[grind .]
theorem Rewriter.createOp_new_inBounds (ptr : Sim.OperationPtr)
    (heq : createOp ctx opType numResults operands blockOperands regions props ip h₁ h₂ h₃ h₄ h₅ = some (newCtx, ptr)) :
    ptr.InBounds newCtx := by
  simp only [createOp] at heq; grind (gen := 10)

@[grind .]
theorem Rewriter.createOp_new_not_inBounds (ptr : Sim.OperationPtr)
    (heq : createOp ctx opType numResults operands blockOperands regions props ip h₁ h₂ h₃ h₄ h₅ = some (newCtx, ptr)) :
    ¬ ptr.InBounds ctx := by
  simp only [createOp] at heq; grind (gen := 10)

@[grind .]
theorem Rewriter.createOp_fieldsInBounds
    (heq : createOp ctx opType numResults operands blockOperands numRegions props ip h₁ h₂ h₃ h₄ h₅ = some (newCtx, newOp)) :
    ctx.spec.FieldsInBounds → newCtx.spec.FieldsInBounds := by
  simp only [createOp] at heq; grind (gen := 10)

buffed
def Sim.IRContext.emptySim : Sim.IRContext OpInfo :=
  ⟨⟨.emptyWithCapacity 1024, #[]⟩, IRContext.empty OpInfo, by constructor <;> grind [TopLevelPtr]⟩

-- TODO: lemma : ptr.IsRepr → ptr.id.toUInt64.toNat = ptr.id
buffed (inline := false)
def IRContext.createSim OpInfo [HasOpInfo OpInfo] : Option (Sim.IRContext OpInfo × Sim.OperationPtr) := do
  rlet ⟨ctx, region⟩ ← Rewriter.createRegion .empty
  have regionIb : region.InBounds ctx := by grind
  have regionRepr : region.spec.IsRepr := by grind
  rlet ⟨ctx, operation⟩ ← Rewriter.createOp ctx HasOpInfo.moduleOpCode #[] #[] #[] #[region] default none
    (by grind) (by grind) (by grind) (by grind) (by grind)
  have regionIb : region.InBounds ctx := by grind [generic_ptr_grind]
  rlet ⟨ctx, block⟩ ← Rewriter.createBlock ctx #[] (some (.atEnd ⟨region.impl.toNat⟩)) (by grind) (by
    simp only [Option.maybe_def, Veir.BlockInsertPoint.inBounds_def]
    rw [← regionIb.sim]
    simp only [RegionPtr.toM]
    simp [show region.spec.toFlat.toUInt64.toNat = region.spec.toFlat by grind]
    exact regionIb.ib) (by grind [Veir.RegionPtr.toFlat, Veir.RegionPtr.toM])
  some (ctx, operation)

@[grind →]
theorem IRContext.create_fieldsInBounds {op: Sim.OperationPtr} (h : IRContext.create OpInfo = some (ctx, op)) :
    ctx.spec.FieldsInBounds := by
  simp only [IRContext.create] at h; grind

@[grind →]
theorem IRContext.create_inBounds {op: Sim.OperationPtr} (h : IRContext.create OpInfo = some (ctx, op)) :
    op.InBounds ctx := by
  simp only [IRContext.create] at h; grind (gen := 10)
