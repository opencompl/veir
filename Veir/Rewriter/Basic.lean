import Veir.IR
import Veir.Rewriter.InsertPoint
import Veir.Rewriter.LinkedList

namespace Veir

/--
- Insert an operation at a given location.
-/
@[irreducible]
def Rewriter.insertOp? (ctx: IRContext) (newOp: OperationPtr) (insertionPoint: InsertPoint)
    (newOpIn: newOp.InBounds ctx := by grind)
    (insIn : insertionPoint.InBounds ctx)
    (ctxInBounds: ctx.FieldsInBounds) : Option IRContext :=
    rlet parent ← insertionPoint.block ctx
    let prev := insertionPoint.prev ctx (by grind)
    let next := insertionPoint.next
    newOp.linkBetweenWithParent ctx prev next parent (by grind) (by grind) (by grind) (by grind)

@[irreducible]
def Rewriter.detachOp (ctx: IRContext) (op: OperationPtr) (hctx : ctx.FieldsInBounds) (hIn : op.InBounds ctx) (hasParent: (op.get ctx hIn).parent.isSome) : IRContext :=
  let opStruct := op.get ctx
  let parent := opStruct.parent.get hasParent
  let ctx := op.setParent ctx none
  let prevOp := opStruct.prev
  let nextOp := opStruct.next
  -- Leo: I had to duplicate the continuation in each branch, I don't really
  -- know why the proofs of the preconditions in, say, `setNextOp` were
  -- metavariable... maybe somehow the execution of the tactics is slightly
  -- delayed?
  match _ : prevOp with
    | some prevOp =>
      let ctx := prevOp.setNextOp ctx nextOp
      match _ : nextOp with
      | some nextOp => nextOp.setPrevOp ctx prevOp (by grind (ematch := 10))
      | none => parent.setLastOp ctx prevOp (by grind (ematch := 10))
    | none =>
      let ctx := parent.setFirstOp ctx nextOp
      match _ : nextOp with
      | some nextOp => nextOp.setPrevOp ctx prevOp (by grind (ematch := 10))
      | none => parent.setLastOp ctx prevOp

@[grind .]
theorem Rewriter.detachOp_inBounds (ptr : GenericPtr) :
    ptr.InBounds (detachOp ctx hctx op hIn hasParent) ↔ ptr.InBounds ctx := by
  grind [detachOp]

@[grind .]
theorem Rewriter.detachOp_fieldsInBounds (hctx : ctx.FieldsInBounds) :
    (detachOp ctx op hctx hIn hasParent).FieldsInBounds := by
  simp only [detachOp]
  split <;> grind

/--
  Detach an operation from its parent if it has one.
  If it has no parent, return the context unchanged.
-/
@[irreducible, inline]
def Rewriter.detachOpIfAttached (ctx: IRContext) (op: OperationPtr)
    (hctx : ctx.FieldsInBounds := by grind)
    (hop : op.InBounds ctx := by grind) : IRContext :=
  match h: (op.get ctx hop).parent with
  | some _ => Rewriter.detachOp ctx op hctx hop (by grind)
  | none => ctx

@[grind .]
theorem Rewriter.detachOpIfAttached_inBounds (ptr : GenericPtr) :
    ptr.InBounds (detachOpIfAttached ctx op h₁ h₂) ↔ ptr.InBounds ctx := by
  grind [detachOpIfAttached]

@[grind .]
theorem Rewriter.detachOpIfAttached_fieldsInBounds (hctx : ctx.FieldsInBounds) :
    (detachOpIfAttached ctx op hctx hIn).FieldsInBounds := by
  grind [detachOpIfAttached]

@[irreducible, inline]
def Rewriter.detachOperands.loop (ctx : IRContext) (op : OperationPtr) (index : Nat)
    (hCtx : ctx.FieldsInBounds := by grind)
    (hOp : op.InBounds ctx := by grind)
    (hIndex : index < op.getNumOperands! ctx := by grind) : IRContext :=
  let ctx' := (OpOperandPtr.mk op index).removeFromCurrent ctx
  match index with
  | .succ index => Rewriter.detachOperands.loop ctx' op index (by grind) (by grind) (by grind)
  | 0 => ctx'

@[grind .]
theorem Rewriter.detachOperands.loop_inBounds (ptr : GenericPtr) :
    ptr.InBounds (detachOperands.loop ctx op index hCtx hOp hIndex) ↔ ptr.InBounds ctx := by
  induction index generalizing ctx <;> simp only [detachOperands.loop] <;> grind

@[grind .]
theorem Rewriter.detachOperands.loop_fieldsInBounds :
    ctx.FieldsInBounds → (detachOperands.loop ctx op index hCtx hOp hIndex).FieldsInBounds := by
  induction index generalizing ctx <;> simp only [detachOperands.loop] <;> grind

@[irreducible, inline]
def Rewriter.detachOperands (ctx : IRContext) (op : OperationPtr)
    (hCtx : ctx.FieldsInBounds := by grind)
    (hOp : op.InBounds ctx := by grind) : IRContext :=
  let numOperands := op.getNumOperands ctx (by grind)
  if h : numOperands = 0 then
    ctx
  else
    Rewriter.detachOperands.loop ctx op (numOperands - 1) (by grind) (by grind) (by grind)

@[grind .]
theorem Rewriter.detachOperands_inBounds (ptr : GenericPtr) :
    ptr.InBounds (detachOperands ctx op hCtx hOp) ↔ ptr.InBounds ctx := by
  grind [detachOperands]

@[grind .]
theorem Rewriter.detachOperands_fieldsInBounds :
    ctx.FieldsInBounds → (detachOperands ctx op hCtx hOp).FieldsInBounds := by
  grind [detachOperands]

@[irreducible, inline]
def Rewriter.detachBlockOperands.loop (ctx : IRContext) (op : OperationPtr) (index : Nat)
    (hCtx : ctx.FieldsInBounds := by grind)
    (hOp : op.InBounds ctx := by grind)
    (hIndex : index < op.getNumSuccessors! ctx := by grind) : IRContext :=
  let ctx' := (BlockOperandPtr.mk op index).removeFromCurrent ctx
  match index with
  | .succ index => Rewriter.detachBlockOperands.loop ctx' op index
  | 0 => ctx'

@[grind .]
theorem Rewriter.detachBlockOperands.loop_inBounds (ptr : GenericPtr) :
    ptr.InBounds (detachBlockOperands.loop ctx op index hCtx hOp hIndex) ↔ ptr.InBounds ctx := by
  induction index generalizing ctx <;> simp only [detachBlockOperands.loop] <;> grind

@[grind .]
theorem Rewriter.detachBlockOperands.loop_fieldsInBounds :
    ctx.FieldsInBounds → (detachBlockOperands.loop ctx op index hCtx hOp hIndex).FieldsInBounds := by
  induction index generalizing ctx <;> simp only [detachBlockOperands.loop] <;> grind

@[irreducible, inline]
def Rewriter.detachBlockOperands (ctx : IRContext) (op : OperationPtr)
    (hCtx : ctx.FieldsInBounds := by grind)
    (hOp : op.InBounds ctx := by grind) : IRContext :=
  let numOperands := op.getNumSuccessors ctx (by grind)
  if h : numOperands = 0 then
    ctx
  else
    Rewriter.detachBlockOperands.loop ctx op (numOperands - 1) (by grind) (by grind) (by grind)

@[grind .]
theorem Rewriter.detachBlockOperands_inBounds (ptr : GenericPtr) :
    ptr.InBounds (detachBlockOperands ctx op hCtx hOp) ↔ ptr.InBounds ctx := by
  grind [detachBlockOperands]

@[grind .]
theorem Rewriter.detachBlockOperands_fieldsInBounds :
    ctx.FieldsInBounds → (detachBlockOperands ctx op hCtx hOp).FieldsInBounds := by
  grind [detachBlockOperands]

@[irreducible, inline]
def Rewriter.eraseOp (ctx : IRContext) (op : OperationPtr)
    (hCtx : ctx.FieldsInBounds := by grind)
    (hOp : op.InBounds ctx := by grind) : IRContext :=
  let ctx := Rewriter.detachOpIfAttached ctx op
  let ctx := Rewriter.detachOperands ctx op
  let ctx := Rewriter.detachBlockOperands ctx op
  op.dealloc ctx

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
@[irreducible]
def Rewriter.insertBlock? (ctx: IRContext) (newBlock: BlockPtr)
    (insertionPoint: BlockInsertPoint) (hib : insertionPoint.InBounds ctx := by grind)
    (newBlockIn: newBlock.InBounds ctx := by grind)
    (ctxInBounds: ctx.FieldsInBounds := by grind) : Option IRContext :=
  match _ : insertionPoint with
    | .before existingBlock =>
      rlet parent ← (existingBlock.get ctx (by grind)).parent
      let prev := (existingBlock.get ctx (by grind)).prev
      let next := some existingBlock
      newBlock.linkBetweenWithParent ctx prev next parent (by grind) (by grind) (by grind) (by grind)
    | .atEnd region =>
      let parent := region
      let prev := (region.get ctx (by grind)).lastBlock
      let next := none
      newBlock.linkBetweenWithParent ctx prev next parent (by grind) (by grind) (by grind) (by grind)

def Rewriter.replaceUse (ctx: IRContext) (use : OpOperandPtr) (newValue: ValuePtr)
    (useIn: use.InBounds ctx := by grind)
    (newIn: newValue.InBounds ctx := by grind)
    (ctxIn: ctx.FieldsInBounds := by grind) : IRContext :=
  if (use.get ctx (by grind)).value = newValue then
    ctx
  else
    let ctx := use.removeFromCurrent ctx (by grind) (by grind)
    let ctx := use.setValue ctx newValue
    let ctx := use.insertIntoCurrent ctx (by grind) (by grind)
    ctx

@[grind =]
theorem Rewriter.replaceUse_inBounds (ptr : GenericPtr) :
    ptr.InBounds (replaceUse ctx use newValue useIn newIn ctxIn) ↔ ptr.InBounds ctx := by
  grind [replaceUse]

@[grind .]
theorem Rewriter.replaceUse_fieldsInBounds :
     ctx.FieldsInBounds → (replaceUse ctx use newValue useIn newIn ctxIn).FieldsInBounds := by
  grind [replaceUse]

@[irreducible]
def Rewriter.replaceValue? (ctx: IRContext) (oldValue: ValuePtr) (newValue: ValuePtr)
    (oldIn: oldValue.InBounds ctx := by grind)
    (newIn: newValue.InBounds ctx := by grind)
    (ctxIn: ctx.FieldsInBounds := by grind)
    (depth: Nat := 1_000_000_000) : Option IRContext :=
  match depth with
  | Nat.succ depth =>
    match _ : oldValue.getFirstUse ctx (by grind) with
    | none => ctx
    | some firstUse =>
    let ctx := Rewriter.replaceUse ctx firstUse newValue
    Rewriter.replaceValue? ctx oldValue newValue (by grind [Rewriter.replaceUse]) (by grind [Rewriter.replaceUse]) (by grind [Rewriter.replaceUse]) depth
  | _ => none

@[grind .]
theorem Rewriter.replaceValue?_inBounds (ptr : GenericPtr) :
    replaceValue? ctx old new h₁ h₂ h₃ d = some ctx' →
    (ptr.InBounds ctx ↔ ptr.InBounds ctx') := by
  induction d generalizing ctx
  case zero => simp [replaceValue?]
  case succ d ih => simp [replaceValue?]; split <;> grind [Rewriter.replaceUse]

@[grind .]
theorem Rewriter.replaceValue?_fieldsInBounds :
     ctx.FieldsInBounds → (replaceValue? ctx old new h₁ h₂ h₃ d).maybe₁ IRContext.FieldsInBounds := by
  induction d generalizing ctx
  case zero => simp [replaceValue?, Option.maybe₁]
  case succ d ih => simp [replaceValue?]; grind [Rewriter.replaceUse]

@[grind .]
theorem Rewriter.replaceValue?_preserves_results_size' (op : OperationPtr) (hop : op.InBounds ctx) :
    replaceValue? ctx old new h₁ h₂ h₃ d = some ctx' →
    op.getNumResults! ctx' = op.getNumResults! ctx := by
  induction d generalizing ctx ctx'
  case zero => simp [replaceValue?, *]
  case succ d ih =>
    simp only [replaceValue?]; split
    · grind
    · rename_i firstUse hFirstUse
      intros hh
      rw [ih (ctx' := ctx') (ctx := Rewriter.replaceUse ctx firstUse new (by grind) (by grind) (by grind))] <;> grind [Rewriter.replaceUse]

@[grind .]
theorem Rewriter.replaceValue?_preserves_results_size (op : OperationPtr) (hop : op.InBounds ctx)
    (hctx' : replaceValue? ctx old new h₁ h₂ h₃ d = some ctx') :
    op.getNumResults! ctx' = op.getNumResults! ctx  := by
  have := @replaceValue?_preserves_results_size'
  grind

@[grind .]
theorem Rewriter.replaceValue?_preserves_parent' (op : OperationPtr) (hop : op.InBounds ctx)
    (hctx' : replaceValue? ctx old new h₁ h₂ h₃ d = some ctx') :
    (op.get! ctx').parent = (op.get! ctx).parent := by
  induction d generalizing ctx
  case zero => simp [replaceValue?, *] at hctx' ⊢
  case succ d ih =>
    simp only [replaceValue?] at hctx'; split at hctx'
    · grind
    · rename_i firstUse hFirstUse
      rw [ih (ctx := Rewriter.replaceUse ctx firstUse new (by grind) (by grind) (by grind)) (by grind [Rewriter.replaceUse])] <;> grind [Rewriter.replaceUse]

@[grind .]
theorem Rewriter.replaceValue?_preserves_parent (op : OperationPtr) (hop : op.InBounds ctx)
    (hctx' : replaceValue? ctx old new h₁ h₂ h₃ d = some ctx') :
    (op.get ctx' (by grind)).parent = (op.get ctx hop).parent := by
  have := @replaceValue?_preserves_parent'
  grind [Rewriter.replaceUse]

@[irreducible]
def Rewriter.replaceValues (ctx: IRContext) (values: List (ValuePtr × ValuePtr)) : Option IRContext :=
  values.foldlM (init := ctx) fun ctx (oldValue, newValue) =>
    Rewriter.replaceValue? ctx oldValue newValue (by sorry) (by sorry) (by sorry)

@[irreducible]
def Rewriter.replaceOp? (ctx: IRContext) (oldOp newOp: OperationPtr)
    (oldIn: oldOp.InBounds ctx := by grind)
    (newIn: newOp.InBounds ctx := by grind)
    (ctxIn: ctx.FieldsInBounds := by grind)
    (hpar : (oldOp.get ctx).parent.isSome = true) : Option IRContext := do
  let numOldResults := oldOp.getNumResults ctx (by grind)
  let numNewResults := newOp.getNumResults ctx (by grind)
  if h : numOldResults ≠ numNewResults then
    none
  else
    let mut newCtx : { c: IRContext //
        c.FieldsInBounds ∧
        (∀ (ptr : GenericPtr), ptr.InBounds c ↔ ptr.InBounds ctx) ∧
        (∀ (op : OperationPtr), ∀ h₁ h₂, (op.getNumResults ctx h₁) = (op.getNumResults c h₂)) ∧
        (∀ (op : OperationPtr), ∀ h₁ h₂, (op.get ctx h₁).parent = (op.get c h₂).parent) } :=
      ⟨ctx, by grind⟩
    for h : i in 0...numOldResults do
      let oldResult := oldOp.getResult i
      let newResult := newOp.getResult i
      -- TODO: fix and use rlet
      match _ : (Rewriter.replaceValue? newCtx oldResult newResult (by grind) (by grind) (by grind)) with
      | none => none
      | some newCtxNoProof =>
        newCtx := ⟨newCtxNoProof, (by grind)⟩
    return Rewriter.eraseOp newCtx oldOp


@[irreducible]
def Rewriter.createBlock (ctx: IRContext) (insertionPoint: Option BlockInsertPoint)
    (hctx : ctx.FieldsInBounds) (hip : insertionPoint.maybe BlockInsertPoint.InBounds ctx)
    : Option (IRContext × BlockPtr) :=
  rlet (ctx, newBlockPtr) ← BlockPtr.allocEmpty ctx
  match h : insertionPoint with
  | some insertionPoint => do
    let ctx ← Rewriter.insertBlock? ctx newBlockPtr insertionPoint (by grind [Option.maybe, cases BlockInsertPoint])
    (ctx, newBlockPtr)
  | none =>
    (ctx, newBlockPtr)

@[irreducible, grind]
def Rewriter.createRegion (ctx: IRContext) : Option (IRContext × RegionPtr) :=
  RegionPtr.allocEmpty ctx

@[irreducible]
def Rewriter.initOpRegions (ctx: IRContext) (opPtr: OperationPtr) (numRegions: Nat)
    (hop : opPtr.InBounds ctx) : Option IRContext :=
  match numRegions with
  | 0 => some ctx
  | Nat.succ n => do
    rlet (ctx, regionPtr) ← Rewriter.createRegion ctx
    let oldRegion := regionPtr.get ctx (by grind)
    let ctx := opPtr.setRegions ctx ((opPtr.get ctx).regions.push regionPtr)
    Rewriter.initOpRegions ctx opPtr n (by grind)

@[grind .]
theorem Rewriter.initOpRegions_fieldsInBounds
    (hx : ctx.FieldsInBounds)
    (heq : initOpRegions ctx opPtr numRegions h₁ = some ctx') :
    ctx'.FieldsInBounds := by
  induction numRegions generalizing ctx <;> sorry --grind [initOpRegions]

@[grind .]
theorem Rewriter.initOpRegions_inBounds_mono (ptr : GenericPtr)
    (heq : initOpRegions ctx opPtr numRegions h₁ = some ctx') :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  induction numRegions generalizing ctx <;>
    grind [initOpRegions, Option.unattach_eq_some_iff]

@[irreducible]
def Rewriter.initOpResults (ctx: IRContext) (opPtr: OperationPtr) (numResults: Nat) (index: Nat := 0) (hop : opPtr.InBounds ctx)
    (hidx : index = opPtr.getNumResults ctx) : IRContext :=
  match numResults with
  | 0 => ctx
  | Nat.succ n =>
    let result: OpResult := { type := (), firstUse := none, index := index, owner := opPtr }
    let ctx := opPtr.pushResult ctx result
    have : opPtr.InBounds ctx := by grind
    have : result.FieldsInBounds ctx := by
      -- TODO(later): write the right lemma somewhere.
      constructor <;> grind [OperationPtr.pushResult, OperationPtr.setResults, OperationPtr.set, OperationPtr.get]
    Rewriter.initOpResults ctx opPtr n (index + 1) (by grind) (by grind)

@[grind .]
theorem Rewriter.initOpResults_fieldsInBounds (hx : ctx.FieldsInBounds) :
    (initOpResults ctx opPtr numResults index h₁ h₂).FieldsInBounds := by
  induction numResults generalizing ctx index
  · grind [initOpResults]
  case succ numResults ih =>
    simp [initOpResults]
    apply ih
    apply OperationPtr.pushResult_fieldsInBounds
    · constructor <;> grind [OperationPtr.pushResult, OperationPtr.setResults, OperationPtr.set, OperationPtr.get]
    · grind

@[grind .]
theorem Rewriter.initOpResults_inBounds_mono (ptr : GenericPtr) :
    ptr.InBounds ctx → ptr.InBounds (initOpResults ctx opPtr numResults index h₁ h₂) := by
  induction numResults generalizing ctx index <;> grind [initOpResults]

@[irreducible]
protected def Rewriter.pushOperand (ctx : IRContext) (opPtr : OperationPtr) (valuePtr : ValuePtr)
    (opPtrInBounds : opPtr.InBounds ctx := by grind) (valueInBounds : valuePtr.InBounds ctx := by grind) (hctx : ctx.FieldsInBounds) : IRContext :=
  let op := (opPtr.get ctx (by grind))
  let index := opPtr.getNumOperands ctx (by grind)
  let operand := { value := valuePtr, owner := opPtr, back := OpOperandPtrPtr.valueFirstUse valuePtr, nextUse := none : OpOperand}
  have : operand.FieldsInBounds ctx := by constructor <;> grind [Option.maybe]
  let ctx := opPtr.pushOperand ctx operand (by grind)
  let ctx := (OpOperandPtr.mk opPtr index).insertIntoCurrent ctx (by grind) (by grind)
  ctx

@[grind .]
theorem Rewriter.pushOperand_inBounds (ptr : GenericPtr) :
    ptr.InBounds (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) ↔
    (ptr.InBounds ctx ∨
     ptr = .opOperand ⟨opPtr, (opPtr.getNumOperands ctx)⟩ ∨
     ptr = .opOperandPtr (.operandNextUse ⟨opPtr, (opPtr.getNumOperands ctx)⟩)) := by
  grind [Rewriter.pushOperand]

@[grind .]
theorem Rewriter.pushOperand_inBounds_mono (ptr : GenericPtr) :
    ptr.InBounds ctx → ptr.InBounds (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃) := by
  grind

@[grind .]
theorem Rewriter.pushOperand_fieldsInBounds :
    (Rewriter.pushOperand ctx opPtr valuePtr h₁ h₂ h₃).FieldsInBounds := by
  grind [Rewriter.pushOperand]

@[irreducible]
def Rewriter.initOpOperands (ctx: IRContext) (opPtr: OperationPtr) (opPtrInBounds : opPtr.InBounds ctx)
    (operands : Array ValuePtr) (hoperands : ∀ oper, oper ∈ operands → oper.InBounds ctx) (hctx : ctx.FieldsInBounds)
    (n : Nat := operands.size) (hn : 0 ≤ n ∧ n ≤ operands.size := by grind) : IRContext :=
  match h : n with
  | 0 => ctx
  | Nat.succ n' =>
    let index := operands.size - n
    let valuePtr := operands[index]'(by grind)
    let ctx := Rewriter.pushOperand ctx opPtr valuePtr (by grind) (by grind) (by grind)
    Rewriter.initOpOperands ctx opPtr (by grind) operands (by grind) (by grind) n' (by grind)

@[grind .]
theorem Rewriter.initOpOperands_fieldsInBounds :
    (initOpOperands ctx opPtr h₁ operands h₂ h₃ n hn).FieldsInBounds := by
  induction n generalizing ctx
  case zero => grind [initOpOperands]
  case succ n ih =>
    simp [initOpOperands]
    grind

@[grind .]
theorem Rewriter.initOpOperands_inBounds_mono (ptr : GenericPtr) :
    ptr.InBounds ctx → ptr.InBounds (initOpOperands ctx opPtr h₁ operands h₂ h₃ n hn) := by
  induction n generalizing ctx
  case zero => grind [initOpOperands]
  case succ n ih =>
    simp [initOpOperands]
    grind

@[irreducible]
def Rewriter.createEmptyOp (ctx : IRContext) (opType : Nat) : Option (IRContext × OperationPtr) :=
  OperationPtr.allocEmpty ctx opType

@[grind .]
theorem Rewriter.createEmptyOp_new_inBounds (h : createEmptyOp ctx opType = some (ctx', op)) :
    op.InBounds ctx' := by
  grind [createEmptyOp]

@[grind .]
theorem Rewriter.createEmptyOp_genericPtr_mono (ptr : GenericPtr) (heq : createEmptyOp ctx type = some (ctx', ptr')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .operation ptr') := by
  grind [createEmptyOp, OperationPtr.allocEmpty_genericPtr_iff']

@[grind .]
theorem Rewriter.createEmptyOp_fieldsInBounds (h : createEmptyOp ctx opType = some (ctx', op)) :
    ctx.FieldsInBounds → ctx'.FieldsInBounds := by
  grind [createEmptyOp]


@[irreducible]
def Rewriter.createOp (ctx: IRContext) (opType: Nat)
    (numResults: Nat) (operands: Array ValuePtr) (numRegions: Nat) (properties: UInt64)
    (insertionPoint: Option InsertPoint)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds ctx)
    (hins : insertionPoint.maybe InsertPoint.InBounds ctx)
    (hx : ctx.FieldsInBounds) : Option (IRContext × OperationPtr) :=
  rlet (ctx, newOpPtr) ← Rewriter.createEmptyOp ctx opType
  have hib : newOpPtr.InBounds ctx := by grind
  have : (newOpPtr.get ctx (by grind)).results = #[] := by
    grind [createEmptyOp, OperationPtr.allocEmpty, Operation.empty]
  have newOpPtrZeroRes: 0 = newOpPtr.getNumResults ctx (by grind) := by grind [OperationPtr.getNumResults]
  let ctx := Rewriter.initOpResults ctx  newOpPtr numResults 0 hib newOpPtrZeroRes
  let ctx := newOpPtr.setProperties ctx properties (by grind)
  have newOpPtrInBounds : newOpPtr.InBounds ctx := by grind
  rlet ctx ← Rewriter.initOpRegions ctx newOpPtr numRegions newOpPtrInBounds
  let ctx := Rewriter.initOpOperands ctx newOpPtr (by grind) operands (by grind) (by grind)
  match _ : insertionPoint with
  | some insertionPoint =>
    rlet ctx ← Rewriter.insertOp? ctx newOpPtr insertionPoint (by grind) (by cases insertionPoint <;> grind (ematch := 6) [Option.maybe]) (by grind) in
    some (ctx, newOpPtr)
  | none =>
    (ctx, newOpPtr)

abbrev ModuleTypeID := 0

unseal Rewriter.createRegion in
@[irreducible]
def IRContext.create : Option (IRContext × OperationPtr) :=
  let ctx : IRContext := {
    nextID := 0,
    operations := Std.HashMap.emptyWithCapacity,
    blocks := Std.HashMap.emptyWithCapacity,
    regions := Std.HashMap.emptyWithCapacity,
    topLevelOp := ⟨0⟩
  }
  -- Note: We inline part of the definition of `createOp` because the above
  -- `ctx` does not satisfy `ctx.FieldsInBounds` because `topLevelOp` is an
  -- invalid pointer.
  rlet (ctx, operation) ← Rewriter.createEmptyOp ctx ModuleTypeID
  have hib : operation.InBounds ctx := by grind
  have : ctx.topLevelOp = ⟨0⟩ := by
    grind [Rewriter.createEmptyOp, OperationPtr.allocEmpty, Operation.empty, OperationPtr.set]
  have hops : ∀ (op : OperationPtr), op.InBounds ctx ↔ op = ⟨0⟩ := by
    grind [Rewriter.createEmptyOp, OperationPtr.allocEmpty, Operation.empty, OperationPtr.set, OperationPtr.InBounds]
  have : (operation.get ctx (by grind)).results = #[] := by
    grind [Rewriter.createEmptyOp, OperationPtr.allocEmpty, Operation.empty]
  have : ∀ (bl : BlockPtr), bl.InBounds ctx ↔ False := by
    grind [Rewriter.createEmptyOp, OperationPtr.allocEmpty, Operation.empty, OperationPtr.set, BlockPtr.InBounds]
  have : ∀ (r : RegionPtr), r.InBounds ctx ↔ False := by
    grind [Rewriter.createEmptyOp, OperationPtr.allocEmpty, Operation.empty, OperationPtr.set, RegionPtr.InBounds]
  have : ctx.nextID = 1 := by
    grind [Rewriter.createEmptyOp, OperationPtr.allocEmpty, Operation.empty, OperationPtr.set, RegionPtr.InBounds]
  have : operation.get ctx (by simp_all) = Operation.empty ModuleTypeID := by
    grind [Rewriter.createEmptyOp, OperationPtr.allocEmpty, Operation.empty, OperationPtr.set, RegionPtr.InBounds]
  rlet ctx ← Rewriter.initOpRegions ctx operation 1 (by grind)
  have : operation = ⟨0⟩ := by grind [Rewriter.createEmptyOp, OperationPtr.allocEmpty]
  have : ctx.topLevelOp = ⟨0⟩ := by
    simp_all [Rewriter.initOpRegions, OperationPtr.setRegions, OperationPtr.set, Rewriter.createRegion]
    grind [RegionPtr.set, RegionPtr.allocEmpty]
  have hop₀ : ∀ (op : OperationPtr), op.InBounds ctx ↔ op = ⟨0⟩ := by
    simp_all [Rewriter.initOpRegions, OperationPtr.setRegions, OperationPtr.set, Rewriter.createRegion]
    simp [OperationPtr.InBounds] at hops
    sorry --grind [Region.empty, RegionPtr.set, OperationPtr.InBounds]
  have : operation.get ctx (by simp_all) =
    { Operation.empty ModuleTypeID with regions := #[⟨1⟩] } := by
    simp_all [Rewriter.initOpRegions, OperationPtr.setRegions, OperationPtr.set, Rewriter.createRegion]
    grind [Operation.empty, RegionPtr.set, RegionPtr.InBounds, RegionPtr.get, OperationPtr.get, RegionPtr.allocEmpty]
  have : ∀ (bl : BlockPtr), bl.InBounds ctx ↔ False := by
    simp_all [Rewriter.initOpRegions, OperationPtr.setRegions, OperationPtr.set, Rewriter.createRegion]
    sorry --grind [Region.empty, RegionPtr.set, BlockPtr.InBounds]
  have : ∀ (r : RegionPtr), r.InBounds ctx ↔ r = ⟨1⟩ := by
    simp_all [Rewriter.initOpRegions, OperationPtr.setRegions, OperationPtr.set, Rewriter.createRegion]
    sorry --grind [Region.empty, RegionPtr.set, RegionPtr.InBounds]
  have : (⟨1⟩ : RegionPtr).get ctx (by simp_all) = Region.empty := by
    simp_all [Rewriter.initOpRegions, OperationPtr.setRegions, OperationPtr.set, Rewriter.createRegion]
    grind [Region.empty, RegionPtr.set, RegionPtr.InBounds, RegionPtr.get, RegionPtr.allocEmpty]
  have : ctx.FieldsInBounds := by
    constructor
    · grind [Operation.empty]
    · sorry -- grind [Operation.FieldsInBounds, Operation.empty]
    · grind
    · grind [Region.FieldsInBounds, Region.empty]
  let moduleRegion := operation.getRegion! ctx 0
  rlet (ctx, block) ← Rewriter.createBlock ctx (some (.atEnd moduleRegion)) (by grind) (by sorry)
  let ctx := { ctx with topLevelOp := operation }
  return (ctx, ⟨0⟩)
