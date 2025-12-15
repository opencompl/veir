import Mlir.Core
import Mlir.Rewriter.LinkedList

namespace Mlir

/--
- A position in the IR where we can insert an operation.
-/
inductive InsertPoint where
  | Before (op: OperationPtr)
  | AtEnd (block: BlockPtr)
deriving DecidableEq

@[grind]
def InsertPoint.InBounds : InsertPoint → IRContext → Prop
| Before op => op.InBounds
| AtEnd bl => bl.InBounds

@[grind =]
theorem InsertPoint.inBounds_before : (Before op).InBounds ctx ↔ op.InBounds ctx := by rfl
@[grind =]
theorem InsertPoint.inBounds_atEnd : (AtEnd bl).InBounds ctx ↔ bl.InBounds ctx := by rfl

@[grind]
def InsertPoint.block! (insertionPoint : InsertPoint) (ctx : IRContext) : Option BlockPtr :=
  match insertionPoint with
  | InsertPoint.Before op => (op.get! ctx).parent
  | InsertPoint.AtEnd b => b

def InsertPoint.block (insertionPoint : InsertPoint) (ctx : IRContext)
    (hIn : insertionPoint.InBounds ctx := by grind) : Option BlockPtr :=
  match insertionPoint with
  | InsertPoint.Before op => (op.get ctx (by grind)).parent
  | InsertPoint.AtEnd b => b

@[grind =]
theorem InsertPoint.block!_eq_block (insertionPoint : InsertPoint) (ctx : IRContext)
    (hIn : insertionPoint.InBounds ctx) :
    insertionPoint.block! ctx = insertionPoint.block ctx hIn := by
  cases insertionPoint <;> grind [InsertPoint.block!, InsertPoint.block]

@[grind .]
theorem InsertPoint.block_InBounds {insertionPoint : InsertPoint} {ctx : IRContext}
    (ctxFieldsInBounds : ctx.FieldsInBounds) (hIn : insertionPoint.InBounds ctx) :
    insertionPoint.block ctx hIn = some blockPtr →
    insertionPoint.InBounds ctx →
    blockPtr.InBounds ctx := by
  simp only [InsertPoint.block]
  grind

/- set_option pp.proofs true -/
/- set_option pp.showLetValues true -/

/--
- Insert an operation at a given location.
-/
@[grind]
def Rewriter.insertOp? (ctx: IRContext) (newOp: OperationPtr) (insertionPoint: InsertPoint)
    (newOpIn: newOp.InBounds ctx := by grind)
    (insIn : insertionPoint.InBounds ctx)
    (ctxInBounds: ctx.FieldsInBounds) : Option IRContext :=
  match _ : insertionPoint with
    | InsertPoint.Before existingOp =>
      rlet parent ← (existingOp.get ctx (by grind)).parent
      let prev := (existingOp.get ctx (by grind)).prev
      let next := some existingOp
      newOp.linkBetweenWithParent ctx prev next parent (by grind) (by grind) (by grind) (by grind)
    | InsertPoint.AtEnd block =>
      let parent := block
      let prev := (block.get ctx (by grind)).lastOp
      let next := none
      newOp.linkBetweenWithParent ctx prev next parent (by grind) (by grind) (by grind) (by grind)

@[irreducible]
def Rewriter.detachOp (ctx: IRContext) (hctx : ctx.FieldsInBounds) (op: OperationPtr) (hIn : op.InBounds ctx) (hasParent: (op.get ctx hIn).parent.isSome) : IRContext :=
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
    (detachOp ctx hctx op hIn hasParent).FieldsInBounds := by
  simp only [detachOp]
  split <;> grind

/--
- Erase an operation and free it from memory.
- TODO: free memory here
-/

@[irreducible, inline]
def Rewriter.eraseOpStart (ctx: IRContext) (hctx : ctx.FieldsInBounds) (op: OperationPtr) (hop : op.InBounds ctx) (hasParent: (op.get ctx hop).parent.isSome) := Id.run do
  let mut newCtx : { c : IRContext // c.FieldsInBounds ∧ ∀ (ptr : GenericPtr), ptr.InBounds ctx ↔ ptr.InBounds c} :=
    ⟨Rewriter.detachOp ctx hctx op hop hasParent, by grind⟩
  for h : index in 0 ... (op.getNumOperands ctx (by grind)) do
    let ctx' := (OpOperandPtr.mk op index).removeFromCurrent newCtx (by
       have := newCtx.property.2 (.opOperand (.mk op index))
       grind [OperationPtr.getNumOperands, OpOperandPtr.InBounds]) (by grind) -- TODO: try to not unfold `get`, maybe some lemma for op.InBounds + index < .. → (.mk op index).InBounds
    newCtx := ⟨ctx', by grind⟩
  newCtx

@[grind .]
theorem Rewriter.eraseOpStart_inBounds (ptr : GenericPtr) :
    ptr.InBounds (eraseOpStart ctx hctx op hIn hasParent) ↔ ptr.InBounds ctx := by
  grind

@[grind .]
theorem Rewriter.eraseOpStart_fieldsInBounds :
    ctx.FieldsInBounds → (eraseOpStart ctx hctx op hIn hasParent).val.FieldsInBounds := by
  grind

@[irreducible]
def Rewriter.eraseOp (ctx: IRContext) (op: OperationPtr) (hctx : ctx.FieldsInBounds := by grind)
    (hop : op.InBounds ctx := by grind) (hasParent: (op.get ctx hop).parent.isSome := by grind) : IRContext := Id.run do
  let ctx := eraseOpStart ctx hctx op hop hasParent
  { ctx.val with operations := ctx.val.operations.erase op }

/-
Remark: the fact that `eraseOp` preserves `FieldsInBounds` relies on the fact
that the context is well formed.  Indeed, it is true because the only pointers
to the operands are in the doubly linked list that we patch.  I think in
addition we need to know that the results of the operation we are removing are
never used, which is ensured in the call to `eraseOp` in `replaceOp?` below for
example.
-/

/--
- A position in the IR where we can insert an operation.
-/
inductive BlockInsertPoint where
  | Before (op: BlockPtr)
  | AtEnd (block: RegionPtr)

@[grind]
def BlockInsertPoint.InBounds : BlockInsertPoint → IRContext → Prop
| Before op => op.InBounds
| AtEnd bl => bl.InBounds
@[grind =]
theorem BlockInsertPoint.inBounds_before : (Before op).InBounds ctx ↔ op.InBounds ctx := by rfl
@[grind =]
theorem BlockInsertPoint.inBounds_atEnd : (AtEnd bl).InBounds ctx ↔ bl.InBounds ctx := by rfl

@[irreducible]
private def Rewriter.insertBlockAfter? (ctx: IRContext) (newBlock: BlockPtr) (existingBlock: BlockPtr)
    (newBlockIn: newBlock.InBounds ctx := by grind)
    (existingBlockIn: existingBlock.InBounds ctx := by grind)
    (ctxInBounds: ctx.FieldsInBounds) : Option IRContext := do
  rlet parent ← (existingBlock.get ctx (by grind)).parent
  let ctx := existingBlock.linkNextBlock ctx newBlock
  rlet ctx ← newBlock.setParentWithCheck ctx parent (by grind)
  let nextBlock := (newBlock.get ctx (by grind)).next
  if h : nextBlock = none then
    parent.setLastBlock ctx (some newBlock) (by grind (ematch := 10))
  else
    ctx

@[irreducible]
private def Rewriter.insertBlockBefore? (ctx: IRContext) (newBlock: BlockPtr) (existingBlock: BlockPtr)
    (newBlockIn: newBlock.InBounds ctx := by grind)
    (existingBlockIn: existingBlock.InBounds ctx := by grind)
    (ctxInBounds: ctx.FieldsInBounds) : Option IRContext := do
  rlet parent ← (existingBlock.get ctx (by grind)).parent
  let ctx := existingBlock.linkPrevBlock ctx newBlock
  rlet ctx ← newBlock.setParentWithCheck ctx parent (by grind)
  let prevBlock := (newBlock.get ctx (by grind)).prev
  if h : prevBlock = none then
    return parent.setFirstBlock ctx (some newBlock) (by grind (ematch := 10))
  else
    ctx

@[irreducible]
private def Rewriter.insertBlockInEmptyRegion? (ctx: IRContext) (newBlock: BlockPtr) (region: RegionPtr)
    (newBlockIn: newBlock.InBounds ctx := by grind)
    (regionIn: region.InBounds ctx := by grind) : Option IRContext := do
  rlet ctx ← newBlock.setParentWithCheck ctx region (by grind)
  let ctx := region.setFirstBlock ctx (some newBlock)
  let ctx := region.setLastBlock ctx (some newBlock)
  let ctx := newBlock.setPrevBlock ctx none
  let ctx := newBlock.setNextBlock ctx none
  return ctx

/--
- Insert a block at a given location.
-/
@[irreducible]
def Rewriter.insertBlock? (ctx: IRContext) (newBlock: BlockPtr) (insertionPoint:
    BlockInsertPoint) (hib : insertionPoint.InBounds ctx := by grind)
    (newBlockIn: newBlock.InBounds ctx := by grind)
    (ctxInBounds: ctx.FieldsInBounds := by grind) : Option IRContext :=
  match h : insertionPoint with
  | BlockInsertPoint.Before existingBlock =>
    Rewriter.insertBlockBefore? ctx newBlock existingBlock (by grind) (by grind) ctxInBounds
  | BlockInsertPoint.AtEnd region =>
    match h : (region.get ctx (by grind)).lastBlock with
    | none => Rewriter.insertBlockInEmptyRegion? ctx newBlock region (by grind) (by grind)
    | some lastBlock => Rewriter.insertBlockAfter? ctx newBlock lastBlock (by grind) (by grind) ctxInBounds

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
