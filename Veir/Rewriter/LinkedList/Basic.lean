module

public import Veir.IR
public import Veir.IR.Grind

namespace Mlir

public section

/-
  Use def chain for operands.
-/

def OpOperandPtr.removeFromCurrent (ctx: IRContext) (operandPtr: OpOperandPtr)
    (operandIn: operandPtr.InBounds ctx := by grind)
    (ctxInBounds: ctx.FieldsInBounds) : IRContext :=
  let operand := operandPtr.get ctx
  let ctx := operand.back.set ctx operand.nextUse
  match hNextUse: operand.nextUse with
  | none => ctx
  | some nextPtr => nextPtr.setBack ctx operand.back

@[grind .]
theorem OpOperandPtr.removeFromCurrent_fieldsInBounds :
    (removeFromCurrent ctx operandPtr h₁ h₂).FieldsInBounds := by
  grind [removeFromCurrent]

@[grind =]
theorem OpOperandPtr.removeFromCurrent_inBounds (ptr : GenericPtr) :
    ptr.InBounds (removeFromCurrent ctx operand h₁ h₂) ↔ ptr.InBounds ctx := by
  grind [removeFromCurrent]

def OpOperandPtr.insertIntoCurrent (ctx: IRContext) (operandPtr: OpOperandPtr)
    (operandIn: operandPtr.InBounds ctx := by grind) (ctxInBounds: ctx.FieldsInBounds) : IRContext :=
  let value := (operandPtr.get ctx).value
  let ctx := operandPtr.setBack ctx (OpOperandPtrPtr.valueFirstUse value)
  let newNextUse := value.getFirstUse ctx
  let ctx := operandPtr.setNextUse ctx newNextUse
  let ctx := value.setFirstUse ctx operandPtr
  match hNextUse: newNextUse with
  | none => ctx
  | some nextUse => nextUse.setBack ctx (OpOperandPtrPtr.operandNextUse operandPtr)

@[grind .]
theorem OpOperandPtr.insertIntoCurrent_fieldsInBounds :
    (insertIntoCurrent ctx operandPtr h₁ h₂).FieldsInBounds := by
  grind [insertIntoCurrent]

@[grind =]
theorem OpOperandPtr.insertIntoCurrent_inBounds (ptr : GenericPtr) :
    ptr.InBounds (insertIntoCurrent ctx operand h₁ h₂) ↔ ptr.InBounds ctx := by
  grind [insertIntoCurrent]

/-
  Operation linked list.
-/

def OperationPtr.linkBetween (self: OperationPtr) (ctx: IRContext)
    (prevOp: Option OperationPtr) (nextOp: Option OperationPtr)
    (selfIn: self.InBounds ctx := by grind)
    (prevIn: ∀ prev, prevOp = some prev → (prev.InBounds ctx) := by grind)
    (nextIn: ∀ next, nextOp = some next → (next.InBounds ctx) := by grind) : IRContext :=
  let ctx := self.setPrevOp ctx prevOp
  let ctx := self.setNextOp ctx nextOp
    match _ : prevOp with
    | none =>
      match _ : nextOp with
      | none => ctx
      | some nextOp => nextOp.setPrevOp ctx (some self)
    | some prevOp =>
      let ctx := prevOp.setNextOp ctx (some self)
      match _ : nextOp with
      | none => ctx
      | some nextOp => nextOp.setPrevOp ctx (some self)

@[grind =]
theorem OperationPtr.linkBetween_inBounds (ptr : GenericPtr) :
    ptr.InBounds (linkBetween self ctx prevOp nextOp h₁ h₂ h₃) ↔ ptr.InBounds ctx := by
  unfold linkBetween; grind

/--
  Set `self` parent to be `parent`.
  Checks that `self` does not already have a parent.
  TODO: We should also check that `self` does not contain `parent`.
-/
def OperationPtr.setParentWithCheck (self: OperationPtr) (ctx: IRContext) (parent: BlockPtr)
    (selfIn: self.InBounds ctx := by grind) : Option IRContext :=
  match (self.get ctx (by grind)).parent with
  | some _ => none
  | none => self.setParent ctx (some parent)

@[grind .]
theorem OperationPtr.setParentWithCheck_fieldsInBounds
    (h₁ : ctx.FieldsInBounds) (h₂ : self.InBounds ctx) (h₃ : parent.InBounds ctx) :
    (setParentWithCheck self ctx parent h₂).maybe₁ IRContext.FieldsInBounds := by
  grind [setParentWithCheck, Option.maybe₁_def]

@[grind =>]
theorem OperationPtr.setParentWithCheck_fieldsInBounds_some
    (h₁ : ctx.FieldsInBounds) (h₂ : self.InBounds ctx) (h₃ : parent.InBounds ctx)
    (heq : setParentWithCheck self ctx parent h₂ = some newCtx) :
    newCtx.FieldsInBounds := by
  grind [setParentWithCheck, Option.maybe₁_def]

@[grind =>]
theorem OperationPtr.setParentWithCheck_inBounds (ptr : GenericPtr)
    (h : self.InBounds ctx)
    (heq : setParentWithCheck self ctx parent h = some newCtx) :
    ptr.InBounds newCtx ↔ ptr.InBounds ctx := by
  grind [setParentWithCheck]

/-
  Block linked list.
-/

/--
  Add previous and next links to `newBlock`, linking it after `self`.
  In particular, this does not update any parent pointers.
-/
def BlockPtr.linkNextBlock (self: BlockPtr) (ctx: IRContext) (newBlock: BlockPtr)
    (opIn: self.InBounds ctx := by grind)
    (newBlockIn: newBlock.InBounds ctx := by grind)
    (ctxInBounds: ctx.FieldsInBounds := by grind) : IRContext :=
  let nextOp := (self.get ctx).next
  -- Set the new op's next and previous pointers
  let ctx := newBlock.setPrevBlock ctx (some self)
  let ctx := newBlock.setPrevBlock ctx nextOp
  -- Update self
  let ctx := self.setNextBlock ctx (some newBlock)
  -- Update next op if it exists
  match heq : nextOp with
  | none => ctx
  | some nextOp => nextOp.setPrevBlock ctx (some newBlock) (by grind (ematch := 10))

@[grind =]
theorem BlockPtr.linkNextBlock_inBounds (ptr : GenericPtr) :
    ptr.InBounds (linkNextBlock self ctx newBlock h₁ h₂ h₃) ↔ ptr.InBounds ctx := by
  simp [linkNextBlock] <;> grind

@[grind .]
theorem BlockPtr.linkNextBlock_fieldsInBounds :
    (linkNextBlock self ctx newBlock h₁ h₂ h₃).FieldsInBounds := by
  grind [linkNextBlock]


@[grind .]
theorem OperationPtr.linkBetween_fieldsInBounds (hx : ctx.FieldsInBounds) :
    (linkBetween self ctx prevOp nextOp h₁ h₂ h₃).FieldsInBounds := by
  unfold linkBetween; simp only; split <;> grind

def OperationPtr.linkBetweenWithParent (self: OperationPtr) (ctx: IRContext)
    (prevOp: Option OperationPtr) (nextOp: Option OperationPtr)
    (parent: BlockPtr)
    (selfIn: self.InBounds ctx := by grind)
    (prevIn: ∀ prev, prevOp = some prev → (prev.InBounds ctx) := by grind)
    (nextIn: ∀ next, nextOp = some next → (next.InBounds ctx) := by grind)
    (parentIn : parent.InBounds ctx := by grind) : Option IRContext :=
  let ctx := self.linkBetween ctx prevOp nextOp
  rlet ctx ← self.setParentWithCheck ctx parent
  match _ : prevOp with
    | none =>
      let ctx := parent.setFirstOp ctx (some self)
      match _ : nextOp with
      | none => parent.setLastOp ctx (some self)
      | some nextOp => ctx
    | some prevOp =>
      match _ : nextOp with
      | none => parent.setLastOp ctx (some self)
      | some nextOp => ctx

@[grind .]
theorem OperationPtr.linkBetweenWithParent_inBounds (ptr : GenericPtr)
    (heq : linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some newCtx) :
    ptr.InBounds newCtx ↔ ptr.InBounds ctx := by
  unfold linkBetweenWithParent at heq; grind

@[grind .]
theorem OperationPtr.linkBetweenWithParent_fieldsInBounds (hx : ctx.FieldsInBounds)
    (heq : linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some newCtx) :
    newCtx.FieldsInBounds := by
  unfold linkBetweenWithParent at heq
  split at heq <;> grind

/--
  Add previous and next links to `newOp`, linking it before `self`.
  In particular, this does not update any parent pointers.
-/
def BlockPtr.linkPrevBlock (self: BlockPtr) (ctx: IRContext) (newBlock: BlockPtr)
    (opIn: self.InBounds ctx := by grind)
    (newBlockIn: newBlock.InBounds ctx := by grind)
    (ctxInBounds: ctx.FieldsInBounds := by grind) : IRContext :=
  let prevOp := (self.get ctx).prev
  -- Set the new op's next and previous pointers
  let ctx := newBlock.setNextBlock ctx (some self)
  let ctx := newBlock.setPrevBlock ctx prevOp
  -- Update self
  let ctx := self.setPrevBlock ctx (some newBlock)
  -- Update previous op if it exists
  match heq : prevOp with
  | none => ctx
  | some prevOp => prevOp.setNextBlock ctx (some newBlock) (by grind (ematch := 10))
@[grind =]
theorem BlockPtr.linkPrevBlock_inBounds (ptr : GenericPtr) :
    ptr.InBounds (linkPrevBlock self ctx newBlock h₁ h₂ h₃) ↔ ptr.InBounds ctx := by
  simp [linkPrevBlock] <;> grind

@[grind .]
theorem BlockPtr.linkPrevBlock_fieldsInBounds :
    (linkPrevBlock self ctx newBlock h₁ h₂ h₃).FieldsInBounds := by
  grind [linkPrevBlock]

/--
  Set `self` parent to be `parent`.
  Checks that `self` does not already have a parent.
  TODO: We should also check that `self` does not contain `parent`.
-/
def BlockPtr.setParentWithCheck (self: BlockPtr) (ctx: IRContext) (parent: RegionPtr)
    (selfIn: self.InBounds ctx := by grind) : Option IRContext :=
  match (self.get ctx (by grind)).parent with
  | some _ => none
  | none => self.setParent ctx (some parent)

@[grind .]
theorem BlockPtr.setParentWithCheck_inBounds (ptr :
    GenericPtr) (h : ptr.InBounds ctx) (heq : setParentWithCheck self ctx parent h₁ = some ctx') :
    ptr.InBounds ctx' := by
  simp [setParentWithCheck] at * <;> grind

@[grind .]
theorem BlockPtr.setParentWithCheck_fieldsInBounds
    (h₁ : ctx.FieldsInBounds) (h₂ : self.InBounds ctx) (h₃ : parent.InBounds ctx) :
    (setParentWithCheck self ctx parent h₂).maybe₁ IRContext.FieldsInBounds := by
  grind [setParentWithCheck, Option.maybe₁_def]
