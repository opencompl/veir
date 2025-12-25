import Veir.IR.Basic
import Veir.IR.Grind

namespace Veir

/-
  Use def chain for operands.
-/

@[irreducible]
def OpOperandPtr.removeFromCurrent (ctx: IRContext) (operandPtr: OpOperandPtr)
    (operandIn: operandPtr.InBounds ctx := by grind)
    (ctxInBounds: ctx.FieldsInBounds := by grind) : IRContext :=
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

@[irreducible]
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

@[grind .]
theorem OperationPtr.linkBetween_fieldsInBounds (hx : ctx.FieldsInBounds) :
    (linkBetween self ctx prevOp nextOp h₁ h₂ h₃).FieldsInBounds := by
  unfold linkBetween; simp only; split <;> grind

/--
  Set `self` parent to be `parent`.
  Checks that `self` does not already have a parent.
  TODO: We should also check that `self` does not contain `parent`.
-/
@[irreducible]
def OperationPtr.setParentWithCheck (self: OperationPtr) (ctx: IRContext) (parent: BlockPtr)
    (selfIn: self.InBounds ctx := by grind) : Option IRContext :=
  match (self.get ctx (by grind)).parent with
  | some _ => none
  | none => self.setParent ctx (some parent)

@[grind .]
theorem OperationPtr.setParentWithCheck_fieldsInBounds
    (h₁ : ctx.FieldsInBounds) (h₂ : self.InBounds ctx) (h₃ : parent.InBounds ctx) :
    (setParentWithCheck self ctx parent h₂).maybe₁ IRContext.FieldsInBounds := by
  grind [setParentWithCheck, Option.maybe₁]

@[grind =>]
theorem OperationPtr.setParentWithCheck_fieldsInBounds_some
    (h₁ : ctx.FieldsInBounds) (h₂ : self.InBounds ctx) (h₃ : parent.InBounds ctx)
    (heq : setParentWithCheck self ctx parent h₂ = some newCtx) :
    newCtx.FieldsInBounds := by
  grind [setParentWithCheck, Option.maybe₁]

@[grind =>]
theorem OperationPtr.setParentWithCheck_inBounds (ptr : GenericPtr)
    (h : self.InBounds ctx)
    (heq : setParentWithCheck self ctx parent h = some newCtx) :
    ptr.InBounds newCtx ↔ ptr.InBounds ctx := by
  grind [setParentWithCheck]

@[irreducible]
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

/-
  Block linked list.
-/

@[irreducible]
def BlockPtr.linkBetween (self: BlockPtr) (ctx: IRContext)
    (prevBlock: Option BlockPtr) (nextBlock: Option BlockPtr)
    (selfIn: self.InBounds ctx := by grind)
    (prevIn: ∀ prev, prevBlock = some prev → (prev.InBounds ctx) := by grind)
    (nextIn: ∀ next, nextBlock = some next → (next.InBounds ctx) := by grind) : IRContext :=
  let ctx := self.setPrevBlock ctx prevBlock
  let ctx := self.setNextBlock ctx nextBlock
  match _ : prevBlock with
  | none =>
    match _ : nextBlock with
    | none => ctx
    | some nextBlock => nextBlock.setPrevBlock ctx (some self)
  | some prevBlock =>
    let ctx := prevBlock.setNextBlock ctx (some self)
    match _ : nextBlock with
    | none => ctx
    | some nextBlock => nextBlock.setPrevBlock ctx (some self)

@[grind =]
theorem BlockPtr.linkBetween_inBounds (ptr : GenericPtr) :
    ptr.InBounds (linkBetween self ctx prevBlock nextBlock h₁ h₂ h₃) ↔ ptr.InBounds ctx := by
  unfold linkBetween; grind

@[grind .]
theorem BlockPtr.linkBetween_fieldsInBounds (hx : ctx.FieldsInBounds) :
    (linkBetween self ctx prevBlock nextBlock h₁ h₂ h₃).FieldsInBounds := by
  unfold linkBetween; simp only; split <;> grind
/--
  Set `self` parent to be `parent`.
  Checks that `self` does not already have a parent.
  TODO: We should also check that `self` does not contain `parent`.
-/
@[irreducible]
def BlockPtr.setParentWithCheck (self: BlockPtr) (ctx: IRContext) (parent: RegionPtr)
    (selfIn: self.InBounds ctx := by grind) : Option IRContext :=
  match (self.get ctx (by grind)).parent with
  | some _ => none
  | none => self.setParent ctx (some parent)

@[grind .]
theorem BlockPtr.setParentWithCheck_fieldsInBounds
    (h₁ : ctx.FieldsInBounds) (h₂ : self.InBounds ctx) (h₃ : parent.InBounds ctx) :
    (setParentWithCheck self ctx parent h₂).maybe₁ IRContext.FieldsInBounds := by
  grind [setParentWithCheck, Option.maybe₁]

@[grind =>]
theorem BlockPtr.setParentWithCheck_fieldsInBounds_some
    (h₁ : ctx.FieldsInBounds) (h₂ : self.InBounds ctx) (h₃ : parent.InBounds ctx)
    (heq : setParentWithCheck self ctx parent h₂ = some newCtx) :
    newCtx.FieldsInBounds := by
  grind [setParentWithCheck, Option.maybe₁]

@[grind =>]
theorem BlockPtr.setParentWithCheck_inBounds (ptr : GenericPtr)
    (h : self.InBounds ctx)
    (heq : setParentWithCheck self ctx parent h = some newCtx) :
    ptr.InBounds newCtx ↔ ptr.InBounds ctx := by
  grind [setParentWithCheck]

@[irreducible]
def BlockPtr.linkBetweenWithParent (self: BlockPtr) (ctx: IRContext)
    (prevBlock: Option BlockPtr) (nextBlock: Option BlockPtr)
    (parent: RegionPtr)
    (selfIn: self.InBounds ctx := by grind)
    (prevIn: ∀ prev, prevBlock = some prev → (prev.InBounds ctx) := by grind)
    (nextIn: ∀ next, nextBlock = some next → (next.InBounds ctx) := by grind)
    (parentIn : parent.InBounds ctx := by grind) : Option IRContext :=
  let ctx := self.linkBetween ctx prevBlock nextBlock
  rlet ctx ← self.setParentWithCheck ctx parent
  match _ : prevBlock with
    | none =>
      let ctx := parent.setFirstBlock ctx (some self)
      match _ : nextBlock with
      | none => parent.setLastBlock ctx (some self)
      | some nextBlock => ctx
    | some prevBlock =>
      match _ : nextBlock with
      | none => parent.setLastBlock ctx (some self)
      | some nextBlock => ctx

@[grind .]
theorem BlockPtr.linkBetweenWithParent_inBounds (ptr : GenericPtr)
    (heq : linkBetweenWithParent self ctx prevBlock nextBlock parent h₁ h₂ h₃ h₄ = some newCtx) :
    ptr.InBounds newCtx ↔ ptr.InBounds ctx := by
  unfold linkBetweenWithParent at heq
  grind

@[grind .]
theorem BlockPtr.linkBetweenWithParent_fieldsInBounds (hx : ctx.FieldsInBounds)
    (heq : linkBetweenWithParent self ctx prevBlock nextBlock parent h₁ h₂ h₃ h₄ = some newCtx) :
    newCtx.FieldsInBounds := by
  unfold linkBetweenWithParent at heq
  split at heq <;> grind
