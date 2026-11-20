module

public section

namespace CTree

/-- Effect representing an immediate undefined behavior -/
structure UBEIn : Type u where

/-- Effect representing an immediate undefined behavior -/
@[expose]
def UBE : UBEIn.{u} → Type
  | .mk => Empty

/-- Typeclass that recursively looks for a UB effect -/
class HasUB (α : Type u) where
  isUB : α → Prop

instance [UB : HasUB α] [UB' : HasUB β] : HasUB (α ⊕ β) where
  isUB := fun
    | .inl x => UB.isUB x
    | .inr x => UB'.isUB x

instance : HasUB UBEIn where
  isUB := fun _ => True

@[simp, grind =]
theorem HasUB.isUB_inl [HasUB α] [HasUB β] (a : α) :
    HasUB.isUB (Sum.inl a : α ⊕ β) ↔ HasUB.isUB a := Iff.rfl

@[simp, grind =]
theorem HasUB.isUB_inr [HasUB α] [HasUB β] (b : β) :
    HasUB.isUB (Sum.inr b : α ⊕ β) ↔ HasUB.isUB b := Iff.rfl

@[simp, grind .]
theorem HasUB.isUB_ube (e : UBEIn) : HasUB.isUB e := trivial

@[default_instance]
instance (priority := low) : HasUB α where
  isUB := fun _ => False

end CTree

end
