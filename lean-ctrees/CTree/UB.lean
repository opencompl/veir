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
  hasUB : α → Prop

instance [UB : HasUB α] [UB' : HasUB β] : HasUB (α ⊕ β) where
  hasUB := fun
    | .inl x => UB.hasUB x
    | .inr x => UB'.hasUB x

instance : HasUB UBEIn where
  hasUB := fun _ => True

@[default_instance]
instance (priority := low) : HasUB α where
  hasUB := fun _ => False

end CTree

end
