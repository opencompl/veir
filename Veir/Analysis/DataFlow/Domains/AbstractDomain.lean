module

public section

namespace Veir

abbrev Set (α : Type) := α → Prop

namespace Set

abbrev Mem (s : Set α) (a : α) : Prop := s a
instance : Membership α (Set α) := ⟨Set.Mem⟩

abbrev Subset (s₁ s₂ : Set α) := ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂
instance : LE (Set α) := ⟨Set.Subset⟩
instance : HasSubset (Set α) := ⟨(· ≤ ·)⟩

end Set

/-- Typeclass for the `⊤` notation. -/
class Top (α : Type) where
  /-- The top element. -/
  top : α

attribute [reducible] Top.top

/-- Typeclass for the `⊥` notation. -/
class Bot (α : Type) where
  /-- The bottom element. -/
  bot : α

attribute [reducible] Bot.bot

/-- The top element. -/
notation "⊤" => Top.top

/-- The bottom element. -/
notation "⊥" => Bot.bot

namespace Set

instance : Top (Set α) where
  top := fun _ => True

instance : Bot (Set α) where
  bot := fun _ => False

end Set

/-- An order with a greatest element. -/
class OrderTop (α : Type) [LE α] extends Top α where
  /-- `⊤` is the greatest element. -/
  le_top (a : α) : a ≤ ⊤

/-- An order with a least element. -/
class OrderBot (α : Type) [LE α] extends Bot α where
  /-- `⊥` is the least element. -/
  bot_le (a : α) : ⊥ ≤ a

/-- An order with both a greatest and least element. -/
class BoundedOrder (α : Type) [LE α] extends OrderTop α, OrderBot α

/-- Typeclass for the `⊔` notation. -/
class Join (α : Type) where
  /-- The join (least upper bound / supremum). -/
  join : α → α → α

attribute [reducible] Join.join

instance (priority := low) [Join α] : Max α where
  max := Join.join

/-- The join (least upper bound / supremum). -/
notation:68 lhs:68 " ⊔ " rhs:69 => Join.join lhs rhs

/--
An algebraic definition of a join semilattice.
-/
class JoinSemilattice (Domain : Type) 
  extends LE Domain, Std.IsPartialOrder Domain, Join Domain where
  /-- The join is an upper bound on the first argument. -/
  le_join_left (a b : Domain) : a ≤ a ⊔ b

  /-- The join is an upper bound on the second argument. -/
  le_join_right (a b : Domain) : b ≤ a ⊔ b

  /-- The join is the least upper bound. -/
  join_le (a b c : Domain) : a ≤ c → b ≤ c → a ⊔ b ≤ c

/--
An abstract domain is a bounded join semilattice equipped 
with a concretization map.

Each abstract value denotes a set of concrete values via
concretization.
-/
class AbstractDomain (AbstractValue : Type) (ConcreteValue : Type)
    extends JoinSemilattice AbstractValue, BoundedOrder AbstractValue where
  /--
  Concretization. Given an abstract value, returns the set of concrete values it
  denotes.
  -/
  γ : AbstractValue → Set ConcreteValue

  /--
  The top element denotes every concrete value.
  -/
  γ_top : γ ⊤ = ⊤

  /--
  The bottom element denotes no concrete values.
  -/
  γ_bot : γ ⊥ = ⊥

  /--
  The order is monotone (it is sound).
  -/
  γ_monotone (a b : AbstractValue) : a ≤ b → γ a ⊆ γ b

end Veir
