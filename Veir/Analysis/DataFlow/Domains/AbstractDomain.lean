module

public section

namespace Veir

@[expose]
def Set (α : Type) := α → Prop

namespace Set

@[expose]
def Mem (s : Set α) (a : α) : Prop := s a
instance : Membership α (Set α) := ⟨Set.Mem⟩

@[expose]
def Subset (s₁ s₂ : Set α) := ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂
instance : LE (Set α) := ⟨Set.Subset⟩
instance : HasSubset (Set α) := ⟨(· ≤ ·)⟩

end Set

/-- Typeclass for the `⊤` notation. -/
class Top (α : Type) where
  /-- The top element. -/
  top : α

/-- Typeclass for the `⊥` notation. -/
class Bot (α : Type) where
  /-- The bottom element. -/
  bot : α

/-- The top element. -/
notation "⊤" => Top.top

/-- The bottom element. -/
notation "⊥" => Bot.bot

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

theorem le_top [LE α] [OrderTop α] (a : α) : a ≤ (⊤ : α) :=
  OrderTop.le_top a

theorem bot_le [LE α] [OrderBot α] (a : α) : (⊥ : α) ≤ a :=
  OrderBot.bot_le a

/--
An algebraic definition of a partial order.
-/
class PartialOrder (Domain : Type) extends BEq Domain, LE Domain where
  /-- Preorder (reflexive + transitive). -/
  le_refl (a : Domain) : a ≤ a
  le_trans (a b c : Domain) : a ≤ b → b ≤ c → a ≤ c

  /-- Partial order: preorder + antisymmetry. -/
  le_antisymm (a b : Domain) : a ≤ b → b ≤ a → a = b

/--
An algebraic definition of a join semilattice.
-/
class JoinSemilattice (Domain : Type) extends PartialOrder Domain where
  /-- Also called a least upper bound or supremum. -/
  join : Domain → Domain → Domain

  /-- The join is an upper bound on the first argument. -/
  le_join_left (a b : Domain) : a ≤ join a b

  /-- The join is an upper bound on the second argument. -/
  le_join_right (a b : Domain) : b ≤ join a b

  /-- The join is the least upper bound. -/
  join_le (a b c : Domain) : a ≤ c → b ≤ c → join a b ≤ c

/--
An abstract domain is a join semilattice equipped with a concretization map.

Each abstract value denotes a set of concrete values, represented as a
`Set ConcreteValue`.
-/
class AbstractDomain (AbstractValue : Type) (ConcreteValue : Type)
    extends JoinSemilattice AbstractValue, BoundedOrder AbstractValue where
  /--
  Concretization. Given an abstract value, returns the set of concrete values it
  denotes.
  -/
  γ : AbstractValue → Set ConcreteValue

  /--
  The order is monotone (it is sound).
  -/
  γ_monotone (a b : AbstractValue) : a ≤ b → γ a ⊆ γ b

end Veir
