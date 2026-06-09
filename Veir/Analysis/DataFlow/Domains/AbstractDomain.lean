module

public section

namespace Veir

@[expose]
def Set (α : Type) := α → Prop

namespace Set

def Mem (s : Set α) (a : α) : Prop := s a
instance : Membership α (Set α) := ⟨Set.Mem⟩

def Subset (s₁ s₂ : Set α) := ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂
instance : LE (Set α) := ⟨Set.Subset⟩
instance : HasSubset (Set α) := ⟨(· ≤ ·)⟩

end Set

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
    extends JoinSemilattice AbstractValue where
  /--
  Concretization. Given an abstract value, returns the set of concrete values it
  denotes.
  -/
  γ : AbstractValue → Set ConcreteValue

  /--
  The order coincides with concretization inclusion.
  Monotonicity (soundness of the order): a ≤ b → γ a ⊆ γ b
  Reflection (completeness of the order): γ a ⊆ γ b → a ≤ b
  -/
  le_iff_γ (a b : AbstractValue) : a ≤ b ↔ γ a ⊆ γ b

end Veir
