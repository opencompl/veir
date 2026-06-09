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

/-- Typeclass for the `⊔` notation. -/
class Join (α : Type) where
  /-- The join (least upper bound / supremum). -/
  join : α → α → α

attribute [reducible] Join.join

instance (priority := low) [Join α] : Max α where
  max := Join.join

/-- The join (least upper bound / supremum). -/
notation:68 lhs:68 " ⊔ " rhs:69 => Join.join lhs rhs

@[simp] theorem max_eq_join [Join α] (a b : α) : max a b = a ⊔ b := rfl

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

namespace JoinSemilattice

instance [JoinSemilattice α] : Std.LawfulOrderSup α where
  max_le_iff a b c := by
    constructor
    · intro h
      exact ⟨
        Std.IsPreorder.le_trans _ _ _ (le_join_left a b) h,
        Std.IsPreorder.le_trans _ _ _ (le_join_right a b) h
      ⟩
    · intro h
      exact join_le a b c h.1 h.2

instance [JoinSemilattice α] : Std.IdempotentOp (max : α → α → α) where
  idempotent a := by
    apply Std.IsPartialOrder.le_antisymm
    · exact join_le a a a (Std.IsPreorder.le_refl a) (Std.IsPreorder.le_refl a)
    · exact le_join_left a a

instance [JoinSemilattice α] : Std.Commutative (max : α → α → α) where
  comm a b := by
    apply Std.IsPartialOrder.le_antisymm
    · exact join_le a b (b ⊔ a) (le_join_right b a) (le_join_left b a)
    · exact join_le b a (a ⊔ b) (le_join_right a b) (le_join_left a b)

instance [JoinSemilattice α] : Std.Associative (max : α → α → α) where
  assoc a b c := by
    apply Std.IsPartialOrder.le_antisymm
    · apply join_le
      · exact join_le a b (a ⊔ (b ⊔ c))
          (le_join_left a (b ⊔ c))
          (Std.IsPreorder.le_trans _ _ _ (le_join_left b c) (le_join_right a (b ⊔ c)))
      · exact Std.IsPreorder.le_trans _ _ _ (le_join_right b c) (le_join_right a (b ⊔ c))
    · apply join_le
      · exact Std.IsPreorder.le_trans _ _ _ (le_join_left a b) (le_join_left (a ⊔ b) c)
      · exact join_le b c ((a ⊔ b) ⊔ c)
          (Std.IsPreorder.le_trans _ _ _ (le_join_right a b) (le_join_left (a ⊔ b) c))
          (le_join_right (a ⊔ b) c)

end JoinSemilattice

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
