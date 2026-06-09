module

public section

namespace Veir

abbrev Set (α : Type) := α → Prop

namespace Set

abbrev Mem (s : Set α) (a : α) : Prop := s a
instance : Membership α (Set α) := ⟨Set.Mem⟩
/- @[simp] theorem mem_def (s : Set α) (a : α) : a ∈ s ↔ s a := Iff.rfl -/

abbrev Subset (s₁ s₂ : Set α) := ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂
instance : LE (Set α) := ⟨Set.Subset⟩
instance : HasSubset (Set α) := ⟨(· ≤ ·)⟩
/- @[simp] theorem subset_def (s₁ s₂ : Set α) : s₁ ⊆ s₂ ↔ ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂ := Iff.rfl -/

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

/- @[simp] theorem mem_top (a : α) : a ∈ (⊤ : Set α) := by -/
  /- trivial -/

/- @[simp] theorem not_mem_bot (a : α) : a ∉ (⊥ : Set α) := by -/
  /- simp -/

/- @[simp] theorem subset_top (s : Set α) : s ⊆ (⊤ : Set α) := by -/
  /- intro _ _ -/
  /- trivial -/

/- @[simp] theorem bot_subset (s : Set α) : (⊥ : Set α) ⊆ s := by -/
  /- intro _ h -/
  /- cases h -/

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

/- theorem le_top [LE α] [OrderTop α] (a : α) : a ≤ (⊤ : α) := -/
  /- OrderTop.le_top a -/

/- theorem bot_le [LE α] [OrderBot α] (a : α) : (⊥ : α) ≤ a := -/
  /- OrderBot.bot_le a -/

/- @[simp] theorem le_bottom_iff [LE α] [Std.IsPartialOrder α] [OrderBot α] (a : α) : -/
    /- a ≤ (⊥ : α) ↔ a = ⊥ := by -/
  /- constructor -/
  /- · intro h -/
    /- exact Std.IsPartialOrder.le_antisymm _ _ h (bot_le a) -/
  /- · intro h -/
    /- simp [h] -/

/- @[simp] theorem top_le_iff [LE α] [Std.IsPartialOrder α] [OrderTop α] (a : α) : -/
    /- (⊤ : α) ≤ a ↔ a = ⊤ := by -/
  /- constructor -/
  /- · intro h -/
    /- exact Std.IsPartialOrder.le_antisymm _ _ (le_top a) h -/
  /- · intro h -/
    /- simp [h] -/

/- instance [LE α] [Std.IsPreorder α] : Std.Refl (· ≤ · : α → α → Prop) where -/
  /- refl := Std.IsPreorder.le_refl -/

/- instance [LE α] [Std.IsPreorder α] : Trans (· ≤ · : α → α → Prop) (· ≤ ·) (· ≤ ·) where -/
  /- trans := by -/
    /- intro a b c hab hbc -/
    /- exact Std.IsPreorder.le_trans a b c hab hbc -/

/- instance [LE α] [Std.IsPartialOrder α] : Std.Antisymm (· ≤ · : α → α → Prop) where -/
  /- antisymm := fun _ _ hab hba => Std.IsPartialOrder.le_antisymm _ _ hab hba -/

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

/- namespace JoinSemilattice -/

/- instance [JoinSemilattice α] : Std.LawfulOrderSup α where -/
  /- max_le_iff a b c := by -/
    /- constructor -/
    /- · intro h -/
      /- exact ⟨ -/
        /- Std.IsPreorder.le_trans _ _ _ (le_join_left a b) h, -/
        /- Std.IsPreorder.le_trans _ _ _ (le_join_right a b) h -/
      /- ⟩ -/
    /- · intro h -/
      /- exact join_le a b c h.1 h.2 -/

/- instance [JoinSemilattice α] : Std.IdempotentOp (max : α → α → α) where -/
  /- idempotent a := by -/
    /- apply Std.IsPartialOrder.le_antisymm -/
    /- · exact join_le a a a (Std.IsPreorder.le_refl a) (Std.IsPreorder.le_refl a) -/
    /- · exact le_join_left a a -/

/- instance [JoinSemilattice α] : Std.Commutative (max : α → α → α) where -/
  /- comm a b := by -/
    /- apply Std.IsPartialOrder.le_antisymm -/
    /- · exact join_le a b (b ⊔ a) (le_join_right b a) (le_join_left b a) -/
    /- · exact join_le b a (a ⊔ b) (le_join_right a b) (le_join_left a b) -/

/- instance [JoinSemilattice α] : Std.Associative (max : α → α → α) where -/
  /- assoc a b c := by -/
    /- apply Std.IsPartialOrder.le_antisymm -/
    /- · apply join_le -/
      /- · exact join_le a b (a ⊔ (b ⊔ c)) -/
          /- (le_join_left a (b ⊔ c)) -/
          /- (Std.IsPreorder.le_trans _ _ _ (le_join_left b c) (le_join_right a (b ⊔ c))) -/
      /- · exact Std.IsPreorder.le_trans _ _ _ (le_join_right b c) (le_join_right a (b ⊔ c)) -/
    /- · apply join_le -/
      /- · exact Std.IsPreorder.le_trans _ _ _ (le_join_left a b) (le_join_left (a ⊔ b) c) -/
      /- · exact join_le b c ((a ⊔ b) ⊔ c) -/
          /- (Std.IsPreorder.le_trans _ _ _ (le_join_right a b) (le_join_left (a ⊔ b) c)) -/
          /- (le_join_right (a ⊔ b) c) -/

/- end JoinSemilattice -/

/- section JoinSemilattice -/

/- variable [JoinSemilattice α] [BoundedOrder α] -/

/- @[simp] theorem join_top (a : α) : a ⊔ (⊤ : α) = ⊤ := by -/
  /- apply Std.IsPartialOrder.le_antisymm -/
  /- · exact JoinSemilattice.join_le a (⊤ : α) (⊤ : α) (le_top a) (Std.IsPreorder.le_refl _) -/
  /- · exact JoinSemilattice.le_join_right a (⊤ : α) -/

/- @[simp] theorem top_join (a : α) : (⊤ : α) ⊔ a = ⊤ := by -/
  /- apply Std.IsPartialOrder.le_antisymm -/
  /- · exact JoinSemilattice.join_le (⊤ : α) a (⊤ : α) (Std.IsPreorder.le_refl _) (le_top a) -/
  /- · exact JoinSemilattice.le_join_left (⊤ : α) a -/

/- @[simp] theorem join_bot (a : α) : a ⊔ (⊥ : α) = a := by -/
  /- apply Std.IsPartialOrder.le_antisymm -/
  /- · exact JoinSemilattice.join_le a (⊥ : α) a (Std.IsPreorder.le_refl _) (bot_le a) -/
  /- · exact JoinSemilattice.le_join_left a (⊥ : α) -/

/- @[simp] theorem bot_join (a : α) : (⊥ : α) ⊔ a = a := by -/
  /- apply Std.IsPartialOrder.le_antisymm -/
  /- · exact JoinSemilattice.join_le (⊥ : α) a a (bot_le a) (Std.IsPreorder.le_refl _) -/
  /- · exact JoinSemilattice.le_join_right (⊥ : α) a -/

/- end JoinSemilattice -/

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

  /-- The top element denotes every concrete value. -/
  γ_top : γ (⊤ : AbstractValue) = (⊤ : Set ConcreteValue)

  /-- The bottom element denotes no concrete values. -/
  γ_bot : γ (⊥ : AbstractValue) = (⊥ : Set ConcreteValue)

  /--
  The order is monotone (it is sound).
  -/
  γ_monotone (a b : AbstractValue) : a ≤ b → γ a ⊆ γ b

/- namespace AbstractDomain -/

/- variable [AbstractDomain α β] {a b : α} -/

/- theorem γ_mono (h : a ≤ b) : -/
    /- AbstractDomain.γ (ConcreteValue := β) a ⊆ AbstractDomain.γ (ConcreteValue := β) b := -/
  /- AbstractDomain.γ_monotone a b h -/

/- @[simp] theorem γ_top_eq : AbstractDomain.γ (ConcreteValue := β) (⊤ : α) = (⊤ : Set β) := -/
  /- AbstractDomain.γ_top -/

/- @[simp] theorem γ_bot_eq : AbstractDomain.γ (ConcreteValue := β) (⊥ : α) = (⊥ : Set β) := -/
  /- AbstractDomain.γ_bot -/

/- theorem γ_le_top (a : α) : -/
    /- AbstractDomain.γ (ConcreteValue := β) a ⊆ AbstractDomain.γ (ConcreteValue := β) (⊤ : α) := -/
  /- γ_mono (le_top a) -/

/- theorem γ_bot_le (a : α) : -/
    /- AbstractDomain.γ (ConcreteValue := β) (⊥ : α) ⊆ AbstractDomain.γ (ConcreteValue := β) a := -/
  /- γ_mono (bot_le a) -/

/- theorem γ_join_left (a b : α) : -/
    /- AbstractDomain.γ (ConcreteValue := β) a ⊆ AbstractDomain.γ (ConcreteValue := β) (a ⊔ b) := -/
  /- γ_mono (JoinSemilattice.le_join_left a b) -/

/- theorem γ_join_right (a b : α) : -/
    /- AbstractDomain.γ (ConcreteValue := β) b ⊆ AbstractDomain.γ (ConcreteValue := β) (a ⊔ b) := -/
  /- γ_mono (JoinSemilattice.le_join_right a b) -/

/- @[simp] theorem mem_γ_top (x : β) : x ∈ AbstractDomain.γ (ConcreteValue := β) (⊤ : α) := by -/
  /- simpa using (Set.mem_top x : x ∈ (⊤ : Set β)) -/

/- @[simp] theorem not_mem_γ_bot (x : β) : x ∉ AbstractDomain.γ (ConcreteValue := β) (⊥ : α) := by -/
  /- simp [γ_bot_eq] -/

/- end AbstractDomain -/

end Veir
