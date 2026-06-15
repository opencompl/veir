module

public import Veir.Analysis.DataFlow.Domains.AbstractDomain

public section

namespace Veir

/-!
# Liveness domain

Instantiation of `AbstractDomain` with a two point lattice used by dead code analysis.
`dead` denotes an unreachable program point or edge, while `live` denotes a reachable one.
-/

/-- Abstract values used to track executability. -/
inductive Liveness where
  | dead
  | live
deriving BEq, DecidableEq, TypeName

namespace Liveness

/-- Defines the ordering of abstract values in the liveness domain. -/
def le (x y : Liveness) : Prop :=
  match x, y with
  | .dead, _ => True
  | .live, .live => True
  | .live, .dead => False

instance : LE Liveness where
  le := le

theorem le_def (a b : Liveness) : (a ≤ b) ↔ le a b := Iff.rfl

@[simp, grind .]
theorem le_top (a : Liveness) : a ≤ .live := by
  cases a <;> trivial

@[simp, grind .]
theorem bot_le (a : Liveness) : .dead ≤ a := by
  cases a <;> trivial

instance : BoundedOrder Liveness where
  top := .live
  bot := .dead
  le_top := le_top
  bot_le := bot_le

@[expose] def γ (absVal : Liveness) : Set Unit :=
  match absVal with
  | .dead => fun _ => False
  | .live => fun _ => True

def join (lhs rhs : Liveness) : Liveness :=
  match lhs, rhs with
  | .live, _ => .live
  | _, .live => .live
  | .dead, .dead => .dead

instance : Join Liveness where
  join := join

theorem γ_monotone (a b : Liveness) : a ≤ b → γ a ⊆ γ b := by
  intro hab x hx
  cases a <;> cases b <;> simp [γ, le_def, le] at hab hx ⊢
  case dead.dead => cases hx
  case dead.live => cases hx
  case live.live => exact hx

@[simp, grind .]
theorem le_refl (a : Liveness) : a ≤ a := by
  cases a <;> simp

@[grind →]
theorem le_trans (a b c : Liveness) : a ≤ b → b ≤ c → a ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all

@[grind →]
theorem le_antisymm (a b : Liveness) : a ≤ b → b ≤ a → a = b := by
  cases a <;> cases b <;> simp_all [le_def, le]

@[simp, grind .]
theorem le_join_left (a b : Liveness) : a ≤ a ⊔ b := by
  cases a <;> cases b <;> simp [join]

@[simp, grind .]
theorem le_join_right (a b : Liveness) : b ≤ a ⊔ b := by
  cases a <;> cases b <;> simp [join]

theorem join_le (a b c : Liveness) : a ≤ c → b ≤ c → a ⊔ b ≤ c := by
  intros
  cases a <;> cases b <;> cases c <;> simp_all [join]

instance : JoinSemilattice Liveness where
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  join := join
  le_join_left := le_join_left
  le_join_right := le_join_right
  join_le := join_le

instance : AbstractDomain Liveness Unit where
  toJoinSemilattice := inferInstance
  toBoundedOrder := inferInstance
  γ := γ
  γ_top := rfl
  γ_bot := rfl
  γ_monotone := γ_monotone

end Liveness

end Veir
