module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Analysis.DataFlow.Domains.AbstractDomain

public section

namespace Veir

/-!
# Constant domain

Instantiation of `AbstractDomain` with a constant propagation lattice whose
elements are `bottom`, a constant, or `top`.
-/

/-- Concrete integer values tracked by the constant domain. -/
structure ConcreteConstant where
  bitwidth : Nat
  value : Data.LLVM.Int bitwidth
deriving BEq, DecidableEq

/-- Abstract values used by sparse constant propagation. -/
inductive AbstractConstant where
  | top
  | bottom
  | constant (value : ConcreteConstant)
deriving BEq, DecidableEq, TypeName

namespace AbstractConstant

/-- Defines the ordering of abstract values in the constant domain. -/
def le (x y : AbstractConstant) : Prop :=
  match x, y with
  | .bottom, _ => True
  | _, .top => True
  | .constant c, .constant d => c = d
  | _, _ => False

instance : LE AbstractConstant where
  le := le

@[simp] theorem le_def (a b : AbstractConstant) : (a ≤ b) ↔ le a b := Iff.rfl

theorem le_top (a : AbstractConstant) : a ≤ .top := by
  cases a <;> trivial

theorem bot_le (a : AbstractConstant) : .bottom ≤ a := by
  cases a <;> trivial

instance : BoundedOrder AbstractConstant where
  top := .top
  bot := .bottom
  le_top := le_top
  bot_le := bot_le

@[expose] def γ (absVal : AbstractConstant) : Set ConcreteConstant :=
  match absVal with
  | .top => fun _ => True
  | .bottom => fun _ => False
  | .constant a => fun concVal => concVal = a

def join (lhs rhs : AbstractConstant) : AbstractConstant :=
  match lhs, rhs with
  | .bottom, y => y
  | x, .bottom => x
  | .top, _ => ⊤
  | _, .top => ⊤
  | .constant c, .constant d => if c = d then .constant c else ⊤

instance : Join AbstractConstant where
  join := join

theorem γ_monotone (a b : AbstractConstant) : a ≤ b → γ a ⊆ γ b := by
  intro hab x hx
  cases a <;> cases b <;> simp [γ, le] at hab hx ⊢
  all_goals first | trivial | exact hx.trans hab

theorem le_refl (a : AbstractConstant) : a ≤ a := by
  cases a <;> simp [le]

theorem le_trans (a b c : AbstractConstant) : a ≤ b → b ≤ c → a ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all [le]

theorem le_antisymm (a b : AbstractConstant) : a ≤ b → b ≤ a → a = b := by
  cases a <;> cases b <;> simp_all [le]

theorem le_join_left (a b : AbstractConstant) : a ≤ a ⊔ b := by
  cases a <;> cases b <;> try simp [le, join]
  case constant.constant c d =>
    by_cases h : c = d <;> simp [h]

theorem le_join_right (a b : AbstractConstant) : b ≤ a ⊔ b := by
  cases a <;> cases b <;> try simp [le, join]
  case constant.constant c d =>
    by_cases h : c = d <;> simp [h]

theorem join_le (a b c : AbstractConstant) : a ≤ c → b ≤ c → a ⊔ b ≤ c := by
  intros
  cases a <;> cases b <;> cases c <;>
    simp [join] <;> (try split) <;> simp_all [le]

instance : JoinSemilattice AbstractConstant where
  le := le
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  join := join
  le_join_left := le_join_left
  le_join_right := le_join_right
  join_le := join_le

instance : AbstractDomain AbstractConstant ConcreteConstant where
  toJoinSemilattice := inferInstance
  toBoundedOrder := inferInstance
  γ := γ
  γ_top := rfl
  γ_bot := rfl
  γ_monotone := γ_monotone

end AbstractConstant

end Veir
