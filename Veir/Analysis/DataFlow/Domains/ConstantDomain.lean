module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Analysis.DataFlow.Domains.AbstractDomain

public section

namespace Veir

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

theorem le_top (a : AbstractConstant) : AbstractConstant.le a .top := by
  cases a <;> trivial

theorem bot_le (a : AbstractConstant) : AbstractConstant.le .bottom a := by
  cases a <;> trivial

instance : BoundedOrder AbstractConstant where
  top := .top
  bot := .bottom
  le_top := le_top
  bot_le := bot_le

def γ (absVal : AbstractConstant) : Set ConcreteConstant :=
  match absVal with
  | .top => fun _ => True
  | .bottom => fun _ => False
  | .constant a => fun concVal => concVal = a

def join (lhs rhs : AbstractConstant) : AbstractConstant :=
  match lhs, rhs with
  | .bottom, y => y
  | x, .bottom => x
  | .top, _ => .top
  | _, .top => .top
  | .constant c, .constant d => if c = d then .constant c else .top

def meet (lhs rhs : AbstractConstant) : AbstractConstant :=
  match lhs, rhs with
  | .top, y => y
  | x, .top => x
  | .bottom, _ => .bottom
  | _, .bottom => .bottom
  | .constant c, .constant d => if c = d then .constant d else .bottom

/-- Build a constant lattice element from an integer at the given bitwidth. -/
/- def ofInt (bitwidth : Nat) (value : Int) : AbstractConstant := -/
  /- .constant { bitwidth := bitwidth, value := BitVec.ofInt bitwidth value } -/

theorem le_iff_γ (a b : AbstractConstant) :
    a ≤ b ↔ γ a ⊆ γ b := by
  change AbstractConstant.le a b ↔ γ a ⊆ γ b
  cases a <;> cases b
  case top.top =>
    constructor
    · intro _
      exact fun {_} h => h
    · intro _
      trivial
  case top.bottom =>
    constructor
    · intro h
      cases h
    · intro h
      have hFalse := h (a := .mk 0 (.poison : Data.LLVM.Int 0)) trivial
      exact False.elim hFalse
  case top.constant value =>
    rcases value with ⟨w, v⟩
    constructor
    · intro h
      cases h
    · intro h
      have hEq := h (a := .mk (w + 1) (.poison : Data.LLVM.Int (w + 1))) trivial
      cases hEq
  case bottom.top =>
    constructor
    · intro _
      exact fun {_} h => False.elim h
    · intro _
      trivial
  case bottom.bottom =>
    constructor
    · intro _
      exact fun {_} h => False.elim h
    · intro _
      trivial
  case bottom.constant value =>
    constructor
    · intro _
      exact fun {_} h => False.elim h
    · intro _
      trivial
  case constant.top value =>
    constructor
    · intro _
      exact fun {_} _ => trivial
    · intro _
      trivial
  case constant.bottom value =>
    constructor
    · intro h
      cases h
    · intro h
      have hFalse := h (a := value) rfl
      exact False.elim hFalse
  case constant.constant c d =>
    constructor
    · intro h
      intro a ha
      change a = c at ha
      exact ha.trans h
    · intro h
      exact h (a := c) rfl

theorem γ_monotone (a b : AbstractConstant) : a ≤ b → γ a ⊆ γ b :=
  (le_iff_γ a b).1

theorem le_refl (a : AbstractConstant) : a ≤ a :=
  (le_iff_γ a a).2 (by
    show γ a ⊆ γ a
    exact fun {_} h => h)

theorem le_trans (a b c : AbstractConstant) : a ≤ b → b ≤ c → a ≤ c := by
  intro h1 h2
  rw [le_iff_γ] at h1 h2 ⊢
  show γ a ⊆ γ c
  exact fun {_} hx => h2 (h1 hx)

theorem le_antisymm (a b : AbstractConstant) : a ≤ b → b ≤ a → a = b := by
  intro h1 h2
  change AbstractConstant.le a b at h1
  change AbstractConstant.le b a at h2
  cases a <;> cases b <;> simp_all [AbstractConstant.le]

theorem le_join_left (a b : AbstractConstant) : a ≤ join a b := by
  show AbstractConstant.le a (join a b)
  cases a <;> cases b <;> try simp [AbstractConstant.le, join]
  case constant.constant c d =>
    by_cases h : c = d <;> simp [h]

theorem le_join_right (a b : AbstractConstant) : b ≤ join a b := by
  show AbstractConstant.le b (join a b)
  cases a <;> cases b <;> try simp [AbstractConstant.le, join]
  case constant.constant c d =>
    by_cases h : c = d <;> simp [h]

theorem join_le (a b c : AbstractConstant) : a ≤ c → b ≤ c → join a b ≤ c := by
  intro ha hb
  change AbstractConstant.le a c at ha
  change AbstractConstant.le b c at hb
  show AbstractConstant.le (join a b) c
  cases a <;> cases b <;> cases c <;>
    simp only [join] <;> (try split) <;> simp_all [AbstractConstant.le]

theorem meet_le_left (a b : AbstractConstant) : meet a b ≤ a := by
  show AbstractConstant.le (meet a b) a
  cases a <;> cases b <;> try simp [AbstractConstant.le, meet]
  case constant.constant c d =>
    by_cases h : c = d <;> simp [h]

theorem meet_le_right (a b : AbstractConstant) : meet a b ≤ b := by
  show AbstractConstant.le (meet a b) b
  cases a <;> cases b <;> try simp [AbstractConstant.le, meet]
  case constant.constant c d =>
    by_cases h : c = d <;> simp [h]

theorem le_meet (a b c : AbstractConstant) : a ≤ b → a ≤ c → a ≤ meet b c := by
  intro hab hac
  change AbstractConstant.le a b at hab
  change AbstractConstant.le a c at hac
  show AbstractConstant.le a (meet b c)
  cases a <;> cases b <;> cases c <;> simp_all [AbstractConstant.le, meet]

instance : AbstractDomain AbstractConstant ConcreteConstant where
  le := le
  top := .top
  bot := .bottom
  γ := γ
  γ_monotone := γ_monotone
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  le_top := le_top
  bot_le := bot_le
  join := .join
  le_join_left := le_join_left
  le_join_right := le_join_right
  join_le := join_le

end AbstractConstant

end Veir
