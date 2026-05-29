module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Analysis.DataFlow.Domains.AbstractDomain

public section

namespace Veir

/-- A known non-poison integer constant. -/
structure KnownConstant where
  bitwidth : Nat
  value : BitVec bitwidth
deriving BEq, DecidableEq

/-- Concrete integer values tracked by the constant domain. -/
structure ConcreteConstant where
  bitwidth : Nat
  value : Data.LLVM.Int bitwidth
deriving BEq, DecidableEq

/-- Abstract values used by sparse constant propagation. -/
inductive AbstractConstant where
  | top
  | bottom
  | poison
  | constant (value : KnownConstant)
deriving BEq, DecidableEq, TypeName

namespace AbstractConstant

def γ (absVal : AbstractConstant) : ConcreteConstant → Prop :=
  match absVal with
  | .top => fun _ => True
  | .bottom => fun _ => False
  | .poison => fun
      | ⟨_, .poison⟩ => True
      | _ => False
  | .constant a => fun concVal => concVal = ⟨a.bitwidth, .val a.value⟩

def join (lhs rhs : AbstractConstant) : AbstractConstant :=
  match lhs, rhs with
  | .bottom, y => y
  | x, .bottom => x
  | .top, _ => .top
  | _, .top => .top
  | .poison, .poison => .poison
  | .constant c, .constant d => if c = d then .constant c else .top
  | .poison, .constant _ => .top
  | .constant _, .poison => .top

def meet (lhs rhs : AbstractConstant) : AbstractConstant :=
  match lhs, rhs with
  | .top, y => y
  | x, .top => x
  | .bottom, _ => .bottom
  | _, .bottom => .bottom
  | .poison, .poison => .poison
  | .constant c, .constant d => if c = d then .constant d else .bottom
  | .poison, .constant _ => .bottom
  | .constant _, .poison => .bottom

/-- Defines the ordering of abstract values in the constant domain. -/
def le (x y : AbstractConstant) : Prop :=
  match x, y with
  | .bottom, _ => True
  | _, .top => True
  | .poison, .poison => True
  | .constant c, .constant d => c = d
  | _, _ => False

instance : LE AbstractConstant where
  le := le

/-- Alias for the top element: value is unknown or conflicting. -/
def unknown : AbstractConstant := .top

/-- Alias for the bottom element: no information has been learned yet. -/
def uninitialized : AbstractConstant := .bottom

/-- Build a constant lattice element from an integer at the given bitwidth. -/
def ofInt (bitwidth : Nat) (value : Int) : AbstractConstant :=
  .constant { bitwidth := bitwidth, value := BitVec.ofInt bitwidth value }

theorem le_iff_γ (a b : AbstractConstant) :
    a ≤ b ↔ ∀ c, γ a c → γ b c := by sorry

theorem le_refl (a : AbstractConstant) : a ≤ a :=
  (le_iff_γ a a).2 (fun _ h => h)

theorem le_trans (a b c : AbstractConstant) : a ≤ b → b ≤ c → a ≤ c := by
  intro h1 h2
  rw [le_iff_γ] at h1 h2 ⊢
  exact fun x hx => h2 x (h1 x hx)

theorem le_antisymm (a b : AbstractConstant) : a ≤ b → b ≤ a → a = b := by
  intro h1 h2
  change AbstractConstant.le a b at h1
  change AbstractConstant.le b a at h2
  cases a <;> cases b <;> simp_all [AbstractConstant.le]

theorem le_top (a : AbstractConstant) : a ≤ .top := by
  show AbstractConstant.le a .top
  cases a <;> trivial

theorem bottom_le (a : AbstractConstant) : .bottom ≤ a := by
  show AbstractConstant.le .bottom a
  cases a <;> trivial

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

@[reducible] def ConstantDomain : AbstractDomain AbstractConstant ConcreteConstant where
  le := le
  γ := γ
  le_iff_γ := le_iff_γ
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  join := .join
  le_join_left := le_join_left
  le_join_right := le_join_right
  join_le := join_le

instance : AbstractDomain AbstractConstant ConcreteConstant := ConstantDomain

end AbstractConstant

end Veir
