module

public import Veir.Analysis.DataFlow.Domains.AbstractDomain

public section

namespace Veir

/-!
# Integer range domain

An abstract domain of closed integer intervals. The order is interval containment:
smaller intervals contain more precise information.
-/

/-- A nonempty closed integer interval. -/
structure IntegerRange where
  lower : Int
  upper : Int
  lower_le_upper : lower ≤ upper
deriving BEq, DecidableEq, Repr

/-- Abstract integer values: uninitialized, unbounded, or a closed interval. -/
inductive IntegerRangeLattice where
  | bottom
  | top
  | interval (range : IntegerRange)
deriving BEq, DecidableEq, Repr

namespace IntegerRangeLattice

/-- Defines the precision ordering of abstract integer ranges. -/
def le : IntegerRangeLattice → IntegerRangeLattice → Prop
  | .bottom, _ => True
  | _, .top => True
  | .interval lhs, .interval rhs => rhs.lower ≤ lhs.lower ∧ lhs.upper ≤ rhs.upper
  | _, _ => False

instance : LE IntegerRangeLattice where
  le := le

theorem le_def (a b : IntegerRangeLattice) : (a ≤ b) ↔ le a b := Iff.rfl

@[simp, grind .]
theorem le_top (a : IntegerRangeLattice) : a ≤ .top := by
  cases a <;> trivial

@[simp, grind .]
theorem bot_le (a : IntegerRangeLattice) : .bottom ≤ a := by
  cases a <;> trivial

instance : BoundedOrder IntegerRangeLattice where
  top := .top
  bot := .bottom
  le_top := le_top
  bot_le := bot_le

/-- The set of concrete integers denoted by an abstract range. -/
@[expose] def γ : IntegerRangeLattice → Set Int
  | .bottom => fun _ => False
  | .top => fun _ => True
  | .interval range => fun value => range.lower ≤ value ∧ value ≤ range.upper

@[simp] theorem mem_γ_bottom (value : Int) : value ∈ γ .bottom ↔ False := Iff.rfl

@[simp] theorem mem_γ_top (value : Int) : value ∈ γ .top ↔ True := Iff.rfl

@[simp] theorem mem_γ_interval (value : Int) (range : IntegerRange) :
    value ∈ γ (.interval range) ↔ range.lower ≤ value ∧ value ≤ range.upper := Iff.rfl

/-- Construct the exact range of a known integer. -/
def singleton (value : Int) : IntegerRangeLattice :=
  .interval { lower := value, upper := value, lower_le_upper := by omega }

/-- The least interval containing both abstract ranges. -/
def join : IntegerRangeLattice → IntegerRangeLattice → IntegerRangeLattice
  | .bottom, rhs => rhs
  | lhs, .bottom => lhs
  | .top, _ => .top
  | _, .top => .top
  | .interval lhs, .interval rhs =>
      .interval
        { lower := min lhs.lower rhs.lower
          upper := max lhs.upper rhs.upper
          lower_le_upper := by
            have hl := lhs.lower_le_upper
            have hr := rhs.lower_le_upper
            omega }

instance : Join IntegerRangeLattice where
  join := join

/-- The intersection of two abstract ranges. -/
def meet : IntegerRangeLattice → IntegerRangeLattice → IntegerRangeLattice
  | .bottom, _ => .bottom
  | _, .bottom => .bottom
  | .top, rhs => rhs
  | lhs, .top => lhs
  | .interval lhs, .interval rhs =>
      let lower := max lhs.lower rhs.lower
      let upper := min lhs.upper rhs.upper
      if h : lower ≤ upper then
        .interval { lower, upper, lower_le_upper := h }
      else
        .bottom

/-- Add two abstract integer ranges. -/
def add (lhs rhs : IntegerRangeLattice) : IntegerRangeLattice :=
  match lhs, rhs with
  | .bottom, _ | _, .bottom => .bottom
  | .top, _ | _, .top => .top
  | .interval lhs, .interval rhs =>
      .interval
        { lower := lhs.lower + rhs.lower
          upper := lhs.upper + rhs.upper
          lower_le_upper := by
            have hl := lhs.lower_le_upper
            have hr := rhs.lower_le_upper
            omega }

/-- Subtract two abstract integer ranges. -/
def sub (lhs rhs : IntegerRangeLattice) : IntegerRangeLattice :=
  match lhs, rhs with
  | .bottom, _ | _, .bottom => .bottom
  | .top, _ | _, .top => .top
  | .interval lhs, .interval rhs =>
      .interval
        { lower := lhs.lower - rhs.upper
          upper := lhs.upper - rhs.lower
          lower_le_upper := by
            have hl := lhs.lower_le_upper
            have hr := rhs.lower_le_upper
            omega }

/-- Multiply two abstract integer ranges. -/
def mul (lhs rhs : IntegerRangeLattice) : IntegerRangeLattice :=
  match lhs, rhs with
  | .bottom, _ | _, .bottom => .bottom
  | .top, _ | _, .top => .top
  | .interval lhs, .interval rhs =>
      let candidates := #[
        lhs.lower * rhs.lower,
        lhs.lower * rhs.upper,
        lhs.upper * rhs.lower,
        lhs.upper * rhs.upper]
      let lower := candidates.foldl min candidates[0]!
      let upper := candidates.foldl max candidates[0]!
      if h : lower ≤ upper then
        .interval { lower, upper, lower_le_upper := h }
      else
        .bottom

theorem γ_monotone (a b : IntegerRangeLattice) : a ≤ b → γ a ⊆ γ b := by
  intro hab value hvalue
  cases a <;> cases b <;>
    simp only [mem_γ_bottom, mem_γ_top, mem_γ_interval] at hvalue ⊢ <;>
    simp [le_def, le] at hab <;> omega

@[simp, grind .]
theorem le_refl (a : IntegerRangeLattice) : a ≤ a := by
  cases a <;> simp [le_def, le]

@[grind →]
theorem le_trans (a b c : IntegerRangeLattice) : a ≤ b → b ≤ c → a ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all [le_def, le]
  omega

@[grind →]
theorem le_antisymm (a b : IntegerRangeLattice) : a ≤ b → b ≤ a → a = b := by
  cases a <;> cases b <;> simp_all [le_def, le]
  next lhs rhs =>
    congr
    cases lhs
    cases rhs
    simp_all
    omega

@[simp, grind .]
theorem le_join_left (a b : IntegerRangeLattice) : a ≤ a ⊔ b := by
  cases a <;> cases b <;> simp [join, le_def, le] <;> omega

@[simp, grind .]
theorem le_join_right (a b : IntegerRangeLattice) : b ≤ a ⊔ b := by
  cases a <;> cases b <;> simp [join, le_def, le] <;> omega

theorem join_le (a b c : IntegerRangeLattice) : a ≤ c → b ≤ c → a ⊔ b ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all [join, le_def, le]
  omega

instance : JoinSemilattice IntegerRangeLattice where
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  join := join
  le_join_left := le_join_left
  le_join_right := le_join_right
  join_le := join_le

instance : AbstractDomain IntegerRangeLattice Int where
  toJoinSemilattice := inferInstance
  toBoundedOrder := inferInstance
  γ := γ
  γ_top := rfl
  γ_bot := rfl
  γ_monotone := γ_monotone

end IntegerRangeLattice

end Veir
