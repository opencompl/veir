module

public import Veir.Data.LLVM.Int.Basic

public section

namespace Veir.Analysis.ConstProp

/-- The concrete domain is LLVM's integer value: a `BitVec n` value or `poison`. -/
abbrev Conc (n : Nat) := Veir.Data.LLVM.Int n

inductive Abs (n : Nat) where
  | top
  | bottom
  | poison
  | const : BitVec n → Abs n

def γ {n : Nat} : Abs n → Conc n → Prop
  | .top      => fun _ => True
  | .bottom   => fun _ => False
  | .poison   => fun c => c = .poison
  | .const c  => fun x => x = .val c

def Conc.toAbs {n : Nat} : Conc n → Abs n
  | .val c  => .const c
  | .poison => .poison

def Abs.join {n : Nat} : Abs n → Abs n → Abs n
  | .bottom,  y         => y
  | x,        .bottom   => x
  | .top,     _         => .top
  | _,        .top      => .top
  | .poison,  .poison   => .poison
  | .const c, .const d  => if c = d then .const c else .top
  | .poison,  .const _  => .top
  | .const _, .poison   => .top

def Abs.meet {n : Nat} : Abs n → Abs n → Abs n
  | .top,     y         => y
  | x,        .top      => x
  | .bottom,  _         => .bottom
  | _,        .bottom   => .bottom
  | .poison,  .poison   => .poison
  | .const c, .const d  => if c = d then .const c else .bottom
  | .poison,  .const _  => .bottom
  | .const _, .poison   => .bottom

def Abs.le {n : Nat} : Abs n → Abs n → Prop
  | .bottom,  _        => True
  | _,        .top     => True
  | .poison,  .poison  => True
  | .const c, .const d => c = d
  | _,        _        => False

/-! ### `join` is the least upper bound, `meet` is the greatest lower bound (w.r.t. `Abs.le`). -/

@[simp] theorem Abs.le_top {n : Nat} (a : Abs n) : Abs.le a .top := by
  cases a <;> trivial

theorem Abs.le_join_left {n : Nat} (a b : Abs n) : Abs.le a (a.join b) := by
  cases a <;> cases b <;> first
    | (simp [Abs.le, Abs.join]; done)
    | (rename_i c d; by_cases h : c = d <;> simp [h, Abs.le, Abs.join])

theorem Abs.le_join_right {n : Nat} (a b : Abs n) : Abs.le b (a.join b) := by
  cases a <;> cases b <;> first
    | (simp [Abs.le, Abs.join]; done)
    | (rename_i c d; by_cases h : c = d <;> simp [h, Abs.le, Abs.join])

/-- `join` is the *least* upper bound: any common upper bound dominates it. -/
theorem Abs.join_le {n : Nat} {a b c : Abs n}
    (ha : Abs.le a c) (hb : Abs.le b c) : Abs.le (a.join b) c := by
  cases a <;> cases b <;> cases c <;>
    simp only [Abs.join] <;> (try split) <;> simp_all [Abs.le]

theorem Abs.meet_le_left {n : Nat} (a b : Abs n) : Abs.le (a.meet b) a := by
  cases a <;> cases b <;> first
    | (simp [Abs.le, Abs.meet]; done)
    | (rename_i c d; by_cases h : c = d <;> simp [h, Abs.le, Abs.meet])

theorem Abs.meet_le_right {n : Nat} (a b : Abs n) : Abs.le (a.meet b) b := by
  cases a <;> cases b <;> first
    | (simp [Abs.le, Abs.meet]; done)
    | (rename_i c d; by_cases h : c = d <;> simp [h, Abs.le, Abs.meet])

/-- `meet` is the *greatest* lower bound: any common lower bound is dominated by it. -/
theorem Abs.le_meet {n : Nat} {a b c : Abs n}
    (ha : Abs.le c a) (hb : Abs.le c b) : Abs.le c (a.meet b) := by
  cases a <;> cases b <;> cases c <;> simp_all [Abs.le, Abs.meet]

/-- `Abs.le` is exactly concretization-inclusion: `γ` is monotone (soundness of the
    order) and reflects the order (completeness). -/
theorem Abs.le_iff_γ {n : Nat} (a b : Abs n) :
    Abs.le a b ↔ ∀ c, γ a c → γ b c := by
  cases a <;> cases b <;> simp [Abs.le, γ]
  · exact ⟨.val 0, by simp⟩             -- top ⊄ poison: a value isn't poison
  · exact ⟨.poison, by simp⟩            -- top ⊄ const _: poison isn't a value

/-! ### `Abs.le` is a partial order. -/

theorem Abs.le_refl {n : Nat} (a : Abs n) : Abs.le a a :=
  (Abs.le_iff_γ a a).2 (fun _ h => h)

theorem Abs.le_trans {n : Nat} {a b c : Abs n}
    (h1 : Abs.le a b) (h2 : Abs.le b c) : Abs.le a c := by
  rw [Abs.le_iff_γ] at h1 h2 ⊢
  exact fun x hx => h2 x (h1 x hx)

theorem Abs.le_antisymm {n : Nat} {a b : Abs n}
    (h1 : Abs.le a b) (h2 : Abs.le b a) : a = b := by
  cases a <;> cases b <;> simp_all [Abs.le]

/-! ### `γ` characterizations of `join` (over-approximate union) and `meet` (exact intersection). -/

/-- `join` over-approximates union: it covers everything either operand covers. -/
theorem γ_join {n : Nat} (a b : Abs n) (c : Conc n) :
    γ a c ∨ γ b c → γ (a.join b) c := by
  rintro (h | h)
  · exact (Abs.le_iff_γ a (a.join b)).1 (Abs.le_join_left a b) c h
  · exact (Abs.le_iff_γ b (a.join b)).1 (Abs.le_join_right a b) c h

/-- `meet` is *exact* intersection: it covers precisely what both operands cover. -/
theorem γ_meet {n : Nat} (a b : Abs n) (c : Conc n) :
    γ (a.meet b) c ↔ γ a c ∧ γ b c := by
  constructor
  · intro h
    exact ⟨(Abs.le_iff_γ _ _).1 (Abs.meet_le_left a b) c h,
           (Abs.le_iff_γ _ _).1 (Abs.meet_le_right a b) c h⟩
  · rintro ⟨h1, h2⟩
    cases a <;> cases b <;> simp_all [γ, Abs.meet]

/-! ### Lifting binary bitvector operations to transfer functions. -/

/-- Concrete semantics of a binary op, with `poison` propagating through it. -/
def Conc.lift {n : Nat} (f : BitVec n → BitVec n → BitVec n) : Conc n → Conc n → Conc n
  | .val x, .val y => .val (f x y)
  | _,      _      => .poison

/-- Lift a binary bitvector op to an abstract transfer function. `bottom` is
    absorbing (an unreachable operand makes the result unreachable), `poison`
    propagates, two known constants give a known constant, and anything else
    falls back to `top`. -/
def Abs.lift {n : Nat} (f : BitVec n → BitVec n → BitVec n) : Abs n → Abs n → Abs n
  | .bottom,  _        => .bottom
  | _,        .bottom  => .bottom
  | .poison,  _        => .poison
  | _,        .poison  => .poison
  | .const c, .const d => .const (f c d)
  | _,        _        => .top

/-- Soundness, proved once for *every* `f`: the abstract lift over-approximates the
    concrete semantics. Each concrete operator inherits this for free. -/
theorem Abs.lift_sound {n : Nat} (f : BitVec n → BitVec n → BitVec n)
    {a b : Abs n} {x y : Conc n} (hx : γ a x) (hy : γ b y) :
    γ (Abs.lift f a b) (Conc.lift f x y) := by
  cases a <;> cases b <;> cases x <;> cases y <;>
    simp_all [γ, Abs.lift, Conc.lift]

/-- Subtraction transfer function. -/
def Abs.sub {n : Nat} : Abs n → Abs n → Abs n := Abs.lift (· - ·)

/-- Bitwise-xor transfer function. -/
def Abs.xor {n : Nat} : Abs n → Abs n → Abs n := Abs.lift (· ^^^ ·)

theorem Abs.sub_sound {n : Nat} {a b : Abs n} {x y : Conc n}
    (hx : γ a x) (hy : γ b y) : γ (Abs.sub a b) (Conc.lift (· - ·) x y) :=
  Abs.lift_sound _ hx hy

theorem Abs.xor_sound {n : Nat} {a b : Abs n} {x y : Conc n}
    (hx : γ a x) (hy : γ b y) : γ (Abs.xor a b) (Conc.lift (· ^^^ ·) x y) :=
  Abs.lift_sound _ hx hy

/-! ### Precision: the lift returns the *best* (least) sound abstract result.

These reverse lemmas read concrete coverage facts back as order bounds: if `r`
covers a given concrete value, then `r` is at least the most precise abstraction
of that value. -/

theorem Abs.poison_le_of_γ {n : Nat} {r : Abs n}
    (h : γ r .poison) : Abs.le Abs.poison r := by
  cases r <;> simp_all [γ, Abs.le]

theorem Abs.const_le_of_γ {n : Nat} {r : Abs n} {k : BitVec n}
    (h : γ r (.val k)) : Abs.le (Abs.const k) r := by
  cases r <;> simp_all [γ, Abs.le]

theorem Abs.top_le_of_γ {n : Nat} {r : Abs n} {w : BitVec n}
    (h1 : γ r .poison) (h2 : γ r (.val w)) : Abs.le Abs.top r := by
  cases r <;> simp_all [γ, Abs.le]

/-- Precision / optimality: any sound over-approximation `r` of the image is at
    least `Abs.lift f a b`. Hence the lift is the least sound result — the best
    answer expressible in this domain. -/
theorem Abs.lift_best {n : Nat} (f : BitVec n → BitVec n → BitVec n) (a b r : Abs n)
    (hr : ∀ x y, γ a x → γ b y → γ r (Conc.lift f x y)) :
    Abs.le (Abs.lift f a b) r := by
  cases a <;> cases b <;> simp only [Abs.lift] <;> try trivial
  case top.poison    => exact Abs.poison_le_of_γ (hr .poison .poison True.intro rfl)
  case poison.top    => exact Abs.poison_le_of_γ (hr .poison .poison rfl True.intro)
  case poison.poison => exact Abs.poison_le_of_γ (hr .poison .poison rfl rfl)
  case poison.const d => exact Abs.poison_le_of_γ (hr .poison (.val d) rfl rfl)
  case const.poison c => exact Abs.poison_le_of_γ (hr (.val c) .poison rfl rfl)
  case const.const c d => exact Abs.const_le_of_γ (hr (.val c) (.val d) rfl rfl)
  case top.top =>
    exact Abs.top_le_of_γ (hr .poison .poison True.intro True.intro)
                          (hr (.val 0) (.val 0) True.intro True.intro)
  case top.const d =>
    exact Abs.top_le_of_γ (hr .poison (.val d) True.intro rfl)
                          (hr (.val 0) (.val d) True.intro rfl)
  case const.top c =>
    exact Abs.top_le_of_γ (hr (.val c) .poison rfl True.intro)
                          (hr (.val c) (.val 0) rfl True.intro)

end Veir.Analysis.ConstProp

end
