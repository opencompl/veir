module

public import Veir.IR.Basic
import all Init.Internal.Order.Basic

public section

namespace Veir

/--
  The interpreter monad. An interpretation step has four outcomes. UB is a property
  of the execution, not of any value, so it lives here rather than inside
  `RuntimeValue` or `LLVM.Int`.
-/
inductive Interp (α : Type) where
  /-- Interpreter could not proceed (malformed IR, unsupported op) at `op`, if known. -/
  | fail (op : Option OperationPtr)
  /-- Execution triggered undefined behaviour at `op`, if known. -/
  | ub (op : Option OperationPtr)
  /-- Execution never terminates. -/
  | spin
  /-- Successful execution producing `a`. -/
  | ok (a : α)
deriving Inhabited

@[expose]
def Interp.map {α β : Type} (f : α → β) : Interp α → Interp β
  | .fail op => .fail op
  | .ub op => .ub op
  | .spin => .spin
  | .ok a => .ok (f a)

@[simp, grind =] theorem Interp.map_fail : Interp.map f (.fail op) = .fail op := rfl
@[simp, grind =] theorem Interp.map_ub : Interp.map f (.ub op) = .ub op := rfl
@[simp, grind =] theorem Interp.map_spin {f : α → β} : Interp.map f .spin = .spin := rfl
@[simp, grind =] theorem Interp.map_ok : Interp.map f (.ok a) = .ok (f a) := rfl

instance : Monad Interp where
  pure x := .ok x
  bind x f := match x with
    | .fail op => .fail op
    | .ub op => .ub op
    | .spin => .spin
    | .ok a => f a
  map := Interp.map

instance : MonadLift Option Interp where
  monadLift
    | none => .fail none
    | some v => .ok v

/-!
  The interpreter of a control-flow graph is a `partial_fixpoint`, and a run
  that never terminates takes the least element of the order below. That
  element is `spin`, which only a run that never terminates refines. It is
  neither `ub`, which would permit the target of a refinement to do anything,
  nor `fail`, which says the interpreter met something it cannot handle.
  Without these instances the least element would be an arbitrary value picked
  by choice, about which nothing can be proven.
-/

instance : Lean.Order.PartialOrder (Interp α) :=
  inferInstanceAs (Lean.Order.PartialOrder (Lean.Order.FlatOrder (.spin : Interp α)))

instance : Lean.Order.CCPO (Interp α) :=
  inferInstanceAs (Lean.Order.CCPO (Lean.Order.FlatOrder (.spin : Interp α)))

/-- `spin` is below every outcome, and the other outcomes are only below themselves. -/
theorem Interp.rel_iff {x y : Interp α} :
    Lean.Order.PartialOrder.rel x y ↔ x = .spin ∨ x = y := by
  constructor
  · intro h
    cases h
    · exact .inl rfl
    · exact .inr rfl
  · rintro (rfl | rfl)
    · exact Lean.Order.FlatOrder.rel.bot
    · exact Lean.Order.FlatOrder.rel.refl

/--
  A predicate that holds of `spin` is admissible, because `spin` is the least
  element. This is what lets a `partial_fixpoint` induction discharge the
  case of a run that never terminates.
-/
theorem Interp.admissible_of_spin {α : Type} (P : Interp α → Prop) (hspin : P .spin) :
    Lean.Order.admissible P := by
  intro c hchain h
  by_cases hex : ∃ x, c x ∧ x ≠ .spin
  · obtain ⟨x, hcx, hne⟩ := hex
    rcases Interp.rel_iff.mp (Lean.Order.le_csup hchain hcx) with rfl | rfl
    · exact absurd rfl hne
    · exact h _ hcx
  · have hbelow : Lean.Order.PartialOrder.rel (Lean.Order.CCPO.csup hchain) (.spin : Interp α) := by
      apply Lean.Order.csup_le hchain
      intro y hy
      have : y = .spin := Classical.byContradiction fun hne => hex ⟨y, hy, hne⟩
      exact this ▸ Lean.Order.PartialOrder.rel_refl
    rcases Interp.rel_iff.mp hbelow with heq | heq <;> exact heq ▸ hspin

@[simp, grind =] theorem Interp.pure_eq (a : α) : (pure a : Interp α) = .ok a := rfl
@[simp, grind =] theorem Interp.bind_ok (a : α) (f : α → Interp β) :
    (Interp.ok a >>= f) = f a := rfl
@[simp, grind =] theorem Interp.bind_ub (f : α → Interp β) :
    ((.ub op : Interp α) >>= f) = .ub op := rfl
@[simp, grind =] theorem Interp.bind_spin (f : α → Interp β) :
    ((.spin : Interp α) >>= f) = .spin := rfl
@[simp, grind =] theorem Interp.bind_fail (f : α → Interp β) :
    ((.fail op : Interp α) >>= f) = .fail op := rfl
@[grind =] theorem Interp.bind_def {α β : Type} (x : Interp α) (f : α → Interp β) :
    (x >>= f) = match x with
      | .fail op => .fail op
      | .ub op => .ub op
      | .spin => .spin
      | .ok a => f a := rfl
@[simp, grind =] theorem Interp.liftOption_none : ((none : Option α) : Interp α) = .fail none := rfl
@[simp, grind =] theorem Interp.liftOption_some (a : α) : ((some a : Option α) : Interp α) = .ok a := rfl

instance : LawfulMonad Interp :=
  LawfulMonad.mk' Interp
    (id_map := fun x => by cases x <;> rfl)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun x _ _ => by cases x <;> rfl)

theorem Interp.bind_eq_bind_iff {α β : Type} {x : Interp α} {f g : α → Interp β} :
    (x >>= f) = (x >>= g) ↔ ∀ a, x = .ok a → f a = g a := by
  cases x <;> simp [Interp.bind_def]

/-- Binding is monotone, so a `partial_fixpoint` may recurse under `do` notation. -/
instance : Lean.Order.MonoBind Interp where
  bind_mono_left h := by
    rcases Interp.rel_iff.mp h with rfl | rfl
    · exact Interp.rel_iff.mpr (.inl rfl)
    · exact Lean.Order.PartialOrder.rel_refl
  bind_mono_right {α β a f₁ f₂} h := by
    cases a
    case ok a => exact h a
    all_goals exact Lean.Order.PartialOrder.rel_refl

/-- Whether the interpretation failed, at any operation. -/
@[expose, simp, grind]
def Interp.isFail : Interp α → Bool
  | .fail _ => true
  | _ => false

/-- Whether the interpretation triggered UB, at any operation. -/
@[expose, simp, grind]
def Interp.isUB : Interp α → Bool
  | .ub _ => true
  | _ => false

/--
  If reporting any failure or UB, blame `op` for it. `spin` is returned
  unchanged, since a run that never terminates has no culprit. This makes
  `withBlame` monotone, so a `partial_fixpoint` may recurse under it.
-/
@[expose]
def Interp.withBlame (op : OperationPtr) : Interp α → Interp α
  | .fail none => .fail (some op)
  | .ub none => .ub (some op)
  | x => x

@[simp, grind =] theorem Interp.withBlame_ok : (Interp.ok a).withBlame op = .ok a := rfl
@[simp, grind =] theorem Interp.withBlame_spin : (Interp.spin : Interp α).withBlame op = .spin := rfl

/-- `withBlame` is monotone, because it returns `spin` unchanged. -/
@[partial_fixpoint_monotone]
theorem Interp.monotone_withBlame [Lean.Order.PartialOrder γ] (f : γ → Interp α)
    (hmono : Lean.Order.monotone f) : Lean.Order.monotone (fun x => (f x).withBlame op) := by
  intro x y h
  rcases Interp.rel_iff.mp (hmono x y h) with heq | heq
  · simp only [heq, Interp.withBlame]
    exact Interp.rel_iff.mpr (.inl rfl)
  · simp only [heq]
    exact Lean.Order.PartialOrder.rel_refl

@[simp, grind =] theorem Interp.withBlame_eq_ok_iff (x : Interp α) :
    x.withBlame op = .ok a ↔ x = .ok a := by
  unfold Interp.withBlame; split <;> simp [reduceCtorEq]

/-- Blaming an operation keeps a run that never terminates. -/
@[simp, grind =] theorem Interp.withBlame_eq_spin_iff (x : Interp α) :
    x.withBlame op = .spin ↔ x = .spin := by
  unfold Interp.withBlame; split <;> simp [reduceCtorEq]

@[simp, grind =] theorem Interp.isFail_withBlame (x : Interp α) :
    (x.withBlame op).isFail = x.isFail := by
  unfold Interp.withBlame; split <;> rfl

@[simp, grind =] theorem Interp.isUB_withBlame (x : Interp α) :
    (x.withBlame op).isUB = x.isUB := by
  unfold Interp.withBlame; split <;> rfl

end Veir
