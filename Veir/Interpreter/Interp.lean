module

public import Veir.IR.Basic
import all Init.Internal.Order.Basic

public section

namespace Veir

/--
  The interpreter monad. An interpretation step has three outcomes. UB is a property
  of the execution, not of any value, so it lives here rather than inside
  `RuntimeValue` or `LLVM.Int`.
-/
inductive Interp (α : Type) where
  /-- Interpreter could not proceed (malformed IR, unsupported op) at `op`, if known. -/
  | fail (op : Option OperationPtr)
  /-- Execution triggered undefined behaviour at `op`, if known. -/
  | ub (op : Option OperationPtr)
  /-- Successful execution producing `a`. -/
  | ok (a : α)
deriving Inhabited

@[expose]
def Interp.map {α β : Type} (f : α → β) : Interp α → Interp β
  | .fail op => .fail op
  | .ub op => .ub op
  | .ok a => .ok (f a)

@[simp, grind =] theorem Interp.map_fail : Interp.map f (.fail op) = .fail op := rfl
@[simp, grind =] theorem Interp.map_ub : Interp.map f (.ub op) = .ub op := rfl
@[simp, grind =] theorem Interp.map_ok : Interp.map f (.ok a) = .ok (f a) := rfl

instance : Monad Interp where
  pure x := .ok x
  bind x f := match x with
    | .fail op => .fail op
    | .ub op => .ub op
    | .ok a => f a

instance : MonadLift Option Interp where
  monadLift
    | none => .fail none
    | some v => .ok v

/-!
  The interpreter of a control-flow graph is a `partial_fixpoint`, and a run
  that never terminates takes the least element of the order below. That
  element is `ub`, which is the outcome that permits the target of a
  refinement to do anything, whereas `fail` says the interpreter met
  something it cannot handle. Without these instances the least element would
  be an arbitrary value picked by choice, about which nothing can be proven.
-/

instance : Lean.Order.PartialOrder (Interp α) :=
  inferInstanceAs (Lean.Order.PartialOrder (Lean.Order.FlatOrder (.ub : Interp α)))

instance : Lean.Order.CCPO (Interp α) :=
  inferInstanceAs (Lean.Order.CCPO (Lean.Order.FlatOrder (.ub : Interp α)))

/-- `ub` is below every outcome, and the other outcomes are only below themselves. -/
theorem Interp.rel_iff {x y : Interp α} :
    Lean.Order.PartialOrder.rel x y ↔ x = .ub ∨ x = y := by
  constructor
  · intro h
    cases h
    · exact .inl rfl
    · exact .inr rfl
  · rintro (rfl | rfl)
    · exact Lean.Order.FlatOrder.rel.bot
    · exact Lean.Order.FlatOrder.rel.refl

/--
  A predicate that holds of `ub` is admissible, because `ub` is the least
  element. This is what lets a `partial_fixpoint` induction discharge the
  case of a run that never terminates.
-/
theorem Interp.admissible_of_ub {α : Type} (P : Interp α → Prop) (hub : P .ub) :
    Lean.Order.admissible P := by
  intro c hchain h
  by_cases hex : ∃ x, c x ∧ x ≠ .ub
  · obtain ⟨x, hcx, hne⟩ := hex
    rcases Interp.rel_iff.mp (Lean.Order.le_csup hchain hcx) with rfl | rfl
    · exact absurd rfl hne
    · exact h _ hcx
  · have hbelow : Lean.Order.PartialOrder.rel (Lean.Order.CCPO.csup hchain) (.ub : Interp α) := by
      apply Lean.Order.csup_le hchain
      intro y hy
      have : y = .ub := Classical.byContradiction fun hne => hex ⟨y, hy, hne⟩
      exact this ▸ Lean.Order.PartialOrder.rel_refl
    rcases Interp.rel_iff.mp hbelow with heq | heq <;> exact heq ▸ hub

@[simp, grind =] theorem Interp.pure_eq (a : α) : (pure a : Interp α) = .ok a := rfl
@[simp, grind =] theorem Interp.bind_ok (a : α) (f : α → Interp β) :
    (Interp.ok a >>= f) = f a := rfl
@[simp, grind =] theorem Interp.bind_ub (f : α → Interp β) :
    ((.ub op : Interp α) >>= f) = .ub op := rfl
@[simp, grind =] theorem Interp.bind_fail (f : α → Interp β) :
    ((.fail op : Interp α) >>= f) = .fail op := rfl
@[simp, grind =] theorem Interp.liftOption_none : ((none : Option α) : Interp α) = .fail none := rfl
@[simp, grind =] theorem Interp.liftOption_some (a : α) : ((some a : Option α) : Interp α) = .ok a := rfl

/-- Binding is monotone, so a `partial_fixpoint` may recurse under `do` notation. -/
instance : Lean.Order.MonoBind Interp where
  bind_mono_left h := by
    rcases Interp.rel_iff.mp h with rfl | rfl
    · simp only [Interp.bind_ub]
      exact Interp.rel_iff.mpr (.inl rfl)
    · exact Lean.Order.PartialOrder.rel_refl
  bind_mono_right {α β a f₁ f₂} h := by
    cases a
    · simp only [Interp.bind_fail]; exact Lean.Order.PartialOrder.rel_refl
    · simp only [Interp.bind_ub]; exact Lean.Order.PartialOrder.rel_refl
    · simp only [Interp.bind_ok]; exact h _

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

/-- If reporting any failure or UB, blame `op` for it. -/
@[expose]
def Interp.withBlame (op : OperationPtr) : Interp α → Interp α
  | .fail none => .fail (some op)
  | .ub none => .ub (some op)
  | x => x

@[simp, grind =] theorem Interp.withBlame_ok : (Interp.ok a).withBlame op = .ok a := rfl

@[simp, grind =] theorem Interp.withBlame_eq_ok_iff (x : Interp α) :
    x.withBlame op = .ok a ↔ x = .ok a := by
  unfold Interp.withBlame; split <;> simp [reduceCtorEq]

@[simp, grind =] theorem Interp.isFail_withBlame (x : Interp α) :
    (x.withBlame op).isFail = x.isFail := by
  unfold Interp.withBlame; split <;> rfl

@[simp, grind =] theorem Interp.isUB_withBlame (x : Interp α) :
    (x.withBlame op).isUB = x.isUB := by
  unfold Interp.withBlame; split <;> rfl

end Veir
