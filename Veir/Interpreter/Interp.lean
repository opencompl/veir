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
  map := Interp.map

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
  inferInstanceAs (Lean.Order.PartialOrder (Lean.Order.FlatOrder (.ub none : Interp α)))

instance : Lean.Order.CCPO (Interp α) :=
  inferInstanceAs (Lean.Order.CCPO (Lean.Order.FlatOrder (.ub none : Interp α)))

/-- `ub none` is below every outcome, and the other outcomes are only below themselves. -/
theorem Interp.rel_iff {x y : Interp α} :
    Lean.Order.PartialOrder.rel x y ↔ x = .ub none ∨ x = y := by
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
theorem Interp.admissible_of_ub {α : Type} (P : Interp α → Prop) (hub : P (.ub none)) :
    Lean.Order.admissible P := by
  intro c hchain h
  by_cases hex : ∃ x, c x ∧ x ≠ .ub none
  · obtain ⟨x, hcx, hne⟩ := hex
    rcases Interp.rel_iff.mp (Lean.Order.le_csup hchain hcx) with rfl | rfl
    · exact absurd rfl hne
    · exact h _ hcx
  · have hbelow : Lean.Order.PartialOrder.rel (Lean.Order.CCPO.csup hchain) (.ub none : Interp α) := by
      apply Lean.Order.csup_le hchain
      intro y hy
      have : y = .ub none := Classical.byContradiction fun hne => hex ⟨y, hy, hne⟩
      exact this ▸ Lean.Order.PartialOrder.rel_refl
    rcases Interp.rel_iff.mp hbelow with heq | heq <;> exact heq ▸ hub

@[simp, grind norm] theorem Interp.pure_eq (a : α) : (pure a : Interp α) = .ok a := rfl
@[simp, grind =] theorem Interp.bind_ok (a : α) (f : α → Interp β) :
    (Interp.ok a >>= f) = f a := rfl
@[simp, grind =] theorem Interp.bind_ub (f : α → Interp β) :
    ((.ub op : Interp α) >>= f) = .ub op := rfl
@[simp, grind =] theorem Interp.bind_fail (f : α → Interp β) :
    ((.fail op : Interp α) >>= f) = .fail op := rfl
@[grind =] theorem Interp.bind_def {α β : Type} (x : Interp α) (f : α → Interp β) :
    (x >>= f) = match x with
      | .fail op => .fail op
      | .ub op => .ub op
      | .ok a => f a := rfl
@[simp, grind =] theorem Interp.liftOption_none : ((none : Option α) : Interp α) = .fail none := rfl
@[simp, grind =] theorem Interp.liftOption_some (a : α) : ((some a : Option α) : Interp α) = .ok a := rfl

instance : LawfulMonad Interp :=
  LawfulMonad.mk' Interp
    (id_map := fun x => by cases x <;> rfl)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun x _ _ => by cases x <;> rfl)

/-- Running a computation twice runs it once: `Interp` has no state. -/
theorem Interp.bind_bind_self {α β : Type} (x : Interp α) (k : α → α → Interp β) :
    (x >>= fun a => x >>= fun b => k a b) = x >>= fun a => k a a := by
  cases x <;> rfl

theorem Interp.bind_eq_bind_iff {α β : Type} {x : Interp α} {f g : α → Interp β} :
    (x >>= f) = (x >>= g) ↔ ∀ a, x = .ok a → f a = g a := by
  cases x <;> simp [Interp.bind_def]

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

/-- A loop runs as another does wherever every step of it runs as the other's step does. -/
theorem Interp.forIn_list_eq_ok {α β : Type} (l : List α) {f g : α → β → Interp (ForInStep β)}
    (hfg : ∀ a b s, f a b = .ok s → g a b = .ok s) {init r : β}
    (h : forIn l init f = .ok r) : forIn l init g = .ok r := by
  induction l generalizing init with
  | nil => simpa using h
  | cons a l ih =>
    simp only [List.forIn_cons] at h ⊢
    rcases hf : f a init with _ | _ | (b | b) <;> rw [hf] at h
    · simp at h
    · simp at h
    · rw [hfg a init _ hf]; simpa using h
    · rw [hfg a init _ hf]; exact ih h

/-- A loop over a range runs as another does wherever every step of it runs as the other's does. -/
theorem Interp.forIn_range_eq_ok {β : Type} (r : Std.Legacy.Range)
    {f g : Nat → β → Interp (ForInStep β)} (hfg : ∀ a b s, f a b = .ok s → g a b = .ok s)
    {init s : β} (h : forIn r init f = .ok s) : forIn r init g = .ok s := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at h ⊢
  exact Interp.forIn_list_eq_ok _ hfg h

/-! ## Refinement -/

/--
An interpretation result `source` is refined by `target` given a refinement relation `R`
on the underlying values. This asserts:
* every well-defined outcome `.ok a` of `source` must be matched by an outcome
  `.ok b` of `target` with `R a b`;
* when `source` is undefined behaviour (`.ub`) or failed interpretation (`.fail`), `target`
  is unconstrained
-/
@[expose]
def Interp.isRefinedBy (R : α → β → Prop) (source : Interp α) (target : Interp β) : Prop :=
  match source, target with
  | .ok a, .ok b => R a b
  | .ub _, _ => True
  | .fail _, _ => True
  | _, _ => False

/-- Any outcome is refined by itself. -/
theorem Interp.isRefinedBy_eq_refl {α : Type} (x : Interp α) : Interp.isRefinedBy Eq x x := by
  cases x <;> simp [Interp.isRefinedBy]

/-- A computation that succeeds with the same result, bound to a continuation. -/
theorem Interp.isRefinedBy_eq_bind_left {α β : Type} {x y : Interp α}
    (h : Interp.isRefinedBy Eq x y) (f : α → Interp β) :
    Interp.isRefinedBy Eq (x >>= f) (y >>= f) := by
  cases x <;> cases y <;> simp [Interp.isRefinedBy] at h ⊢
  subst h
  exact Interp.isRefinedBy_eq_refl _

/-- A computation bound to continuations that succeed with the same results. -/
theorem Interp.isRefinedBy_eq_bind_right {α β : Type} (x : Interp α) {f g : α → Interp β}
    (h : ∀ a, Interp.isRefinedBy Eq (f a) (g a)) :
    Interp.isRefinedBy Eq (x >>= f) (x >>= g) := by
  cases x with
  | ok a => exact h a
  | _ => simp [Interp.isRefinedBy]

/-- A computation that succeeds wherever another does, with the same result. -/
theorem Interp.isRefinedBy_eq_of_ok {α : Type} {x y : Interp α}
    (h : ∀ a, x = .ok a → y = .ok a) : Interp.isRefinedBy Eq x y := by
  cases x with
  | ok a => rw [h a rfl]; exact Interp.isRefinedBy_eq_refl _
  | _ => simp [Interp.isRefinedBy]

/-- A refinement followed by a computation that succeeds with the same result. -/
theorem Interp.isRefinedBy_trans_eq {α β : Type} {R : α → β → Prop} {s : Interp α}
    {t t' : Interp β} (h : Interp.isRefinedBy R s t) (h' : Interp.isRefinedBy Eq t t') :
    Interp.isRefinedBy R s t' := by
  cases s <;> cases t <;> cases t' <;> simp_all [Interp.isRefinedBy]

end Veir
