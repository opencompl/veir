module

public import Veir.Interpreter.Interp

public section

namespace Veir.Puddle.CTree

/--
A nondeterministic creation computation, with a separate obligation for invalid construction.
An empty outcome relation must not hide unresolved handles or incorrect result counts.
-/
structure CreationM (α : Type) where
  safe : Prop
  outcomes : Interp α → Prop

namespace CreationM

@[expose]
def pure (a : α) : CreationM α := ⟨True, fun outcome => outcome = .ok a⟩

/-- Sequence successful outcomes and propagate interpreter errors without calling `next`. -/
@[expose]
def bind (m : CreationM α) (next : α → CreationM β) : CreationM β where
  safe := m.safe ∧ ∀ a, m.outcomes (.ok a) → (next a).safe
  outcomes outcome :=
    (∃ a, m.outcomes (.ok a) ∧ (next a).outcomes outcome) ∨
    (∃ op, m.outcomes (.ub op) ∧ outcome = .ub op) ∨
    (∃ op, m.outcomes (.fail op) ∧ outcome = .fail op)

instance : Monad CreationM where
  pure := CreationM.pure
  bind := CreationM.bind

/-- Interpret an operation using its complete relation of possible outcomes. -/
@[expose]
def choose (outcomes : Interp α → Prop) : CreationM α := ⟨True, outcomes⟩

/-- A construction error is an unsatisfied obligation, not an interpreter failure or no behavior. -/
@[expose]
def invalid : CreationM α := ⟨False, fun _ => False⟩

/-- Require a construction invariant before returning a value. -/
@[expose]
def checked (condition : Prop) (a : α) : CreationM α :=
  ⟨condition, fun outcome => outcome = .ok a⟩

@[ext]
theorem ext {m n : CreationM α} (hsafe : m.safe ↔ n.safe)
    (houtcomes : ∀ outcome, m.outcomes outcome ↔ n.outcomes outcome) : m = n := by
  cases m
  cases n
  congr 1
  · exact propext hsafe
  · funext outcome
    exact propext (houtcomes outcome)

@[simp]
theorem pure_bind (a : α) (next : α → CreationM β) :
    (CreationM.pure a).bind next = next a := by
  apply ext <;> simp [CreationM.pure, CreationM.bind]

@[simp]
theorem bind_pure (m : CreationM α) : m.bind CreationM.pure = m := by
  apply ext
  · simp [CreationM.bind, CreationM.pure]
  · intro outcome
    cases outcome <;> simp [CreationM.bind, CreationM.pure]

/-- Consume deterministic assignment updates before introducing outcome quantifiers. -/
theorem checked_bind (condition : Prop) (a : α) (next : α → CreationM β) :
    (checked condition a).bind next =
      ⟨condition ∧ (next a).safe, (next a).outcomes⟩ := by
  apply ext <;> simp [CreationM.bind, checked]

@[simp]
theorem invalid_bind (next : α → CreationM β) :
    (invalid : CreationM α).bind next = invalid := by
  apply ext <;> simp [CreationM.bind, invalid]

theorem bind_assoc (m : CreationM α) (next : α → CreationM β) (last : β → CreationM γ) :
    (m.bind next).bind last = m.bind (fun a => (next a).bind last) := by
  apply ext
  · simp [CreationM.bind]
    grind
  · intro outcome
    cases outcome <;> simp [CreationM.bind] <;> grind

instance : LawfulMonad CreationM := LawfulMonad.mk' CreationM
  (by intro α m; exact bind_pure m)
  (by intro α β a next; exact pure_bind a next)
  (by intro α β γ m next last; exact bind_assoc m next last)

/-- Check construction safety and every complete outcome against a single postcondition. -/
@[expose]
def Models (m : CreationM α) (k : Interp α → Prop) : Prop :=
  m.safe ∧ ∀ outcome, m.outcomes outcome → k outcome

@[simp]
theorem models_pure (a : α) (k : Interp α → Prop) : (CreationM.pure a).Models k ↔ k (.ok a) := by
  simp [Models, CreationM.pure]

@[simp]
theorem models_invalid (k : Interp α → Prop) : (invalid : CreationM α).Models k ↔ False := by
  simp [Models, invalid]

@[simp]
theorem models_checked (condition : Prop) (a : α) (k : Interp α → Prop) :
    (checked condition a).Models k ↔ condition ∧ k (.ok a) := by
  simp [Models, checked]

@[simp]
theorem models_choose (outcomes : Interp α → Prop) (k : Interp α → Prop) :
    (choose outcomes).Models k ↔ ∀ outcome, outcomes outcome → k outcome := by
  simp [Models, choose]

/-- Bridge the outcome monad to the previous continuation semantics. -/
theorem models_bind (m : CreationM α) (next : α → CreationM β) (k : Interp β → Prop) :
    (m.bind next).Models k ↔
      m.Models (fun outcome => outcome.foldProp (fun a => (next a).Models k) k) := by
  simp only [Models, CreationM.bind]
  constructor
  · rintro ⟨⟨hm, hnext⟩, h⟩
    refine ⟨hm, ?_⟩
    intro outcome houtcome
    cases outcome with
    | ok a =>
      exact ⟨hnext a houtcome, fun result hresult => h result (.inl ⟨a, houtcome, hresult⟩)⟩
    | ub op => exact h (.ub op) (.inr (.inl ⟨op, houtcome, rfl⟩))
    | fail op => exact h (.fail op) (.inr (.inr ⟨op, houtcome, rfl⟩))
  · rintro ⟨hm, h⟩
    refine ⟨⟨hm, fun a ha => (h (.ok a) ha).1⟩, ?_⟩
    rintro result (⟨a, ha, hresult⟩ | ⟨op, hop, rfl⟩ | ⟨op, hop, rfl⟩)
    · exact (h (.ok a) ha).2 result hresult
    · exact h (.ub op) hop
    · exact h (.fail op) hop

/-- Eliminate a named result after its successful interpretation fixes it to a concrete value. -/
@[simp]
theorem forall_result_eq (condition : β → Prop) (value : β → α) (post : α → β → Prop) :
    (∀ result choice, condition choice → result = value choice → post result choice) ↔
      ∀ choice, condition choice → post (value choice) choice := by
  constructor
  · intro h choice hchoice
    exact h (value choice) choice hchoice rfl
  · rintro h result choice hchoice rfl
    exact h choice hchoice

end CreationM

end Veir.Puddle.CTree
