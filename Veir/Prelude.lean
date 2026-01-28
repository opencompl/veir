module

public section

macro:50 "rlet" pat:term ":=" expr:term rest:term : term =>
  `(match _ : $expr:term with
      | $pat => $rest)

macro:50 "rlet" pat:term "←" expr:term  rest:term : term =>
  `(match _ : $expr:term with
      | none => none
      | some $pat => $rest)

macro:50 "rlet" h:ident ":" pat:term "←" expr:term  rest:term : term =>
  `(match $h:ident : $expr:term with
      | none => none
      | some $pat => $rest)

-- TODO: remove this
macro:50 "rlet" pat:term "←" expr:term "in" rest:term : term =>
  `(match _ : $expr:term with
      | none => none
      | some $pat => $rest)

def Option.maybe (p : α → β → Prop) (x : Option α) (y : β) : Prop :=
  ∀ z, x = some z → p z y

theorem Option.maybe_def (p : α → β → Prop) (x : Option α) (y : β) :
    x.maybe p y ↔ ∀ z, x = some z → p z y := by
  simp [Option.maybe]

@[grind .] theorem Option.maybe_some : p x y → (some x).maybe p y := by grind [maybe]
@[grind .] theorem Option.maybe_none : none.maybe p y := by grind [maybe]

def Option.maybe₁ (p : α → Prop) (x : Option α)  : Prop :=
  ∀ z, x = some z → p z

theorem Option.maybe₁_def (p : α → Prop) (x : Option α) :
    x.maybe₁ p ↔ ∀ z, x = some z → p z := by
  simp [Option.maybe₁]

@[grind .] theorem Option.maybe₁_some : p x → (some x).maybe₁ p := by grind [maybe₁]
@[grind .] theorem Option.maybe₁_none : none.maybe₁ p := by grind [maybe₁]
