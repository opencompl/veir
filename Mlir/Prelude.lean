module

@[expose] public section

@[inline, specialize] def _root_.USize.foldM {α : Type u} {m : Type u → Type v} [Monad m] (n : USize) (f : (i : USize) → i < n → α → m α) (init : α) : m α :=
  let rec @[specialize] loop (i : USize) (h : i ≤ n) (x : α) : m α :=
    if h : i = 0 then pure x else f (n-i-1) (by sorry) x >>= loop i sorry
  termination_by i
  decreasing_by sorry
  loop n (by sorry) init

-- A useful definition to get information in a do monad about a succeeding bind.
abbrev satisfies {α : Type} (f : Option α) : Option {x : α // f = some x} :=
  match f with
  | none => none
  | some x => some ⟨x, by rfl⟩

-- We only consider 64 bit systems.
axiom System.Platform.numBits_64_axiom : System.Platform.numBits = 64

@[simp, grind=]
theorem System.Platform.numBits_64 : System.Platform.numBits = 64 := by
  exact numBits_64_axiom

@[simp, grind=]
theorem USize.size_eq_64_bits : USize.size = UInt64.size := by
  simp only [USize.size, System.Platform.numBits_64]

@[grind=]
theorem UInt32_size_sub (x : UInt32) :
    UInt32.size.toUSize - x.toUSize = (UInt32.size - x.toNat).toUSize := by
  by_cases Hzero: x = 0
  · subst x; simp
  · have : x > 0 := by grind only
    rw [←USize.toNat_inj]
    rw [USize.toNat_ofNat_of_lt']
    · simp only [Nat.toUSize_eq, USize.toNat_sub, UInt32.toNat_toUSize, USize.toNat_ofNat',
      Nat.add_mod_mod, UInt32.size]
      cases System.Platform.numBits_eq <;> rename_i HnumBits <;> rw [HnumBits]
      · simp only [Nat.reducePow, Nat.add_mod_right, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one,
        Nat.reduceAdd]
        grind only [= UInt32.lt_iff_toNat_lt, cases Or]
      · grind only [Nat.add_sub_assoc, UInt32.toNat_lt_size]
    · have := USize.size_eq
      grind

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

-- TODO(leo): remove this
macro:50 "rlet" pat:term "←" expr:term "in" rest:term : term =>
  `(match _ : $expr:term with
      | none => none
      | some $pat => $rest)

def Option.maybe (p : α → β → Prop) (x : Option α) (y : β) : Prop :=
  ∀ z, x = some z → p z y

@[grind .] theorem Option.maybe_some : p x y → (some x).maybe p y := by grind [maybe]
@[grind .] theorem Option.maybe_none : none.maybe p y := by grind [maybe]

def Option.maybe₁ (p : α → Prop) (x : Option α)  : Prop :=
  ∀ z, x = some z → p z

@[grind .] theorem Option.maybe₁_some : p x → (some x).maybe₁ p := by grind [maybe₁]
@[grind .] theorem Option.maybe₁_none : none.maybe₁ p := by grind [maybe₁]
