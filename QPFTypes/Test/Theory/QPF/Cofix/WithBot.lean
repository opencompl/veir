module

import QPFTypes

/-!
# `partial_fixpoint` on a `CofixWithBot` type

Streams, `StreamF α S = α × S`, have no shape free of `α`, so `Cofix StreamF` has no
`HasBot` instance without assuming `α` inhabited. `CofixWithBot StreamF` has one regardless:
the result is the type of *partial* streams, where `⊥` cuts the stream off.
-/

namespace QPFTypes.Test.WithBot

open QPF Lean.Order

@[qpf] def StreamF (α S : liveParam Type) := α × S

/-- Possibly-partial streams. -/
abbrev PStream (a : Type) : Type :=
  CofixWithBot (@TypeFun.ofCurried 2 StreamF) #t[a]

example (a : Type) : CCPO (PStream a) := inferInstance

variable {a b : Type}

def PStream.cons (x : a) (xs : PStream a) : PStream a :=
  Cofix.mk (Comp.mk (some (x, xs)))

def PStream.dest (xs : PStream a) : Option (a × PStream a) :=
  Cofix.dest xs

@[simp, grind =]
theorem PStream.dest_cons (x : a) (xs : PStream a) :
    (Cofix.dest (cons x xs)).get = some (x, xs) := by
  simp [cons]; rfl

@[partial_fixpoint_monotone]
theorem PStream.cons_mono {γ : Type} [PartialOrder γ] (x : a) (f : γ → PStream a)
    (hf : monotone f) : monotone (fun y => PStream.cons x (f y)) := by
  apply Cofix.mk_map_mono
    (Comp.mk (some (x, ())) : (@TypeFun.ofCurried 2 StreamF).WithBot (#t[a] ::: Unit))
    (fun y _ => f y)
  exact fun y₁ y₂ h _ => hf y₁ y₂ h

/-- Not productive: `⊥`. -/
def PStream.spin : PStream a := PStream.spin
partial_fixpoint

/-- Drops elements until `p` holds; not productive. -/
def PStream.dropUntil (p : a → Bool) (xs : PStream a) : PStream a :=
  match PStream.dest xs with
  | none => Cofix.bot _
  | some (x, xs') => if p x then .cons x xs' else PStream.dropUntil p xs'
partial_fixpoint


/-! ## Casting a total stream out of `CofixWithBot` -/

/-- Total streams. -/
def Stream (a : Type) : Type :=
  Cofix (@TypeFun.ofCurried 2 StreamF) #t[a]

def Stream.head (xs : Stream a) : a := (Cofix.dest xs).1

def Stream.tail (xs : Stream a) : Stream a := (Cofix.dest xs).2

/-! ### repeat -/

def PStream.repeat (x : a) : PStream a := .cons x (PStream.repeat x)
partial_fixpoint

theorem PStream.repeat_hasNoBot (x : a) : (PStream.repeat x).HasNoBot := by
  apply CofixWithBot.HasNoBot.coinduct (fun z => z = PStream.repeat x) _ _ rfl
  rintro _ rfl
  refine ⟨(x, PStream.repeat x), ?_, fun _ => rfl⟩
  conv => lhs; rw [PStream.repeat.eq_1]
  exact congrArg Comp.get (Cofix.dest_mk _)

/-- `repeat x`, as a total stream. -/
def Stream.repeat (x : a) : Stream a :=
  CofixWithBot.get (PStream.repeat x) (PStream.repeat_hasNoBot x)

/-! ### map -/

def PStream.map (f : α → β) (xs : Stream α) : PStream β :=
  .cons (f xs.head) (map f xs.tail)
partial_fixpoint

def Stream.map (xs : Stream α) (f : α → β) : Stream β :=
  CofixWithBot.get (PStream.map f xs) <| by
    apply CofixWithBot.HasNoBot.coinduct (fun z => ∃ xs, z = PStream.map f xs) _ _ ⟨xs, rfl⟩
    rintro _ ⟨xs, rfl⟩
    rw [PStream.map.eq_1]
    exact ⟨_, PStream.dest_cons _ _, fun _ => ⟨_, rfl⟩⟩


/-! ### filter -/

def PStream.filter (xs : Stream α) (P : α → Bool) : PStream α :=
  if P xs.head then
    cons xs.head (filter xs.tail P)
  else
    filter xs.tail P
partial_fixpoint

/-- Some element of `xs`, now or later, satisfies `P`. -/
inductive Stream.Eventually (P : α → Bool) : Stream α → Prop
  | here {xs : Stream α} : P xs.head → Stream.Eventually P xs
  | later {xs : Stream α} : Stream.Eventually P xs.tail → Stream.Eventually P xs

/-- At every point of `xs`, some future element satisfies `P`. -/
coinductive Stream.InfOften (P : α → Bool) : Stream α → Prop
  | mk {xs : Stream α} :
      Stream.Eventually P xs → Stream.InfOften P xs.tail → Stream.InfOften P xs

/-- The elements of `xs` satisfying `P`, as a total stream. -/
def Stream.filter (P : α → Bool) (xs : Stream α) (h : xs.InfOften P) : Stream α :=
  CofixWithBot.get (PStream.filter xs P) <| by
    apply CofixWithBot.HasNoBot.coinduct
      (fun z => ∃ xs, xs.InfOften P ∧ z = PStream.filter xs P) _ _ ⟨xs, h, rfl⟩
    rintro _ ⟨xs, h, rfl⟩
    cases h with | mk hev hinf =>
    induction hev with
    | @here xs hP =>
      rw [PStream.filter.eq_1, hP]
      exact ⟨_, PStream.dest_cons _ _, fun _ => ⟨_, hinf, rfl⟩⟩
    | @later xs hev ih =>
      rw [PStream.filter.eq_1]
      split
      · exact ⟨_, PStream.dest_cons _ _, fun _ => ⟨_, hinf, rfl⟩⟩
      · cases hinf with | mk _ hinf' => exact ih hinf'


end QPFTypes.Test.WithBot
