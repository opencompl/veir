module

import QPFTypes.Theory.QPF.Cofix

/-!
# `partial_fixpoint` on a `Cofix` type

The point of `QPFTypes.Theory.QPF.Cofix.Order` is ergonomics: corecursive definitions
should be writable directly, with `partial_fixpoint`, instead of by hand-rolling a
coalgebra for `Cofix.corec`. This file is the acceptance test for that claim.

We build the delay (partiality) monad `Delay R` as `Cofix` of the shape functor

```
DelayShape R X = now r | later x
```

by hand — polynomial functor, `QPF` instance, `IsPolynomial` instance — and then check
that `Delay.spin` and `Delay.bind` elaborate via `partial_fixpoint`. `Delay.bind` is the
interesting one: it recurses on `now` without a guarding constructor, so it is *not*
productive and could not be written with `Cofix.corec`.

`DelayShape` plays the role of `ITreeF` in the reference's `ITree/Definition.lean`.
-/

namespace QPFTypes.Test

open QPFTypes TypeVec MvFunctor QPF Lean.Order

universe u

/-! ## The shape functor -/

/-- One layer of a delayed computation: either a result, or a `later` step. -/
inductive DelayShape (R : Type u) (X : Type u) where
  | now (r : R)
  | later (x : X)
  deriving Inhabited

/-- `DelayShape R` as a function on type vectors. The single type-vector slot is the
recursive one. -/
def DelayF (R : Type u) : TypeVec.{u} 1 → Type u := fun v => DelayShape R (v 0)

/-- The shapes of `DelayShape R`: `now r` carries an `R` and has no children, `later` has
exactly one child. -/
abbrev DelayHead (R : Type u) : Type u := R ⊕ PUnit

/-- `DelayShape R` as a polynomial functor: `now r` has no recursive position, `later` has
one. -/
def delayP (R : Type u) : MvPFunctor.{u} 1 where
  A := DelayHead R
  B
    | .inl _ => TypeVec.nil ::: PEmpty
    | .inr _ => TypeVec.nil ::: PUnit

instance (R : Type u) : MvFunctor (DelayF R) where
  map f
    | .now r => .now r
    | .later x => .later (f 0 x)

instance (R : Type u) : QPF (DelayF R) where
  P := delayP R
  abs
    | ⟨.inl r, _⟩ => .now r
    | ⟨.inr _, f⟩ => .later (lastFun f ⟨⟩)
  repr
    | .now r => ⟨.inl r, splitFun nilFun (fun e => e.elim)⟩
    | .later x => ⟨.inr ⟨⟩, splitFun nilFun (fun _ => x)⟩
  abs_repr := by rintro v (_ | _) <;> rfl
  abs_map := by
    rintro v w f ⟨(_ | _), g⟩ <;> rfl

instance (R : Type u) : IsPolynomial (DelayF R) where
  repr_abs := by
    rintro v ⟨(r | ⟨⟩), g⟩
    · -- `now r`: both children families are maps out of `PEmpty`
      refine congrArg _ (eq_of_drop_last_eq ((eq_nilFun _).trans (eq_nilFun _).symm) ?_)
      funext e
      exact e.elim
    · -- `later`: the single child is `lastFun g ⟨⟩`
      refine congrArg _ (eq_of_drop_last_eq ((eq_nilFun _).trans (eq_nilFun _).symm) ?_)
      funext u
      cases u
      rfl

/-! ## The delay monad -/

/-- The delay (partiality) monad: a result after finitely many steps, or divergence. -/
abbrev Delay (R : Type u) : Type u := Cofix (DelayF R) TypeVec.nil

/-- The bottom shape: `later`, which carries no `R`. This is what makes `⊥` — the
everywhere-`later` tree, i.e. divergence — available without assuming `R` inhabited. -/
instance (R : Type u) : Inhabited (DelayF R (TypeVec.nil ::: PUnit)) :=
  ⟨.later ⟨⟩⟩

variable {R S : Type u}

/-- Return a result immediately. -/
def Delay.now (r : R) : Delay R := Cofix.mk (.now r)

/-- Take one step of delay. -/
def Delay.later (t : Delay R) : Delay R := Cofix.mk (.later t)

@[simp] theorem Delay.dest_now (r : R) : Cofix.dest (Delay.now r) = .now r := Cofix.dest_mk _
@[simp] theorem Delay.dest_later (t : Delay R) :
    Cofix.dest (Delay.later t) = .later t := Cofix.dest_mk _

/-! ## Monotonicity of `later`

This is the only thing `partial_fixpoint` needs beyond the `CCPO` instance, and it is a
direct instance of the generic `Cofix.mk_mono`. -/

@[partial_fixpoint_monotone]
theorem Delay.later_mono {γ : Type v} [PartialOrder γ] (f : γ → Delay R)
    (hf : monotone f) : monotone (fun x => Delay.later (f x)) :=
  Cofix.mk_mono (F := DelayF R) (Sum.inr ⟨⟩ : DelayHead R) nilFun (fun x _ => f x) (fun x y h _ => hf x y h)

/-! ## The acceptance test: `partial_fixpoint` -/

/-- Destructor at the `DelayShape` type, so that `match` sees the constructors. -/
def Delay.dest (x : Delay R) : DelayShape R (Delay R) := Cofix.dest x

@[simp] theorem Delay.dest_eq_now (r : R) : Delay.dest (Delay.now r) = .now r := Cofix.dest_mk _
@[simp] theorem Delay.dest_eq_later (t : Delay R) :
    Delay.dest (Delay.later t) = .later t := Cofix.dest_mk _

/-- Divergence: `later` forever. `partial_fixpoint` accepts this given `CCPO (Delay R)`
and `Delay.later_mono`; it is `⊥`. -/
def Delay.spin : Delay R := Delay.later Delay.spin
partial_fixpoint

/-- Monadic bind. -/
def Delay.bind (x : Delay R) (f : R → Delay S) : Delay S :=
  match Delay.dest x with
  | .now r => f r
  | .later t => Delay.later (Delay.bind t f)
partial_fixpoint

@[simp]
theorem Delay.bind_now (r : R) (f : R → Delay S) : Delay.bind (Delay.now r) f = f r := by
  rw [Delay.bind]; simp

@[simp]
theorem Delay.bind_later (t : Delay R) (f : R → Delay S) :
    Delay.bind (Delay.later t) f = Delay.later (Delay.bind t f) := by
  rw [Delay.bind]; simp

/-- The case that `Cofix.corec` cannot express: the recursive call is **not** guarded by a
constructor, so this definition is not productive. On input where `p` never holds it
denotes `⊥`.

This needs nothing beyond `CCPO (Delay Nat)` — the recursive occurrence is a bare
application, which Lean's own monotonicity lemmas handle. -/
def Delay.forever (p : Nat → Bool) (k : Nat) : Delay Nat :=
  if p k then Delay.now k else Delay.forever p (k + 1)
partial_fixpoint

theorem Delay.forever_eq (p : Nat → Bool) (k : Nat) :
    Delay.forever p k = if p k then Delay.now k else Delay.forever p (k + 1) := by
  rw [Delay.forever]

/-! ## The instances really are there -/

example : PartialOrder (Delay Nat) := inferInstance
noncomputable example : CCPO (Delay Nat) := inferInstance
example : IsPolynomial (DelayF Nat) := inferInstance

/-! ## Monotonicity of `bind`

`Delay.iter` recurses inside the *continuation* of a `bind`, so `partial_fixpoint` needs
`bind` to be monotone in its second argument. This is the analogue of `bind_mono` in the
reference's `ITree/Definition.lean`; where that proof inducts on finite approximations,
this one coinducts with `Cofix.le_coinduct`.
-/

/-- The polynomial decomposition of a `later` node. -/
theorem Delay.repr_dest_later (y : Delay R) :
    QPF.repr (Cofix.dest (Delay.later y))
      = (⟨Sum.inr ⟨⟩, splitFun nilFun (fun _ => y)⟩ :
          (QPF.P (DelayF R)) (TypeVec.nil ::: Delay R)) := by
  rw [Delay.dest_later]
  rfl

theorem Delay.bind_mono_right (x : Delay R) {u₁ u₂ : R → Delay S}
    (hu : ∀ r, u₁ r ⊑ u₂ r) : Delay.bind x u₁ ⊑ Delay.bind x u₂ := by
  refine Cofix.le_coinduct
    (fun p₁ p₂ => (p₁ ⊑ p₂) ∨
      ∃ z : Delay R, p₁ = Delay.bind z u₁ ∧ p₂ = Delay.bind z u₂)
    ?_ (Or.inr ⟨x, rfl, rfl⟩)
  rintro p₁ p₂ (h | ⟨z, rfl, rfl⟩)
  · -- already related: re-use one step of the order itself
    rcases Cofix.le_step h with hb | ⟨a, fd, g, g', h₁, h₂, h₃⟩
    · exact Or.inl hb
    · exact Or.inr ⟨a, fd, g, g', h₁, h₂, fun i => Or.inl (h₃ i)⟩
  · -- a `bind` pair: look at one layer of `z`
    rcases hz : Delay.dest z with r | t
    · -- `now r`: both sides step to the continuations, related by `hu`
      rw [show Delay.bind z u₁ = u₁ r by rw [Delay.bind, hz],
        show Delay.bind z u₂ = u₂ r by rw [Delay.bind, hz]]
      rcases Cofix.le_step (hu r) with hb | ⟨a, fd, g, g', h₁, h₂, h₃⟩
      · exact Or.inl hb
      · exact Or.inr ⟨a, fd, g, g', h₁, h₂, fun i => Or.inl (h₃ i)⟩
    · -- `later t`: same shape on both sides, children are again a `bind` pair
      rw [show Delay.bind z u₁ = Delay.later (Delay.bind t u₁) by rw [Delay.bind, hz],
        show Delay.bind z u₂ = Delay.later (Delay.bind t u₂) by rw [Delay.bind, hz]]
      exact Or.inr ⟨Sum.inr ⟨⟩, nilFun,
        (fun _ => Delay.bind t u₁), (fun _ => Delay.bind t u₂),
        Delay.repr_dest_later _, Delay.repr_dest_later _, fun _ => Or.inr ⟨t, rfl, rfl⟩⟩

@[partial_fixpoint_monotone]
theorem Delay.bind_mono {γ : Type v} [PartialOrder γ] (x : Delay R) (k : γ → R → Delay S)
    (hk : monotone k) : monotone (fun y => Delay.bind x (k y)) :=
  fun y₁ y₂ h => Delay.bind_mono_right x (fun r => hk y₁ y₂ h r)

/-- The non-productive loop combinator: `iter g` feeds `inl` results back into `g`. The
recursive call sits inside the continuation of a `bind`, with no guarding constructor. -/
def Delay.iter {α β : Type u} (g : α → Delay (α ⊕ β)) : α → Delay β :=
  fun a => Delay.bind (g a) (fun s =>
    match s with
    | .inl a' => Delay.iter g a'
    | .inr b => Delay.now b)
partial_fixpoint

end QPFTypes.Test
