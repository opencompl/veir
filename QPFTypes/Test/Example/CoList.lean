module

import QPFTypes

/-!
# Example: possibly-infinite lists

`CoList a` is built as `Cofix` of the shape functor `CoListF a CoList = Unit ⊕ (a × CoList)`,
whose `QPF` and `IsPolynomial` instances are derived by `@[qpf]`.
We then define the constructors, prove them monotone,
and define `CoList.map` with `partial_fixpoint`.

The bottom element of the order is the infinite repetition of the default shape. `nil` is
the only shape without an `a` to supply, so `⊥ = nil`: a definition that fails to be
productive yields a list that is cut off at that point. This is the same choice as for
`Stream` in [ISTA-PLV/coinductive](https://github.com/ISTA-PLV/coinductive).
-/

namespace QPFTypes.Test.CoList

open QPF (Cofix)
open Lean.Order

/-! ## The type -/

@[qpf] def CoListF (α CoList : liveParam Type) :=
    Unit ⊕ (α × CoList)

instance {α β} : Inhabited (CoListF α β) where
  default := .inl ()

/-- Possibly-infinite lists. -/
def CoList (a : Type) : Type :=
  Cofix (@TypeFun.ofCurried 2 CoListF) #t[a]
  deriving PartialOrder, CCPO

variable {a b : Type}

/-! ## Constructors and destructor -/

@[match_pattern] def CoListF.nil : CoListF α β := .inl ()
def CoList.nil : CoList a := Cofix.mk .nil

@[match_pattern] def CoListF.cons (x : α) (xs : β) : CoListF α β := .inr (x, xs)
def CoList.cons (x : a) (xs : CoList a) : CoList a :=
  Cofix.mk (.cons x xs)

def CoList.dest (xs : CoList α) : CoListF α (CoList α) :=
  Cofix.dest xs

@[simp, grind =] theorem CoList.dest_nil :
    CoList.dest (CoList.nil : CoList a) = CoListF.nil :=
  Cofix.dest_mk _

@[simp, grind =] theorem CoList.dest_cons (x : a) (xs : CoList a) :
    CoList.dest (CoList.cons x xs) = CoListF.cons x xs :=
  Cofix.dest_mk _

/-! ## Monotonicity of the constructors -/

@[partial_fixpoint_monotone]
theorem CoList.cons_mono {γ : Type} [PartialOrder γ] (x : a) (f : γ → CoList a)
    (hf : monotone f) : monotone (fun y => CoList.cons x (f y)) := by
  apply Cofix.mk_map_mono (Sum.inr (x, ())) (fun y _ => f y)
  exact fun y₁ y₂ h _ => hf y₁ y₂ h

/-! ## `map` via `partial_fixpoint` -/

def CoList.map (f : a → b) (xs : CoList a) : CoList b :=
  match CoList.dest xs with
  | .nil => .nil
  | .cons x xs' => .cons (f x) (CoList.map f xs')
partial_fixpoint

@[simp]
theorem CoList.map_nil (f : a → b) : CoList.map f .nil = .nil := by
  rw [CoList.map]; rfl

@[simp]
theorem CoList.map_cons (f : a → b) (x : a) (xs : CoList a) :
    CoList.map f (.cons x xs) = .cons (f x) (CoList.map f xs) := by
  rw [CoList.map]; simp

end QPFTypes.Test.CoList
