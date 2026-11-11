module

public import QPFTypes

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

@[expose] public section

namespace QPFTypes.Test.CoList

open QPF (Cofix)
open Lean.Order

/-! ## The type -/

@[qpf] def CoListF (α CoList : liveParam Type) :=
    Unit ⊕ (α × CoList)

instance {α β} : Inhabited (CoListF α β) where
  default := .inl ()

/-- Possibly-infinite lists. Use `curry` so the wrapper inherits the standard
curry/uncurry QPF instances when used as a nested container. -/
def CoList (a : Type) : Type :=
  TypeFun.curry (Cofix (@TypeFun.ofCurried 2 CoListF)) a
  deriving PartialOrder, CCPO

-- `Cofix` is itself polynomial; expose that instance for the curried `CoList` wrapper
-- so other examples can use it as a nested container (see `CoTree.lean`).
instance CoList.instQPF : QPF (@TypeFun.ofCurried 1 CoList) :=
  QPF.instOfCurriedCurry (F := Cofix (@TypeFun.ofCurried 2 CoListF))

instance CoList.instIsPolynomial : QPF.IsPolynomial (@TypeFun.ofCurried 1 CoList) :=
  QPF.IsPolynomial.instOfCurriedCurry (F := Cofix (@TypeFun.ofCurried 2 CoListF))

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

/-! ## Guarded corecursion specifications

Bertot's *CoInduction in Coq* uses this type as `Llist`. See `README.md` in this
directory for the guardedness taxonomy and `GuardedCorecursion.v` for the Rocq checks.
Unlike the existing safe `map` above, the following `unsafe def`s only check the bodies'
types: they are motivating examples for `codef`, not executable lazy implementations.
-/

/-- A corecursive map with `f` captured outside the local recursion. This is the shape
of `comap` in Korkut's *A Rose Tree Is Blooming*, and is deliberately separate from
the `partial_fixpoint` implementation above. Rocq can unfold this helper to a nested
cofixpoint in `CoTree.map` and `CoTree.unfold`. Making `f` an explicit recursive
parameter instead causes those outer definitions to fail guardedness checking. -/
unsafe def CoList.mapCorec (f : a → b) : CoList a → CoList b :=
  let rec go (xs : CoList a) : CoList b :=
    match xs.dest with
    | .nil => .nil
    | .cons x xs' => .cons (f x) (go xs')
  go

/-- Append a possibly-infinite list. The `nil` branch returns an existing value without
constructing anything: only branches containing recursive calls need guards. If `xs`
is infinite, `ys` is never reached. -/
unsafe def CoList.append (xs ys : CoList a) : CoList a :=
  match xs.dest with
  | .nil => ys
  | .cons x xs' => .cons x (CoList.append xs' ys)

end QPFTypes.Test.CoList
