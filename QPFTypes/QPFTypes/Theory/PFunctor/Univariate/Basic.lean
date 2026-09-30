/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

/-!
# Polynomial Functors

This file defines polynomial functors and the W-type construction as a polynomial functor.
-/
@[expose] public section

namespace QPFTypes

universe u v uA uB uA₁ uB₁ uA₂ uB₂ v₁ v₂ v₃

-- Note: `set_option linter.checkUnivs` should not apply here,
-- we really do want two separate universe levels
set_option linter.checkUnivs false in
/-- A polynomial functor `P` is given by a type `A` and a family `B` of types over `A`. `P` maps
any type `α` to a new type `P α`, which is defined as the sigma type `Σ x, P.B x → α`.

An element of `P α` is a pair `⟨a, f⟩`, where `a` is an element of a type `A` and
`f : B a → α`. Think of `a` as the shape of the object and `f` as an index to the relevant
elements of `α`.
-/
structure PFunctor where
  /-- The head type -/
  A : Type uA
  /-- The child family of types -/
  B : A → Type uB

namespace PFunctor

instance : Inhabited PFunctor :=
  ⟨⟨default, default⟩⟩

variable (P : PFunctor.{uA, uB}) {α : Type v₁} {β : Type v₂} {γ : Type v₃}

/-- Applying `P` to an object of `Type` -/
@[coe]
def Obj (α : Type v) : Type (max v uA uB) :=
  Σ x : P.A, P.B x → α

instance : CoeFun PFunctor.{uA, uB} (fun _ => Type v → Type (max v uA uB)) where
  coe := Obj

/-- Applying `P` to a morphism of `Type` -/
def map (f : α → β) : P α → P β :=
  fun ⟨a, g⟩ => ⟨a, f ∘ g⟩

instance Obj.inhabited [Inhabited P.A] [Inhabited α] : Inhabited (P α) :=
  ⟨⟨default, default⟩⟩

instance : Functor P.Obj where map := @map P

/-- We prefer `PFunctor.map` to `Functor.map` because it is universe-polymorphic. -/
@[simp]
theorem map_eq_map {α β : Type v} (f : α → β) (x : P α) : f <$> x = P.map f x :=
  rfl

@[simp]
protected theorem map_eq (f : α → β) (a : P.A) (g : P.B a → α) :
    P.map f ⟨a, g⟩ = ⟨a, f ∘ g⟩ :=
  rfl

@[simp]
protected theorem id_map : ∀ x : P α, P.map id x = x := fun ⟨_, _⟩ => rfl

@[simp]
protected theorem map_map (f : α → β) (g : β → γ) :
    ∀ x : P α, P.map g (P.map f x) = P.map (g ∘ f) x := fun ⟨_, _⟩ => rfl

instance : LawfulFunctor (Obj.{v} P) where
  map_const := rfl
  id_map x := P.id_map x
  comp_map f g x := P.map_map f g x |>.symm

/-- The W-type (well-founded tree) associated to a polynomial functor.
    Nodes are labeled by shapes `a : P.A` and branching is given by `P.B a`. -/
inductive W (P : PFunctor.{uA, uB}) : Type (max uA uB)
  | mk (a : P.A) (f : P.B a → W P) : W P

/- Inhabitants of W types is awkward to encode as an instance assumption because there needs to be a
value `a : P.A` such that `P.B a` is empty to yield a finite tree. -/

variable {P}

/-- The root element of a W tree -/
def W.head : W P → P.A
  | .mk a _f => a

/-- The children of the root of a W tree -/
def W.children : ∀ x : W P, P.B (W.head x) → W P
  | .mk _a f => f

/-- The destructor for W-types -/
def W.dest : W P → P (W P)
  | .mk a f => ⟨a, f⟩

/-- The constructor for W-types -/
def W.mk' : P (W P) → W P
  | ⟨a, f⟩ => .mk a f

@[simp]
theorem W.dest_mk' (p : P (W P)) : W.dest (W.mk' p) = p := by cases p; rfl

@[simp]
theorem W.mk'_dest (p : W P) : W.mk' (W.dest p) = p := by cases p; rfl

variable (P)

/-- `Idx` identifies a location inside the application of a polynomial functor. For `F : PFunctor`,
`x : F α` and `i : F.Idx`, `i` can designate one part of `x` or is invalid, if `i.1 ≠ x.1`. -/
def Idx : Type (max uA uB) :=
  Σ x : P.A, P.B x

instance Idx.inhabited [Inhabited P.A] [Inhabited (P.B default)] : Inhabited P.Idx :=
  ⟨⟨default, default⟩⟩

variable {P}

/-- `x.iget i` takes the component of `x` designated by `i` if any, or returns a default value -/
def Obj.iget [DecidableEq P.A] {α} [Inhabited α] (x : P α) (i : P.Idx) : α :=
  if h : i.1 = x.1 then x.2 (cast (congrArg _ h) i.2) else default

@[simp]
theorem fst_map (x : P α) (f : α → β) : (P.map f x).1 = x.1 := by cases x; rfl

@[simp]
theorem iget_map [DecidableEq P.A] [Inhabited α] [Inhabited β] (x : P α)
    (f : α → β) (i : P.Idx) (h : i.1 = x.1) : (P.map f x).iget i = f (x.iget i) := by
  simp only [Obj.iget, fst_map, *, dite_eq_left]
  cases x
  rfl

end PFunctor
