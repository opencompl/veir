/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
module

public import QPFTypes.Theory.TypeVec.Basic

/-!

# The categorical structure of tuples of types

## Features

* `α ⟹ β`    - n-tuples of maps
* `f ⊚ g`     - composition

Also, support functions for operating with n-tuples of types, such as:

* `appendFun f g` - appends a function g to an n-tuple of functions
* `dropFun f`     - drops the last function from an n+1-tuple
* `lastFun f`     - returns the last function of a tuple.

Since e.g. `appendFun α.dropFun α.lastFun` is propositionally equal to `α` but not definitionally equal
to it, we need support functions and lemmas to mediate between constructions.

This file is a modified version of `Mathlib.Data.TypeVec`, with `Fin2` replaced by `Fin` throughout,
this is also only a subset of the implemented features,
the rest are distributed in this directory.
-/


@[expose] public section

universe u v w x

namespace QPFTypes

/-- arrow in the category of `TypeVec` -/
def TypeVec.Arrow (α : TypeVec.{u} n) (β : TypeVec.{v} n) :=
  ∀ i : Fin n, α i → β i

@[inherit_doc] scoped infixl:40 " ⟹ " => TypeVec.Arrow

variable {n : Nat}

/-- append an arrow and a function for arbitrary source and target type vectors -/
def TypeVec.splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α → last α') : α ⟹ α' :=
  Fin.cases g f

/-- append an arrow and a function as well as their respective source and target types / typevecs -/
def TypeVec.appendFun {α α' : TypeVec n} {β β' : Type _} (f : α ⟹ α') (g : β → β') :
    append1 α β ⟹ append1 α' β' :=
  splitFun f g

/-- arrow composition in the category of `TypeVec` -/
@[grind]
def TypeVec.comp (g : β ⟹ γ) (f : α ⟹ β)
    : α ⟹ γ :=
  fun i x => g i (f i x)

@[inherit_doc] scoped infixr:80 " ⊚ " => TypeVec.comp -- type as \oo
@[inherit_doc] scoped infixl:0 " ::: " => TypeVec.appendFun

namespace TypeVec

section

variable {α : TypeVec.{u} n} {β : TypeVec.{v} n} {γ : TypeVec.{w} n} {δ : TypeVec.{x} n}

/-- Extensionality for arrows -/
@[ext]
theorem Arrow.ext (f g : α ⟹ β) :
    (∀ i, f i = g i) → f = g := by
  intro h; funext i; apply h

instance Arrow.inhabited (α β : TypeVec n) [∀ i, Inhabited (β i)] : Inhabited (α ⟹ β) :=
  ⟨fun _ _ => default⟩

/-- identity of arrow composition -/
def id {α : TypeVec n} : α ⟹ α := fun _ x => x

@[simp, grind =]
theorem id_comp (f : α ⟹ β) : id ⊚ f = f :=
  rfl

@[simp, grind =]
theorem comp_id (f : α ⟹ β) : f ⊚ id = f :=
  rfl

@[grind =]
theorem comp_assoc
    (h : γ ⟹ δ) (g : β ⟹ γ) (f : α ⟹ β) :
    (h ⊚ g) ⊚ f = h ⊚ g ⊚ f :=
  rfl

end

/-- split off the prefix of an arrow -/
def dropFun {α β : TypeVec (n + 1)} (f : α ⟹ β) : drop α ⟹ drop β := fun i => f i.succ

/-- split off the last function of an arrow -/
def lastFun {α β : TypeVec (n + 1)} (f : α ⟹ β) : last α → last β :=
  f 0

/-- arrow in the category of `0-length` vectors -/
def nilFun {α : TypeVec 0} {β : TypeVec 0} : α ⟹ β := fun i => i.elim0

theorem eq_of_drop_last_eq {α β : TypeVec (n + 1)} {f g : α ⟹ β} (h₀ : dropFun f = dropFun g)
    (h₁ : lastFun f = lastFun g) : f = g := by
  refine funext (fun x => ?_)
  refine Fin.cases ?_ ?_ x
  · apply h₁
  · intro j
    apply congrFun h₀

@[simp]
theorem dropFun_splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α → last α') :
    dropFun (splitFun f g) = f :=
  rfl

/-- turn an equality into an arrow -/
def Arrow.mp {α β : TypeVec n} (h : α = β) : α ⟹ β
  | _ => Eq.mp (congrFun h _)

/-- turn an equality into an arrow, with reverse direction -/
-- TODO(WS): This should be an alias to Arrow.mp h.symm
def Arrow.mpr {α β : TypeVec n} (h : α = β) : β ⟹ α
  | _ => Eq.mpr (congrFun h _)

/-- decompose a vector into its prefix appended with its last element -/
def toAppend1DropLast {α : TypeVec (n + 1)} : α ⟹ (drop α ::: last α) :=
  Arrow.mpr (append1_drop_last _)

/-- stitch two bits of a vector back together -/
def fromAppend1DropLast {α : TypeVec (n + 1)} : (drop α ::: last α) ⟹ α :=
  Arrow.mp (append1_drop_last _)

@[simp]
theorem dropFun_from_append1_drop_last {α : TypeVec (n + 1)} :
    dropFun (@fromAppend1DropLast _ α) = id :=
  rfl

@[simp]
theorem lastFun_from_append1_drop_last {α : TypeVec (n + 1)} :
    lastFun (@fromAppend1DropLast _ α) = _root_.id :=
  rfl

@[simp, grind =]
theorem lastFun_splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α → last α') :
    lastFun (splitFun f g) = g :=
  rfl

@[simp]
theorem dropFun_id {α : TypeVec (n + 1)} : dropFun (@TypeVec.id _ α) = id :=
  rfl

@[simp, grind =]
theorem dropFun_appendFun {α α' : TypeVec n} {β β' : Type _} (f : α ⟹ α') (g : β → β') :
    dropFun (f ::: g) = f := rfl

@[simp]
theorem lastFun_appendFun {α α' : TypeVec n} {β β' : Type _} (f : α ⟹ α') (g : β → β') :
    lastFun (f ::: g) = g := rfl

theorem split_dropFun_lastFun {α α' : TypeVec (n + 1)} (f : α ⟹ α') :
    splitFun (dropFun f) (lastFun f) = f :=
  eq_of_drop_last_eq rfl rfl

theorem splitFun_inj {α α' : TypeVec (n + 1)} {f f' : drop α ⟹ drop α'} {g g' : last α → last α'}
    (H : splitFun f g = splitFun f' g') : f = f' ∧ g = g' := by
  rw [← dropFun_splitFun f g, H, ← lastFun_splitFun f g, H]; simp

theorem appendFun_inj {α α' : TypeVec n} {β β' : Type _} {f f' : α ⟹ α'} {g g' : β → β'} :
    (f ::: g : (α ::: β) ⟹ _) = (f' ::: g' : (α ::: β) ⟹ _)
    → f = f' ∧ g = g' :=
  splitFun_inj

theorem splitFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : drop α₀ ⟹ drop α₁)
    (f₁ : drop α₁ ⟹ drop α₂) (g₀ : last α₀ → last α₁) (g₁ : last α₁ → last α₂) :
    splitFun (f₁ ⊚ f₀) (g₁ ∘ g₀) = splitFun f₁ g₁ ⊚ splitFun f₀ g₀ :=
  eq_of_drop_last_eq rfl rfl

@[simp, grind =]
theorem appendFun_comp_splitFun {α γ : TypeVec n} {β δ : Type _} {ε : TypeVec (n + 1)}
    (f₀ : drop ε ⟹ α) (f₁ : α ⟹ γ) (g₀ : last ε → β) (g₁ : β → δ) :
    appendFun f₁ g₁ ⊚ splitFun f₀ g₀ = splitFun (α' := γ.append1 δ) (f₁ ⊚ f₀) (g₁ ∘ g₀) :=
  (splitFun_comp _ _ _ _).symm

@[grind =, grind =_]
theorem appendFun_comp {α₀ α₁ α₂ : TypeVec n}
    {β₀ β₁ β₂ : Type _}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂)
    (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (f₁ ⊚ f₀ ::: g₁ ∘ g₀) = (f₁ ::: g₁) ⊚ (f₀ ::: g₀) :=
  eq_of_drop_last_eq rfl rfl

theorem appendFun_comp' {α₀ α₁ α₂ : TypeVec n} {β₀ β₁ β₂ : Type _}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (f₁ ::: g₁) ⊚ (f₀ ::: g₀) = (f₁ ⊚ f₀ ::: g₁ ∘ g₀) :=
  eq_of_drop_last_eq rfl rfl

theorem nilFun_comp {α₀ : TypeVec 0} (f₀ : α₀ ⟹ Fin.elim0) : nilFun ⊚ f₀ = f₀ :=
  funext fun i => i.elim0

@[grind =]
theorem appendFun_comp_id {α : TypeVec n} {β₀ β₁ β₂ : Type u} (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (@id _ α ::: g₁ ∘ g₀) = (id ::: g₁) ⊚ (id ::: g₀) :=
  eq_of_drop_last_eq rfl rfl

@[simp]
theorem dropFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
    dropFun (f₁ ⊚ f₀) = dropFun f₁ ⊚ dropFun f₀ :=
  rfl

@[simp]
theorem lastFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
    lastFun (f₁ ⊚ f₀) = lastFun f₁ ∘ lastFun f₀ :=
  rfl

theorem appendFun_aux {α α' : TypeVec n} {β β' : Type _} (f : (α ::: β) ⟹ (α' ::: β')) :
    (dropFun f ::: lastFun f) = f :=
  eq_of_drop_last_eq rfl rfl

@[simp, grind =]
theorem appendFun_id_id {α : TypeVec n} {β : Type _} :
    (@TypeVec.id n α ::: @_root_.id β) = TypeVec.id :=
  eq_of_drop_last_eq rfl rfl

/-- cases distinction for an arrow in the category of 0-length type vectors -/
def typevecCasesNil₃ {β : ∀ v v' : TypeVec 0, v ⟹ v' → Sort _}
    (f : β Fin.elim0 Fin.elim0 nilFun) :
    ∀ v v' fs, β v v' fs := fun v v' fs => by
  refine cast ?_ f
  have eq₁ : v = Fin.elim0 := by funext i; exact i.elim0
  have eq₂ : v' = Fin.elim0 := by funext i; exact i.elim0
  have eq₃ : fs = nilFun := by funext i; exact i.elim0
  cases eq₁; cases eq₂; cases eq₃; rfl

/-- cases distinction for an arrow in the category of (n+1)-length type vectors -/
def typevecCasesCons₃ (n : Nat) {β : ∀ v v' : TypeVec (n + 1), v ⟹ v' → Sort _}
    (F : ∀ (t t') (f : t → t') (v v' : TypeVec n) (fs : v ⟹ v'),
    β (v ::: t) (v' ::: t') (fs ::: f)) :
    ∀ v v' fs, β v v' fs := by
  intro v v'
  rw [← append1_drop_last v, ← append1_drop_last v']
  intro fs
  rw [← split_dropFun_lastFun fs]
  apply F

/-- specialized cases distinction for an arrow in the category of 0-length type vectors -/
def typevecCasesNil₂ {β : Fin.elim0 ⟹ Fin.elim0 → Sort _} (f : β nilFun) : ∀ f, β f := by
  intro g
  suffices g = nilFun by rwa [this]
  ext i
  exact i.elim0

/-- specialized cases distinction for an arrow in the category of (n+1)-length type vectors -/
def typevecCasesCons₂ (n : Nat) (t t' : Type _) (v v' : TypeVec n)
    {β : (v ::: t) ⟹ (v' ::: t') → Sort _}
    (F : ∀ (f : t → t') (fs : v ⟹ v'), β (fs ::: f)) : ∀ fs, β fs := by
  intro fs
  rw [← split_dropFun_lastFun fs]
  apply F

theorem typevecCasesNil₂_appendFun {β : Fin.elim0 ⟹ Fin.elim0 → Sort _} (f : β nilFun) :
    typevecCasesNil₂ f nilFun = f :=
  rfl

theorem typevecCasesCons₂_appendFun (n : Nat) (t t' : Type _) (v v' : TypeVec n)
    {β : (v ::: t) ⟹ (v' ::: t') → Sort _}
    (F : ∀ (f : t → t') (fs : v ⟹ v'), β (fs ::: f))
    (f fs) :
    typevecCasesCons₂ n t t' v v' F (fs ::: f) = F f fs :=
  rfl

/-- `const x α` is an arrow that ignores its source and constructs a `TypeVec` that
contains nothing but `x` -/
protected def const {β} (x : β) : ∀ {n} (α : TypeVec n), α ⟹ «repeat» _ β
  | 0, _, i => i.elim0
  | .succ _, α, i =>
    Fin.cases (motive := fun i => α i → («repeat» (.succ _) β) i)
      (fun _ => x)
      (fun j => TypeVec.const x (drop α) j)
      i

theorem const_append1 {β γ} (x : γ) {n} (α : TypeVec n) :
    TypeVec.const x (α ::: β) = appendFun (TypeVec.const x α) fun _ => x := rfl

theorem eq_nilFun {α β : TypeVec 0} (f : α ⟹ β) : f = nilFun := by
  ext x; exact x.elim0

theorem id_eq_nilFun {α : TypeVec 0} : @id _ α = nilFun := by
  ext x; exact x.elim0

theorem const_nil {β} (x : β) (α : TypeVec 0) : TypeVec.const x α = nilFun := by
  ext i : 1; exact i.elim0

/-- Projection from a repeat vector. Since `repeat n α` has `α` at every index,
this extracts the underlying `α` value. -/
-- TODO(WS): i is not unique here so should be explicit
def ofRepeat {α : Sort _} : ∀ {n : Nat} {i : Fin n}, «repeat» n α i → α
  | _ + 1, ⟨0, _⟩ => fun x => x
  | _ + 1, ⟨k + 1, hk⟩ => @ofRepeat α _ ⟨k, Nat.lt_of_succ_lt_succ hk⟩

theorem const_iff_true : ∀ {n} {α : TypeVec n} {i : Fin n} {x p},
    ofRepeat (TypeVec.const p α i x) ↔ p
  | _ + 1, _, ⟨0, _⟩, _, _ => Iff.rfl
  | _ + 1, _, ⟨k + 1, hk⟩, _, _ => const_iff_true (i := ⟨k, Nat.lt_of_succ_lt_succ hk⟩)
