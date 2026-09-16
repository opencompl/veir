/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon, Alex Keizer
-/
module

public import QPFTypes.PFunctor.Multivariate.Basic
public import QPFTypes.PFunctor.Univariate.M

/-!
# The M construction as a multivariate polynomial functor.

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.

## Main definitions

* `M.mk`     - constructor
* `M.dest`   - destructor
* `M.corec`  - corecursor: useful for formulating infinite, productive computations
* `M.bisim`  - bisimulation: proof technique to show the equality of infinite objects

## Implementation notes

Dual view of M-types:

* `mp`: polynomial functor
* `M`: greatest fixed point of a polynomial functor

Specifically, we define the polynomial functor `mp` as:

* A := a possibly infinite tree-like structure without information in the nodes
* B := given the tree-like structure `t`, `B t` is a valid path
  from the root of `t` to any given node.

As a result `mp α` is made of a dataless tree and a function from
its valid paths to values of `α`

The difference with the polynomial functor of an initial algebra is
that `A` is a possibly infinite tree.

## Reference

* Jeremy Avigad, Mario M. Carneiro and Simon Hudon.
  [*Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

@[expose] public section

namespace QPFTypes
namespace MvPFunctor

open TypeVec

universe u

variable {n : Nat} (P : MvPFunctor.{u} (n + 1))

/-- A path from the root of a tree to one of its node -/
inductive M.Path : P.last.M → Fin n → Type u
  | root (x : P.last.M)
          (a : P.A)
          (f : P.last.B a → P.last.M)
          (h : PFunctor.M.dest x = ⟨a, f⟩)
          (i : Fin n)
          (c : P.drop.B a i) : M.Path x i
  | child (x : P.last.M)
          (a : P.A)
          (f : P.last.B a → P.last.M)
          (h : PFunctor.M.dest x = ⟨a, f⟩)
          (j : P.last.B a)
          (i : Fin n)
          (c : M.Path (f j) i) : M.Path x i

instance M.Path.inhabited (x : P.last.M) {i} [Inhabited (P.drop.B x.head i)] :
    Inhabited (M.Path P x i) :=
  let a := PFunctor.M.head x
  let f := PFunctor.M.children x
  ⟨M.Path.root _ a f
      (PFunctor.M.casesOn' x
        (r := fun _ => PFunctor.M.dest x = ⟨a, f⟩)
        <| by
        intros; simp [a]; rfl)
      _ default⟩

/-- Polynomial functor of the M-type of `P`. `A` is a data-less
possibly infinite tree whereas, for a given `a : A`, `B a` is a valid
path in tree `a` so that `mp α` is made of a tree and a function
from its valid paths to the values it contains -/
def mp : MvPFunctor n where
  A := P.last.M
  B := M.Path P

/-- `n`-ary M-type for `P` -/
def M (α : TypeVec n) : Type _ :=
  P.mp α

instance mvfunctorM : MvFunctor P.M := by delta M; infer_instance
instance : LawfulMvFunctor P.M := inferInstanceAs (LawfulMvFunctor P.mp)

instance inhabitedM {α : TypeVec _} [I : Inhabited P.A] [∀ i : Fin n, Inhabited (α i)] :
    Inhabited (P.M α) :=
  @Obj.inhabited _ (mp P) _ (@PFunctor.M.inhabited P.last I) _

/-- construct through corecursion the shape of an M-type
without its contents -/
def M.corecShape {β : Type v} (g₀ : β → P.A) (g₂ : ∀ b : β, P.last.B (g₀ b) → β) :
    β → P.last.M :=
  PFunctor.M.corec fun b => ⟨g₀ b, g₂ b⟩

/-- Proof of type equality as an arrow -/
def castDropB {a a' : P.A} (h : a = a') : P.drop.B a ⟹ P.drop.B a' := fun _i b => Eq.recOn h b

/-- Proof of type equality as a function -/
def castLastB {a a' : P.A} (h : a = a') : P.last.B a → P.last.B a' := fun b => Eq.recOn h b

/-- Using corecursion, construct the contents of an M-type -/
def M.corecContents {α : TypeVec.{u} n}
    {β : Type v}
    (g₀ : β → P.A)
    (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : ∀ b : β, P.last.B (g₀ b) → β)
    (x : _)
    (b : β)
    (h : x = M.corecShape P g₀ g₂ b) :
    M.Path P x ⟹ α
  | _, M.Path.root x a f h' i c =>
    have : a = g₀ b := by
      subst h; cases h'; rfl
    g₁ b i (P.castDropB this i c)
  | _, M.Path.child x a f h' j i c =>
    have h₀ : a = g₀ b := by
      subst h; cases h'; rfl
    have h₁ : f j = M.corecShape P g₀ g₂ (g₂ b (castLastB P h₀ j)) := by
      subst h; cases h'; rfl
    M.corecContents g₀ g₁ g₂ (f j) (g₂ b (P.castLastB h₀ j)) h₁ i c

/-- Corecursor for M-type of `P` -/
def M.corec' {α : TypeVec n} {β : Type v} (g₀ : β → P.A) (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : ∀ b : β, P.last.B (g₀ b) → β) : β → P.M α := fun b =>
  ⟨M.corecShape P g₀ g₂ b, M.corecContents P g₀ g₁ g₂ _ _ rfl⟩

/-- Corecursor for M-type of `P` -/
def M.corec {α : TypeVec n} {β : Type u} (g : β → P (α.append1 β)) : β → P.M α :=
  M.corec' P (fun b => (g b).fst) (fun b => dropFun (g b).snd) fun b => lastFun (g b).snd

/-- Implementation of destructor for M-type of `P` -/
def M.pathDestLeft {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) : P.drop.B a ⟹ α := fun i c =>
  f' i (M.Path.root x a f h i c)

/-- Implementation of destructor for M-type of `P` -/
def M.pathDestRight {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) :
    ∀ j : P.last.B a, M.Path P (f j) ⟹ α := fun j i c => f' i (M.Path.child x a f h j i c)

/-- Destructor for M-type of `P` -/
def M.dest' {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) : P (α.append1 (P.M α)) :=
  ⟨a, splitFun (M.pathDestLeft P h f') fun x => ⟨f x, M.pathDestRight P h f' x⟩⟩

/-- Destructor for M-types -/
def M.dest {α : TypeVec n} (x : P.M α) : P (α ::: P.M α) :=
  let ⟨_, _⟩ := PFunctor.M.dest x.fst
  M.dest' P rfl x.snd

/-- Constructor for M-types -/
def M.mk {α : TypeVec n} : P (α.append1 (P.M α)) → P.M α :=
  M.corec _ fun i => (TypeVec.id ::: M.dest P) <$$> i

/-! ### `dest` lemmas -/
section DestLemmas

theorem M.dest'_eq_dest' {α : TypeVec n} {x : P.last.M} {a₁ : P.A}
    {f₁ : P.last.B a₁ → P.last.M} (h₁ : PFunctor.M.dest x = ⟨a₁, f₁⟩) {a₂ : P.A}
    {f₂ : P.last.B a₂ → P.last.M} (h₂ : PFunctor.M.dest x = ⟨a₂, f₂⟩) (f' : M.Path P x ⟹ α) :
    M.dest' P h₁ f' = M.dest' P h₂ f' := by cases h₁.symm.trans h₂; rfl

theorem M.dest_eq_dest' {α : TypeVec n} {x : P.last.M} {a : P.A}
    {f : P.last.B a → P.last.M} (h : PFunctor.M.dest x = ⟨a, f⟩)
    (f' : M.Path P x ⟹ α) : M.dest P ⟨x, f'⟩ = M.dest' P h f' :=
  M.dest'_eq_dest' ..

theorem M.dest_corec' {α : TypeVec.{u} n} {β : Type u} (g₀ : β → P.A)
    (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α) (g₂ : ∀ b : β, P.last.B (g₀ b) → β) (x : β) :
    M.dest P (M.corec' P g₀ g₁ g₂ x) = ⟨g₀ x, splitFun (g₁ x) (M.corec' P g₀ g₁ g₂ ∘ g₂ x)⟩ := by
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem M.dest_corec {α : TypeVec n} {β : Type u} (g : β → P (α.append1 β)) (x : β) :
    M.dest P (M.corec P g x) = (TypeVec.id ::: M.corec P g) <$$> g x := by
  rw [M.corec, M.dest_corec']
  obtain ⟨a, f⟩ := g x
  simp only [MvPFunctor.map_eq]
  congr 1
  rw [← split_dropFun_lastFun f, appendFun_comp_splitFun]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
theorem M.dest_map {α β : TypeVec n} (g : α ⟹ β) (x : P.M α) :
    M.dest P (g <$$> x) = (g ::: fun x => g <$$> x) <$$> M.dest P x := by
  obtain ⟨a, f⟩ := x
  simp only [MvFunctor.map, M.dest]
  rcases PFunctor.M.dest a with ⟨a', f'⟩
  simp only [M.dest', MvPFunctor.map_eq, appendFun_comp_splitFun]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
theorem M.map_dest {α β : TypeVec n} (g : (α ::: P.M α) ⟹ (β ::: P.M β)) (x : P.M α)
    (h : ∀ x : P.M α, lastFun g x = (dropFun g <$$> x : P.M β)) :
    g <$$> M.dest P x = M.dest P (dropFun g <$$> x) := by
  rw [M.dest_map]; congr
  apply eq_of_drop_last_eq (by simp)
  simp only [lastFun_appendFun]
  ext1; apply h

end DestLemmas

/-! ## Bisimulation -/

/--
Bisimilarity: `x` and `y` are bisimilar if they share the same head
and non-recursive content, and each pair of corresponding children is again bisimilar.
-/
coinductive IsBisim {α : TypeVec n} : M P α → M P α → Prop where
  | step {x y : M P α} {a : P.A} {f : P.drop.B a ⟹ α} {g g' : P.last.B a → M P α} :
        M.dest P x = ⟨a, splitFun f g⟩ → M.dest P y = ⟨a, splitFun f g'⟩
        → (∀ i, IsBisim (g i) (g' i))
        → IsBisim x y

/-- One-step unfolding of IsBisim: extract the witness data -/
theorem IsBisim.destruct {α : TypeVec n} {x y : M P α} (h : IsBisim P x y) :
    ∃ (a : P.A) (f : P.drop.B a ⟹ α) (g g' : P.last.B a → M P α),
      M.dest P x = ⟨a, splitFun f g⟩ ∧
      M.dest P y = ⟨a, splitFun f g'⟩ ∧
      ∀ i, IsBisim P (g i) (g' i) := by
  cases h with
  | step e₁ e₂ h' => exact ⟨_, _, _, _, e₁, e₂, h'⟩

set_option backward.isDefEq.respectTransparency false in
/-- Helper lemma for bisimulation proof -/
private theorem M.bisim_lemma {α : TypeVec n} {a₁ : (mp P).A} {f₁ : (mp P).B a₁ ⟹ α} {a' : P.A}
    {f' : (P.B a').drop ⟹ α} {f₁' : (P.B a').last → M P α}
    (e₁ : M.dest P ⟨a₁, f₁⟩ = ⟨a', splitFun f' f₁'⟩) :
    ∃ (g₁' : _) (e₁' : PFunctor.M.dest a₁ = ⟨a', g₁'⟩),
      f' = M.pathDestLeft P e₁' f₁ ∧
        f₁' = fun x : (last P).B a' => ⟨g₁' x, M.pathDestRight P e₁' f₁ x⟩ := by
  generalize ef : @splitFun n _ (append1 α (M P α)) f' f₁' = ff at e₁
  let he₁' := PFunctor.M.dest a₁
  rcases e₁' : he₁' with ⟨a₁', g₁'⟩
  rw [M.dest_eq_dest' _ e₁'] at e₁
  cases e₁; exact ⟨_, e₁', splitFun_inj ef⟩

/-- Bisimulation principle: bisimilar M-type elements are equal. -/
theorem M.bisim {α : TypeVec n} {x y : M P α} (h : IsBisim P x y) : x = y := by
  let R : P.M α → P.M α → Prop := fun x y => IsBisim P x y
  -- First show the shapes (univariate M-types) are equal
  obtain ⟨a₁, f₁⟩ := x
  obtain ⟨a₂, f₂⟩ := y
  dsimp [mp] at *
  obtain rfl : a₁ = a₂ := by
    apply PFunctor.M.bisim
    apply PFunctor.M.IsBisim.coinduct (fun a₁ a₂ => ∃ x y : P.M α, R x y ∧ x.1 = a₁ ∧ y.1 = a₂)
    · rintro _ _ ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩
      obtain ⟨a', f', f₁', f₂', e₁, e₂, h'⟩ := r.destruct
      rcases M.bisim_lemma P e₁ with ⟨g₁', e₁', rfl, rfl⟩
      rcases M.bisim_lemma P e₂ with ⟨g₂', e₂', _, rfl⟩
      exact ⟨_, g₁', g₂', e₁', e₂', fun b => ⟨_, _, h' b, rfl, rfl⟩⟩
    · exact ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, h, rfl, rfl⟩
  congr 1
  -- Now prove the path functions are equal using path induction
  funext i p
  induction p with (
    obtain ⟨a', f', f₁', f₂', e₁, e₂, h''⟩ := h.destruct
    obtain ⟨g₁', e₁', rfl, rfl⟩ := M.bisim_lemma P e₁
    obtain ⟨g₂', e₂', e₃, rfl⟩ := M.bisim_lemma P e₂
    cases h'.symm.trans e₁'
    cases h'.symm.trans e₂'
  )
  | root x a f h' i c =>
    exact congrFun (congrFun e₃ i) c
  | child x a f h' j i c IH =>
    exact IH _ _ (h'' _)

end MvPFunctor
end QPFTypes
