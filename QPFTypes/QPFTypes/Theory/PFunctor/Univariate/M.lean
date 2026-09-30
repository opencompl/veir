/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import QPFTypes.Theory.PFunctor.Univariate.Basic

/-!
# M-types

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.
-/
@[expose] public section
namespace QPFTypes

universe uA uB w

open Nat Function

variable (F : PFunctor.{uA, uB})

namespace PFunctor

namespace Approx

/-- `CofixA F n` is an `n` level approximation of an M-type -/
inductive CofixA : Nat → Type (max uA uB)
  | continue : CofixA 0
  | intro {n} : ∀ a, (F.B a → CofixA n) → CofixA (n + 1)

/-- default inhabitant of `CofixA` -/
protected def CofixA.default [Inhabited F.A] : ∀ n, CofixA F n
  | 0 => CofixA.continue
  | n + 1 => CofixA.intro default fun _ => CofixA.default n

instance [Inhabited F.A] {n} : Inhabited (CofixA F n) :=
  ⟨CofixA.default F n⟩

theorem cofixA_eq_zero : ∀ x y : CofixA F 0, x = y
  | CofixA.continue, CofixA.continue => rfl

variable {F}

/-- The label of the root of the tree for a non-trivial approximation -/
def head' : ∀ {n}, CofixA F (n + 1) → F.A
  | _, CofixA.intro i _ => i

/-- For a non-trivial approximation, return all the subtrees of the root -/
def children' : ∀ {n} (x : CofixA F (n + 1)), F.B (head' x) → CofixA F n
  | _, CofixA.intro _ f => f

theorem approx_eta {n : Nat} (x : CofixA F (n + 1)) :
    x = CofixA.intro (head' x) (children' x) := by
  cases x; rfl

/-- Relation between two approximations of the cofix of a polynomial functor
that state they both contain the same data until one of them is truncated -/
inductive Agree : ∀ {n : Nat}, CofixA F n → CofixA F (n + 1) → Prop
  | continu (x : CofixA F 0) (y : CofixA F 1) : Agree x y
  | intro {n} {a} (x : F.B a → CofixA F n) (x' : F.B a → CofixA F (n + 1)) :
    (∀ i : F.B a, Agree (x i) (x' i)) → Agree (CofixA.intro a x) (CofixA.intro a x')

/-- Given an infinite series of approximations `approx`,
`AllAgree approx` states that they are all consistent with each other. -/
def AllAgree (x : ∀ n, CofixA F n) :=
  ∀ n, Agree (x n) (x (n + 1))

@[simp]
theorem agree_trivial {x : CofixA F 0} {y : CofixA F 1} : Agree x y := by constructor

@[grind →]
theorem agree_head {n} {x : CofixA F (n + 1)} {y : CofixA F (n + 2)} (h : Agree x y) :
    head' x = head' y := by
  cases h; rfl

theorem agree_children {n : Nat} (x : CofixA F (n + 1)) (y : CofixA F (n + 2)) {i j}
    (h₀ : HEq i j) (h₁ : Agree x y) : Agree (children' x i) (children' y j) := by
  obtain - | ⟨_, _, hagree⟩ := h₁; cases h₀
  apply hagree

/-- `truncate a` turns `a` into a more limited approximation -/
def truncate : ∀ {n : Nat}, CofixA F (n + 1) → CofixA F n
  | 0, CofixA.intro _ _ => CofixA.continue
  | _ + 1, CofixA.intro i f => CofixA.intro i <| truncate ∘ f

@[grind .]
theorem truncate_eq_of_agree {n : Nat} (x : CofixA F n) (y : CofixA F (n + 1)) (h : Agree x y) :
    truncate y = x := by
  induction n with
  | zero =>
    cases x; cases y; rfl
  | succ n n_ih =>
    cases h with
    | intro f f' h₁ =>
      simp only [truncate, Function.comp_def]
      congr 1
      grind

variable {X : Type w}
variable (f : X → F X)

/--
`sCorec f i n` creates an approximation of height `n`
of the final coalgebra of `f`
-/
def sCorec : X → ∀ n, CofixA F n
  | _, 0 => CofixA.continue
  | j, n + 1 => CofixA.intro (f j).1 fun i => sCorec ((f j).2 i) n

theorem P_corec (i : X) (n : Nat) : Agree (sCorec f i n) (sCorec f i (n + 1)) := by
  induction n generalizing i with
  | zero => constructor
  | succ n n_ih => exact .intro _ _ fun _ => n_ih _

/-- `Path F` provides indices to access internal nodes in `Corec F` -/
def Path (F : PFunctor.{uA, uB}) :=
  List F.Idx

instance Path.inhabited : Inhabited (Path F) :=
  ⟨[]⟩

instance CofixA.instSubsingleton : Subsingleton (CofixA F 0) :=
  ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩

theorem head_succ' (n m : Nat) (x : ∀ n, CofixA F n) (Hconsistent : AllAgree x) :
    head' (x (n + 1)) = head' (x (m + 1)) := by
  suffices ∀ k, head' (x (k + 1)) = head' (x 1) by
    rw [this n, this m]
  intro k
  induction k with
  | zero => rfl
  | succ k k_ih =>
    exact (agree_head (Hconsistent (k + 1))).symm.trans k_ih

end Approx

open Approx

/-- Internal definition for `M`. It is needed to avoid name clashes
between `M.mk` and `M.casesOn` and the declarations generated for
the structure -/
structure MIntl where
  /-- An `n`-th level approximation, for each depth `n` -/
  approx : ∀ n, CofixA F n
  /-- Each approximation agrees with the next -/
  consistent : AllAgree approx

/-- For polynomial functor `F`, `M F` is its final coalgebra -/
def M :=
  MIntl F

theorem M.default_consistent [Inhabited F.A] : ∀ n, Agree (default : CofixA F n) default
  | 0 => Agree.continu _ _
  | n + 1 => Agree.intro _ _ fun _ => M.default_consistent n

instance M.inhabited [Inhabited F.A] : Inhabited (M F) :=
  ⟨{ approx := default
     consistent := M.default_consistent _ }⟩

instance MIntl.inhabited [Inhabited F.A] : Inhabited (MIntl F) :=
  show Inhabited (M F) by infer_instance

namespace M

@[ext]
theorem ext' (x y : M F) (H : ∀ i : Nat, x.approx i = y.approx i) : x = y := by
  cases x; congr 1; grind

variable {X : Type _}
variable (f : X → F X)
variable {F}

/-- Corecursor for the M-type defined by `F`. -/
protected def corec (i : X) : M F where
  approx := sCorec f i
  consistent := P_corec _ _

/-- Given a tree generated by `F`, `head` gives us the first piece of data it contains -/
def head (x : M F) :=
  head' (x.approx 1)

/-- Return all the subtrees of the root of a tree `x : M F` -/
def children (x : M F) (i : F.B (head x)) : M F :=
  have H := fun n : Nat => @head_succ' _ n 0 x.approx x.consistent
  { approx n := children' (x.approx _) (cast (congrArg _ <| by simp only [head, H]) i)
    consistent := by
      intro n
      have P' := x.consistent (n + 1)
      apply agree_children _ _ _ P'
      grind
      }

/-- Select a subtree using an `i : F.Idx` or return an arbitrary tree if
`i` designates no subtree of `x` -/
def ichildren [Inhabited (M F)] [DecidableEq F.A] (i : F.Idx) (x : M F) : M F :=
  if H' : i.1 = head x then children x (cast (congrArg _ <| by simp only [head, H']) i.2)
  else default

theorem head_succ (n m : Nat) (x : M F) :
    head' (x.approx (n + 1)) = head' (x.approx (m + 1)) :=
  head_succ' n m _ x.consistent

theorem head_eq_head' : ∀ (x : M F) (n : Nat), head x = head' (x.approx <| n + 1)
  | ⟨_, h⟩, _ => head_succ' _ _ _ h

theorem head'_eq_head : ∀ (x : M F) (n : Nat), head' (x.approx <| n + 1) = head x
  | ⟨_, h⟩, _ => head_succ' _ _ _ h

theorem truncate_approx (x : M F) (n : Nat) : truncate (x.approx <| n + 1) = x.approx n :=
  truncate_eq_of_agree _ _ (x.consistent _)

/-- Unfold an M-type -/
def dest : M F → F (M F)
  | x => ⟨head x, fun i => children x i⟩

namespace Approx

/-- Generates the approximations needed for `M.mk` -/
protected def sMk (x : F (M F)) : ∀ n, CofixA F n
  | 0 => CofixA.continue
  | n + 1 => CofixA.intro x.1 fun i => (x.2 i).approx n

protected theorem P_mk (x : F (M F)) : AllAgree (Approx.sMk x)
  | 0 => by constructor
  | n + 1 => by
    constructor
    intro i
    apply (x.2 i).consistent

end Approx

/-- Constructor for M-types -/
protected def mk (x : F (M F)) : M F where
  approx := Approx.sMk x
  consistent := Approx.P_mk x

@[simp, grind =]
theorem dest_mk (x : F (M F)) : dest (M.mk x) = x := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
theorem mk_dest (x : M F) : M.mk (dest x) = x := by
  ext n
  dsimp only [M.mk]
  induction n with
  | zero => apply Subsingleton.elim
  | succ n =>
      dsimp only [Approx.sMk, dest, head]
      rcases h : x.approx (succ n) with - | ⟨hd, ch⟩
      have h' : hd = head' (x.approx 1) := by
        rw [← head_succ' n, h, head']
        apply x.consistent
      revert ch
      rw [h']
      intro ch h
      congr
      ext a
      dsimp only [children]
      generalize hh : cast _ a = a'' at ⊢
      replace hh : a ≍ a'' := by grind
      revert a''
      rw [h]
      intro _ hh
      cases hh
      rfl

theorem mk_inj {x y : F (M F)} (h : M.mk x = M.mk y) : x = y := by
  rw [← dest_mk x, h, dest_mk]

/-- Destructor for M-types -/
protected def cases {r : M F → Sort w} (f : ∀ x : F (M F), r (M.mk x)) (x : M F) : r x :=
  suffices r (M.mk (dest x)) by
    rw [← mk_dest x]
    exact this
  f _

/-- Destructor for M-types -/
protected def casesOn {r : M F → Sort w} (x : M F) (f : ∀ x : F (M F), r (M.mk x)) : r x :=
  M.cases f x

/-- Destructor for M-types, similar to `casesOn` but also
gives access directly to the root and subtrees of an M-type -/
protected def casesOn' {r : M F → Sort w} (x : M F) (f : ∀ a f, r (M.mk ⟨a, f⟩)) : r x :=
  M.casesOn x (fun ⟨a, g⟩ => f a g)

theorem approx_mk (a : F.A) (f : F.B a → M F) (i : Nat) :
    (M.mk ⟨a, f⟩).approx (i + 1) = CofixA.intro a fun j => (f j).approx i :=
  rfl

theorem corec_def {X : Type _} (f : X → F X) (x₀ : X) :
    M.corec f x₀ = M.mk (F.map (M.corec f) (f x₀)) := by
  apply ext'
  intro n
  cases n with
  | zero => apply @Subsingleton.elim _ CofixA.instSubsingleton
  | succ n =>
    simp only [M.corec, M.mk, Approx.sMk, sCorec, PFunctor.map]
    cases f x₀
    rfl

@[simp, grind =]
theorem head_mk (x : F (M F)) : head (M.mk x) = x.1 :=
  Eq.symm <|
    calc
      x.1 = (dest (M.mk x)).1 := by rw [dest_mk]
      _ = head (M.mk x) := rfl

theorem dest_corec (g : X → F X) (x : X) : M.dest (M.corec g x) = F.map (M.corec g) (g x) := by
  rw [corec_def, dest_mk]

/-!
## Bisimulation Principle
-/

coinductive IsBisim : M F → M F → Prop where
  | step {x y : M F} {a f f'} :
        M.dest x = ⟨a, f⟩ → M.dest y = ⟨a, f'⟩
        → (∀ i, IsBisim (f i) (f' i))
        → IsBisim x y

/-- Bisimulation principle for M-types -/
@[grind .]
theorem bisim (x y : M F) : IsBisim x y → x = y := by
  intro h
  ext n
  induction n generalizing x y
  case zero =>
    apply Subsingleton.elim
  case succ n ih =>
    cases h
    grind [approx_mk, mk_dest]

end M

end PFunctor

end QPFTypes
