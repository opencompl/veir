-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

module

public import CTree.Effect
public import QPFTypes

public section

/-!
Choice Trees (CTrees) are a data structure for representing and reasoning about
nondeterministic programs.
These semantics are represented as a (possibly infinitely deep) tree shallowly embedded in a theorem prover,
with "Vis" nodes for various kinds of runtime effects, and "Tau"/"Br"/"Choice" (name varies) nodes
for (demonic) nondeterministic choices happening.

The first implementation of CTrees is in Rocq (https://doi.org/10.1017/S0956796825100105).
The present implementation makes slightly different design choices in how nondeterminism is handled.
-/

/-! Definitions and monotonicity proofs are partly adapted from the ones in Coinductive and EffectSSA. -/

namespace CTree

open Lean.Order QPFTypes QPF QPFTypes.Unary
open Subeffect (mapEff mapCont)

/--
Type of the unary choice.
It is used to encode ITree-style tau nodes.
-/
inductive C1In : Type u where
| c1

/--
The only case of the unary choice gives a unit result.
ITree-style tau nodes only have a single child.
-/
@[expose]
def C1 (c : C1In.{u}) : Type u :=
  match c with
  | .c1 => PUnit


/-! ## Low-level CTree definitions -/

/--
The basic coinductive functor for CTree, with constructor resp. for leaves (`ret`),
for n-ary nondeterministic choices (`tau`), and for n-ary events/effects (`vis`).
In the `tau` case, the `C1` effect for a unary choice is hardcoded.
-/
@[expose, qpf] def CTreeF {EIn : Type u} (E : EIn → Type u) {CIn : Type u} (C : CIn → Type u)
    (R : Type v) (X : liveParam (Type (max u v))) : Type (max u v) :=
  R ⊕ (Σ i, (C1 ⊕ₑ C) i → X) ⊕ (Σ i, E i → X)

namespace CTreeF

variable {EIn CIn : Type u} {E : EIn → Type u} {C : CIn → Type u} {R : Type v} {X : Type (max u v)}

@[expose, match_pattern] def ret (r : R) : CTreeF E C R X := .inl r
@[expose, match_pattern] def tau (i : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) i → X) : CTreeF E C R X :=
  .inr (.inl ⟨i, k⟩)
@[expose, match_pattern] def vis (i : EIn) (k : E i → X) : CTreeF E C R X :=
  .inr (.inr ⟨i, k⟩)

@[elab_as_elim, cases_eliminator] def cases {motive : CTreeF E C R X → Sort w}
    (ret : ∀ r, motive (.ret r)) (tau : ∀ i k, motive (.tau i k))
    (vis : ∀ i k, motive (.vis i k)) : (t : CTreeF E C R X) → motive t
  | .ret r => ret r
  | .tau i k => tau i k
  | .vis i k => vis i k

end CTreeF

/--
The bottom shape is a unary silent step, so its cofixpoint is the spinning CTree.
-/
instance : HasBot (CTreeF E C R) where
  botShape := .tau (.inl .c1) (fun _ => ⟨⟩)

/--
The high-level CTree datatype
-/
abbrev CTree {EIn : Type u} (E : EIn → Type u) {CIn : Type u} (C : CIn → Type u) (α : Type u) : Type u := Cofix (CTreeF E C α)

/--
A CTree limited to depth n
-/
@[expose, implicit_reducible] def CTreeN {EIn : Type u} (E : EIn → Type u) {CIn : Type u} (C : CIn → Type u) (α : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => CTreeF E C α (CTreeN E C α n)


variable {EIn FIn CIn : Type u} {E : EIn → Type u} {F : FIn → Type u} {C : CIn → Type u} {R R' : Type u} (RR : R → R' → Prop)

/--
Folds the head of a CTree
-/
def CTree.fold (t : CTreeF E C R (CTree E C R)) : CTree E C R := Cofix.mk t

/--
Unfolds the head of a CTree
-/
def CTree.unfold (t : CTree E C R) : CTreeF E C R (CTree E C R) := Cofix.dest t

/-! ## High-level CTree constructors -/

/--
A leaf returning a value
-/
def CTree.ret (r : R) : CTree E C R := CTree.fold (.ret r)

/--
An n-ary choice that generates τ transitions.
This is the general case that covers both the hardcoded `tau1` choice and user-provided `tau` choices.
-/
def CTree.tauG (i : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) i → CTree E C R) : CTree E C R := CTree.fold (.tau i k)

/--
A custom n-ary choice that generates τ transitions
-/
def CTree.tau (i : CIn) (k : C i → CTree E C R) : CTree E C R := CTree.fold (.tau (.inr i) k)

/--
A unary choice that generates a τ transition
-/
def CTree.tau1 (t : CTree E C R) : CTree E C R := CTree.tauG (.inl .c1) λ _ => t

/--
A visible effect
-/
def CTree.vis (i : EIn) (k : E i → CTree E C R) : CTree E C R := CTree.fold (.vis i k)

/--
A CTree triggering the given sub-effect and immediately returning.
-/
def CTree.trigger {SubEIn : Type u} {SubE : SubEIn → Type u} [SubE -< E] (i : SubEIn) : CTree E C (SubE i) :=
  CTree.vis (Subeffect.mapEff SubE E i) (fun x => CTree.ret (Subeffect.mapCont SubE E i x))

/--
A CTree making an n-ary sub-choice and immediately returning
-/
def CTree.choose {SubCIn : Type u} {SubC : SubCIn → Type u} [SubC -< C] (i : SubCIn) : CTree E C (SubC i) :=
  CTree.tau (Subeffect.mapEff SubC C i) (fun x => CTree.ret (Subeffect.mapCont SubC C i x))


/-!
## Basic simp lemmas

Lemmas used in proofs of monotonicity required to use partial_fixpoint
-/

theorem CTree.tau_def {i : CIn} (k : C i → CTree E C R) :
    CTree.tau i k = CTree.tauG (.inr i) k := by rfl

theorem CTree.tau1_def (t : CTree E C R) :
    CTree.tau1 t = CTree.tauG (.inl .c1) (fun _ => t) := by rfl

theorem CTree.choose_def {SubCIn : Type u} {SubC : SubCIn → Type u} [SubC -< C] (i : SubCIn) :
    CTree.choose (E := E) i =
    CTree.tau (Subeffect.mapEff SubC C i) (fun x => CTree.ret (Subeffect.mapCont SubC C i x)) :=
  by rfl

theorem CTree.trigger_def {SubEIn : Type u} {SubE : SubEIn → Type u} [SubE -< E] (i : SubEIn) :
    CTree.trigger (C := C) i =
    CTree.vis (Subeffect.mapEff SubE E i) (fun x => CTree.ret (Subeffect.mapCont SubE E i x)) :=
  by rfl

@[simp, grind =]
theorem CTree.fold_unfold (t : CTree E C R) :
  CTree.fold (CTree.unfold t) = t := by simp [CTree.fold, CTree.unfold]

@[simp, grind =]
theorem CTree.unfold_fold (t : CTreeF E C R _) :
    (fold t).unfold = t := by simp [CTree.fold, CTree.unfold]

/-- Observe the first `n` layers of a tree. -/
def CTree.approx (t : CTree E C R) : (n : Nat) → CTreeN E C R n
  | 0 => ⟨⟩
  | n + 1 => match t.unfold with
    | .ret r => .ret r
    | .tau i k => .tau i (fun c => (k c).approx n)
    | .vis i k => .vis i (fun e => (k e).approx n)

@[simp, grind =]
theorem approx_ret_succ (r : R) n :
  (CTree.ret (E := E) (C := C) r).approx (n + 1) = CTreeF.ret r := by
    simp [CTree.ret, CTree.approx]

@[simp]
theorem approx_fold_ret_succ (r : R) n :
  (CTree.fold (CTreeF.ret (E := E) (C := C) r)).approx (n + 1) = CTreeF.ret r :=
    approx_ret_succ r n

@[simp, grind =]
theorem approx_tau_succ i (k : (C1 ⊕ₑ C) i → CTree E C R) n :
  (CTree.tauG i k).approx (n + 1) = CTreeF.tau i (fun c => (k c).approx n) := by
    simp [CTree.tauG, CTree.approx]

@[simp]
theorem approx_fold_tau_succ i (k : (C1 ⊕ₑ C) i → CTree E C R) n :
  (CTree.fold (CTreeF.tau i k)).approx (n + 1) = CTreeF.tau i (fun c => (k c).approx n) :=
    approx_tau_succ i k n

@[simp, grind =]
theorem approx_vis_succ i (k : E i → CTree E C R) n :
  (CTree.vis i k).approx (n + 1) = CTreeF.vis i (λ e => (k e).approx n) := by
    simp [CTree.vis, CTree.approx]

@[simp]
theorem approx_fold_vis_succ i (t : E i → CTree E C R) n :
  (CTree.fold (CTreeF.vis i t)).approx (n + 1) = CTreeF.vis i (λ o => (t o).approx n) := approx_vis_succ i t n

@[simp, grind =]
theorem unfold_ret (r : R) :
  CTree.unfold (CTree.ret r) = CTreeF.ret (E := E) (C := C) r := by
    simp [CTree.ret]

@[simp, grind =]
theorem unfold_tauG i (k : (C1 ⊕ₑ C) i → CTree E C R) :
  CTree.unfold (CTree.tauG i k) = CTreeF.tau i k := by
    simp [CTree.tauG]

@[simp, grind =]
theorem unfold_tau1 (t : CTree E C R) :
    CTree.unfold (CTree.tau1 t) = CTreeF.tau (.inl .c1) (fun _ => t) := by
  apply unfold_tauG

@[simp, grind =]
theorem unfold_vis i (k : E i → CTree E C R) :
  CTree.unfold (CTree.vis i k) = CTreeF.vis i k := by
    simp [CTree.vis]

@[partial_fixpoint_monotone]
theorem vis_mono α [PartialOrder α] i (f : α → E i → CTree E C R) :
  monotone f →
  monotone (λ x => CTree.vis i (f x)) := by
    intro hf x y hxy
    exact Cofix.mk_map_mono
      (.vis i id) id (fun _ _ h => h) _ _ (hf x y hxy)

@[partial_fixpoint_monotone]
theorem tauG_mono α [PartialOrder α] i (f : α → (C1 ⊕ₑ C) i → CTree E C R) :
  monotone f →
  monotone (λ x => CTree.tauG i (f x)) := by
    intro hf x y hxy
    exact Cofix.mk_map_mono
      (.tau i id) id (fun _ _ h => h) _ _ (hf x y hxy)

@[partial_fixpoint_monotone]
theorem tau_mono α [PartialOrder α] i (f : α → C i → CTree E C R) :
  monotone f →
  monotone (λ x => CTree.tau i (f x)) := by
    simp only [CTree.tau]
    intros h
    apply tauG_mono
    apply h

@[partial_fixpoint_monotone]
theorem tau1_mono α [PartialOrder α] (f : α → CTree E C R) :
  monotone f →
  monotone (λ x => CTree.tau1 (f x)) := by
    simp only [CTree.tau1]
    intros h
    apply tauG_mono
    intros x y h'
    simp only [PartialOrder.rel, SumE.eq_inl]
    intros
    apply h
    apply h'


/--
A single-state CTree that keeps emitting τ
-/
def CTree.spin : CTree E C R := CTree.tau1 spin
partial_fixpoint

private theorem dest_eq_unfold (t : CTree E C R) : Cofix.dest t = t.unfold := rfl

/-- Finite observations determine a tree, by bisimulation. -/
@[ext] theorem CTree.ext (t s : CTree E C R) :
    (∀ n, t.approx n = s.approx n) → t = s := by
  apply Cofix.bisim (fun x y : CTree E C R => ∀ n, x.approx n = y.approx n)
  intro x y h
  -- Depth one fixes the root; depth n+1 compares its children at depth n.
  have hsucc (n : Nat) := h (n + 1)
  simp only [dest_eq_unfold]
  cases hx : CTree.unfold x <;> cases hy : CTree.unfold y <;>
    simp only [CTree.approx, hx, hy] at hsucc <;> cases hsucc 0
  case ret.ret.refl r => exact ⟨CTreeF.ret r, rfl, rfl⟩
  all_goals
    simp only [CTreeN, CTreeF, CTreeF.tau, CTreeF.vis, Sum.inr.injEq, Sum.inl.injEq, Sigma.mk.injEq,
      heq_eq_eq, true_and] at hsucc
  case tau.tau.refl i k l =>
    exact ⟨CTreeF.tau i (fun o => ⟨(k o, l o), fun n => congrFun (hsucc n) o⟩), rfl, rfl⟩
  case vis.vis.refl i k l =>
    exact ⟨CTreeF.vis i (fun o => ⟨(k o, l o), fun n => congrFun (hsucc n) o⟩), rfl, rfl⟩

@[simp] theorem CTree.bot_eq :
    Cofix.bot (@TypeFun.ofCurried 1 (CTreeF E C R)) = (CTree.spin : CTree E C R) := by
  have hb : CTree.unfold (Cofix.bot (@TypeFun.ofCurried 1 (CTreeF E C R))) =
      CTreeF.tau (.inl .c1) (fun _ => Cofix.bot (@TypeFun.ofCurried 1 (CTreeF E C R))) := by
    unfold CTree.unfold Cofix.bot
    rw [Cofix.dest_abs, MvPFunctor.M.dest_bot, QPF.abs_map]
    erw [QPF.abs_repr]
    rfl
  apply CTree.ext
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [CTree.spin.eq_def, CTree.tau1_def, approx_tau_succ]
    simp only [CTree.approx, hb, ih]

/-- For a unary polynomial functor, a non-bottom order step is precisely a
layer whose corresponding children satisfy the relation. -/
private theorem leStep_iff_liftR {F : TypeVec.{u} 1 → Type u} [QPF F] [IsPolynomial F]
    [HasBot F TypeVec.nil] (p : Cofix F TypeVec.nil → Cofix F TypeVec.nil → Prop) (x y) :
    Cofix.LeStep p x y ↔ x = Cofix.bot F ∨
      MvFunctor.LiftR (TypeVec.RelLast TypeVec.nil p) (Cofix.dest x) (Cofix.dest y) := by
  unfold Cofix.LeStep
  rw [QPF.liftR_iff]
  apply or_congr_right
  constructor
  · rintro ⟨a, fd, g, g', hx, hy, h⟩
    refine ⟨a, _, _, (QPF.abs_repr _).symm.trans (congrArg QPF.abs hx),
      (QPF.abs_repr _).symm.trans (congrArg QPF.abs hy), ?_⟩
    intro i; obtain rfl : i = 0 := Fin.ext (by omega)
    exact h
  · rintro ⟨a, f, g, hx, hy, h⟩
    refine ⟨a, TypeVec.nilFun, TypeVec.lastFun f, TypeVec.lastFun g, ?_, ?_, h 0⟩
    all_goals
      first | erw [hx, IsPolynomial.repr_abs] | erw [hy, IsPolynomial.repr_abs]
      apply congrArg _
      exact (TypeVec.split_dropFun_lastFun _).symm.trans
        (congrArg (fun fd => TypeVec.splitFun fd _) (TypeVec.eq_nilFun _))

private theorem leStep_iff (p : CTree E C R → CTree E C R → Prop) (t1 t2 : CTree E C R) :
    Cofix.LeStep p t1 t2 ↔
    t1 = .spin ∨
    (∃ r, t1 = .ret r ∧ t2 = .ret r) ∨
    (∃ i t1' t2', t1 = .tauG i t1' ∧ t2 = .tauG i t2' ∧ ∀ o, p (t1' o) (t2' o)) ∨
    (∃ i t1' t2', t1 = .vis i t1' ∧ t2 = .vis i t2' ∧ ∀ o, p (t1' o) (t2' o)) := by
  rw [leStep_iff_liftR, CTree.bot_eq]
  apply or_congr_right
  constructor
  · rintro ⟨w, hx, hy⟩
    rw [dest_eq_unfold] at hx hy
    have hx := (CTree.fold_unfold t1).symm.trans (congrArg CTree.fold hx.symm)
    have hy := (CTree.fold_unfold t2).symm.trans (congrArg CTree.fold hy.symm)
    cases w using CTreeF.cases with
    | ret r => exact Or.inl ⟨r, hx, hy⟩
    | tau i k => exact Or.inr (Or.inl ⟨i, _, _, hx, hy, fun o => (k o).property⟩)
    | vis i k => exact Or.inr (Or.inr ⟨i, _, _, hx, hy, fun o => (k o).property⟩)
  · rintro (⟨r, rfl, rfl⟩ | ⟨i, k, k', rfl, rfl, hk⟩ | ⟨i, k, k', rfl, rfl, hk⟩)
    · exact ⟨CTreeF.ret r, (unfold_ret r).symm, (unfold_ret r).symm⟩
    · exact ⟨CTreeF.tau i (fun o => ⟨(k o, k' o), hk o⟩), (unfold_tauG i k).symm,
        (unfold_tauG i k').symm⟩
    · exact ⟨CTreeF.vis i (fun o => ⟨(k o, k' o), hk o⟩), (unfold_vis i k).symm,
        (unfold_vis i k').symm⟩

theorem CTree.le_unfold (t1 t2 : CTree E C R) :
  (t1 ⊑ t2) = (t1 = .spin ∨
    (∃ r, t1 = .ret r ∧ t2 = .ret r) ∨
    (∃ i t1' t2', t1 = .tauG i t1' ∧ t2 = .tauG i t2' ∧ ∀ o, t1' o ⊑ t2' o) ∨
    (∃ i t1' t2', t1 = .vis i t1' ∧ t2 = .vis i t2' ∧ ∀ o, t1' o ⊑ t2' o)) := by
  apply propext
  constructor
  · exact fun h => (leStep_iff _ _ _).mp (Cofix.le_step h)
  · rintro (rfl | ⟨_, rfl, rfl⟩ | ⟨i, k, k', rfl, rfl, hk⟩ | ⟨i, k, k', rfl, rfl, hk⟩)
    · rw [← CTree.bot_eq]; apply Cofix.bot_le
    · apply PartialOrder.rel_refl
    · exact tauG_mono _ i id (fun _ _ h => h) _ _ hk
    · exact vis_mono _ i id (fun _ _ h => h) _ _ hk

/--
The monadic bind operator, that sequences a CTree and a continuation
-/
def bind (t : CTree E C X) (k : X → CTree E C Y) : CTree E C Y :=
  match t.unfold with
  | .ret r => k r
  | .tau i k' => .tauG i (fun x => CTree.bind (k' x) k)
  | .vis i k' => .vis i (fun x => CTree.bind (k' x) k)
partial_fixpoint

@[simp, grind =]
theorem CTree.bind_ret {β} r (t : β → CTree E C α) :
  CTree.bind (.ret r) t = t r := by
    rw [CTree.bind, unfold_ret]

@[simp, grind =]
theorem CTree.bind_vis {β} i k (t : β → CTree E C α) :
  CTree.bind (.vis i k) t = .vis i (λ o => CTree.bind (k o) t) := by
    rw [CTree.bind, unfold_vis]

@[simp, grind =]
theorem CTree.bind_tau {β} c k (t : β → CTree E C α) :
  CTree.bind (.tauG c k) t = .tauG c (λ o => CTree.bind (k o) t) := by
    rw [CTree.bind, unfold_tauG]

instance : Monad (CTree E C) where
  pure := CTree.ret
  bind := CTree.bind

@[simp, grind =]
theorem bind_pure (value : α) (next : α → CTree E C β) :
    CTree.bind (pure value) next = next value :=
  CTree.bind_ret value next

@[simp] theorem CTree.bind_spin (k : X → CTree E C Y) :
    CTree.bind CTree.spin k = CTree.spin := by
  apply CTree.ext
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    conv => lhs; rw [CTree.spin.eq_def, CTree.tau1_def, CTree.bind_tau, approx_tau_succ]
    conv => rhs; rw [CTree.spin.eq_def, CTree.tau1_def, approx_tau_succ]
    simp only [ih]

@[partial_fixpoint_monotone]
theorem bind_mono {γ} [PartialOrder γ]
  (f : γ → CTree E C X) (g : γ → X → CTree E C Y) :
  monotone f →
  monotone g →
  monotone (λ x => CTree.bind (f x) (g x)) := by
  intro hf hg x y hxy
  -- A return hands control to already-ordered continuations. At a branch or
  -- event, the children are again binds of ordered input trees.
  let p (a b : CTree E C Y) := a ⊑ b ∨
    ∃ t s : CTree E C X, t ⊑ s ∧ a = CTree.bind t (g x) ∧ b = CTree.bind s (g y)
  have known (a b : CTree E C Y) (h : a ⊑ b) : Cofix.LeStep p a b := by
    rcases Cofix.le_step h with hb | ⟨i, fd, k, k', ha, hb, hk⟩
    · exact Or.inl hb
    · exact Or.inr ⟨i, fd, k, k', ha, hb, fun o => Or.inl (hk o)⟩
  refine Cofix.le_coinduct p ?_ (Or.inr ⟨_, _, hf _ _ hxy, rfl, rfl⟩)
  rintro a b (hab | ⟨t, s, hts, rfl, rfl⟩)
  · exact known _ _ hab
  rw [CTree.le_unfold] at hts
  rcases hts with rfl | ⟨r, rfl, rfl⟩ | ⟨i, k, k', rfl, rfl, hk⟩ | ⟨i, k, k', rfl, rfl, hk⟩
  · rw [CTree.bind_spin]
    exact Or.inl CTree.bot_eq.symm
  · simp only [CTree.bind_ret]; exact known _ _ (hg _ _ hxy r)
  · simp only [CTree.bind_tau]
    apply (leStep_iff _ _ _).mpr
    exact Or.inr (Or.inr (Or.inl ⟨i, _, _, rfl, rfl, fun o => Or.inr ⟨_, _, hk o, rfl, rfl⟩⟩))
  · simp only [CTree.bind_vis]
    apply (leStep_iff _ _ _).mpr
    exact Or.inr (Or.inr (Or.inr ⟨i, _, _, rfl, rfl, fun o => Or.inr ⟨_, _, hk o, rfl, rfl⟩⟩))

instance : MonoBind (CTree E C) where
  bind_mono_left := by
    intro _ _ _ _ _ _
    dsimp only [Bind.bind]
    apply bind_mono (λ x => x) <;> grind [monotone]
  bind_mono_right := by
    intro _ _ a _ _ _
    dsimp only [Bind.bind]
    apply bind_mono (λ x => a) (λ x => x)
    · grind [monotone]
    · grind [monotone]
    · intro _; grind

@[elab_as_elim, cases_eliminator]
def CTree.cases {motive : CTree E C X → Sort v}
    (ret : ∀ r, motive (pure r))
    (tau : ∀ c k, motive (CTree.tauG c k))
    (vis : ∀ e k, motive (CTree.vis e k))
    (t : CTree E C X) : motive t := by
    rw [<-CTree.fold_unfold t]
    cases t.unfold
    · apply ret
    · apply tau
    · apply vis

@[simp, grind =]
theorem unfold_pure (r : R) :
  CTree.unfold (pure r) = CTreeF.ret (E := E) (C := C) r := by
    simp [pure]

@[simp]
theorem approx_pure_succ (r : α) n :
  (pure r : CTree _ _ _).approx (n + 1) = CTreeF.ret (E := E) (C := C) r := by
    simp [pure]

@[simp, grind =]
theorem id_map : ∀ (x : CTree E C R), id <$> x = x := by
  simp only [Functor.map, Function.comp_id]
  intro t
  ext n
  induction n generalizing t; congr 0
  unfold CTree.bind
  cases t <;> simp [*]

theorem bind_assoc : ∀ {α β γ} (x : CTree E C α) (f : α → CTree E C β) (g : β → CTree E C γ),
    x >>= f >>= g = x >>= fun x => f x >>= g := by
  simp only [Bind.bind]
  intro _ _ _ t1 t2 t3
  ext n
  induction n generalizing t1; congr 0
  rw [CTree.bind.eq_def t1]
  rw [CTree.bind.eq_def t1]
  split <;> simp [*]

instance : LawfulMonad (CTree E C) := LawfulMonad.mk' (CTree E C)
  (id_map := id_map)
  (pure_bind := by simp [pure, Bind.bind])
  (bind_assoc := bind_assoc)

instance : MonoBind (CTree E C) where
  bind_mono_left := by
    intros
    rw [Bind.bind]
    apply bind_mono (λ x => x) <;> grind [monotone]
  bind_mono_right := by
    intro _ _ a _ _ _
    rw [Bind.bind]
    apply bind_mono (λ x => a) (λ x => x)
    · grind [monotone]
    · grind [monotone]
    · intro _; grind

@[simp, grind =]
theorem CTree.ret_pure (r : R) : CTree.ret (E := E) (C := C) r = pure r := by
  rfl

@[simp, grind =]
theorem bind_tau {α β} c k (t : β → CTree E C α) :
  (.tauG c k) >>= t = .tauG c (λ x => k x >>= t) := by simp [Bind.bind]

@[simp, grind =]
theorem bind_vis {α β} i k (t : β → CTree E C α) :
  (.vis i k) >>= t = .vis i (λ o => k o >>= t) := by simp [Bind.bind]

end CTree
