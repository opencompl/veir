-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

module

public import Coinductive
public import CTree.Effect

public section

/-!
Choice Trees (CTrees) are a data structure for representing and reasoning about
nondeterministic programs.
These semantics are represented as a (possibly infinitely deep) tree shallowly embedded in a theorem prover,
with "Vis" nodes for various kinds of runtime effects, and "Tau"/"Br"/"Choice" (name varies) nodes
for (demonic) nondeterministic choices happening.

The first implementation of CTrees is in Rocq (https://doi.org/10.1017/S0956796825100105).
the present implementation makes slightly different design choices in how nondeterminism is handled.
-/

/-! Definitions and monotonicity proofs are partly adapted from the ones in Coinductive and EffectSSA. -/

namespace CTree

open Coinductive Lean.Order
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

-- TODO is universe w needed?
/--
The basic coinductive functor for CTree, with constructor resp. for leaves (`ret`),
for n-ary nondeterministic choices (`tau`), and for n-ary events/effects (`vis`).
In the `tau` case, the `C1` effect for a unary choice is hardcoded.
-/
inductive CTreeF {EIn : Type u} (E : EIn → Type u) {CIn : Type u} (C : CIn → Type u)
    (R : Type v) (CTree : Type w) : Type (max u v w) where
  | ret (r : R)
  | tau (i : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) i → CTree)
  | vis (i : EIn) (k : E i → CTree)

/--
The coinductive library defines the bottom element as the cofixpoint of the provided inhabitant of the functor applied to unit.
Here, the bottom element is thus defined as the spinning CTree.
-/
instance {EIn : Type u} {E : EIn → Type u} {CIn : Type u} {C : CIn → Type u} {α : Type u} : Inhabited (CTreeF E C α PUnit) where
  default := .tau (.inl .c1) (fun _ => ⟨⟩)

/--
Auxiliary definition to encode CTree as a polynomial functor
-/
inductive CTreeF.In {EIn : Type u} (E : EIn → Type u) {CIn : Type u} (C : CIn → Type u) (α : Type u) : Type u where
  | ret (r : α)
  | tau (i : C1In ⊕ CIn)
  | vis (i : EIn)

/--
CTree as a polynomial functor
-/
instance {EIn : Type u} (E : EIn → Type u) {CIn : Type u} (C : CIn → Type u) (α : Type u) : PF (CTreeF E C α) where
  P := ⟨CTreeF.In E C α, fun
    | .ret _ => PEmpty
    | .tau i => (C1 ⊕ₑ C) i
    | .vis i => E i⟩
  unpack
    | .ret r => .obj (.ret r) nofun
    | .tau i k => .obj (.tau i) k
    | .vis i k => .obj (.vis i) k
  pack
    | .obj (.ret r) _ => .ret r
    | .obj (.tau i) k => .tau i k
    | .obj (.vis i) k => .vis i k
  unpack_pack := by rintro _ ⟨⟩ <;> simp
  pack_unpack := by rintro _ (⟨⟨⟩, _⟩ | ⟨⟨⟩⟩) <;> simp <;> funext x <;> cases x

/--
The high-level CTree datatype
-/
abbrev CTree {EIn : Type u} (E : EIn → Type u) {CIn : Type u} (C : CIn → Type u) (α : Type u) : Type u := CoInd (CTreeF E C α)

/--
A CTree limited to depth n
-/
abbrev CTreeN {EIn : Type u} (E : EIn → Type u) {CIn : Type u} (C : CIn → Type u) (α : Type u) (n : Nat) : Type u := CoIndN (CTreeF E C α) n


variable {EIn FIn CIn : Type u} {E : EIn → Type u} {F : FIn → Type u} {C : CIn → Type u} {R R' : Type u} (RR : R → R' → Prop)

/--
Folds the head of a CTree
-/
def CTree.fold (t : CTreeF E C R (CTree E C R)) : CTree E C R := CoInd.fold _ t

/--
Unfolds the head of a CTree
-/
def CTree.unfold (t : CTree E C R) : CTreeF E C R (CTree E C R) := CoInd.unfold _ t

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

@[simp, grind =]
theorem CTree.fold_unfold (t : CTree E C R) :
  CTree.fold (CTree.unfold t) = t := by simp [CTree.fold, CTree.unfold]

@[simp, grind =]
theorem CTree.unfold_fold (t : CTreeF E C R _) :
    (fold t).unfold = t := by simp [CTree.fold, CTree.unfold]

@[simp, grind =]
theorem approx_ret_succ (r : R) n :
  (CTree.ret (E := E) (C := C) r).approx (n + 1) = CTreeF.ret r := by
    simp [CTree.ret, CTree.fold, CoInd.fold, PF.map, PF.pack, PF.unpack]

@[simp]
theorem approx_fold_ret_succ (r : R) n :
  (CTree.fold (CTreeF.ret (E := E) (C := C) r)).approx (n + 1) = CTreeF.ret r :=
    approx_ret_succ r n

@[simp, grind =]
theorem approx_tau_succ i (k : (C1 ⊕ₑ C) i → CTree E C R) n :
  (CTree.tauG i k).approx (n + 1) = CTreeF.tau i (fun c => (k c).approx n) := by
    simp only [CTree.tauG, CTree.fold, CoInd.fold, PF.map, PF.pack, PF.unpack]
    rfl

@[simp]
theorem approx_fold_tau_succ i (k : (C1 ⊕ₑ C) i → CTree E C R) n :
  (CTree.fold (CTreeF.tau i k)).approx (n + 1) = CTreeF.tau i (fun c => (k c).approx n) :=
    approx_tau_succ i k n

@[simp, grind =]
theorem approx_vis_succ i (k : E i → CTree E C R) n :
  (CTree.vis i k).approx (n + 1) = CTreeF.vis i (λ e => (k e).approx n) := by
    simp only [CTree.vis, CTree.fold, CoInd.fold, PF.map, PF.pack]
    rfl

@[simp]
theorem approx_fold_vis_succ i (t : E i → CTree E C R) n :
  (CTree.fold (CTreeF.vis i t)).approx (n + 1) = CTreeF.vis i (λ o => (t o).approx n) := approx_vis_succ i t n

@[simp]
theorem unfold_ret (r : R) :
  CTree.unfold (CTree.ret r) = CTreeF.ret (E := E) (C := C) r := by
    simp [CTree.ret, CTree.fold, CTree.unfold]

@[simp]
theorem unfold_tauG i (k : (C1 ⊕ₑ C) i → CTree E C R) :
  CTree.unfold (CTree.tauG i k) = CTreeF.tau i k := by
    simp [CTree.tauG, CTree.fold, CTree.unfold]

@[simp]
theorem unfold_tau1 (t : CTree E C R) :
    CTree.unfold (CTree.tau1 t) = CTreeF.tau (.inl .c1) (fun _ => t) := by
  apply unfold_tauG

@[simp]
theorem unfold_vis i (k : E i → CTree E C R) :
  CTree.unfold (CTree.vis i k) = CTreeF.vis i k := by
    simp [CTree.vis, CTree.fold, CTree.unfold]

theorem vis_monoN (i : EIn) (t1 t2 : E i → CTree E C R) n :
  (∀ o, CoIndN.le _ ((t1 o).approx n) ((t2 o).approx n)) →
  CoIndN.le _ ((CTree.vis i t1).approx (n + 1)) ((CTree.vis i t2).approx (n + 1))
 := by
    intro hs
    simp only [approx_vis_succ, CoIndN.le, PF.unpack]
    right
    constructor <;> try rfl
    grind [coherent1]

@[partial_fixpoint_monotone]
theorem vis_mono α [PartialOrder α] i (f : α → E i → CTree E C R) :
  monotone f →
  monotone (λ x => CTree.vis i (f x)) := by
    intro hf t1 t2 hle
    apply CoInd.le_leN
    rintro ⟨n⟩; simp only [CoIndN.le]
    apply vis_monoN
    intro o
    have := hf t1 t2 hle o
    grind [CoInd.leN_le]

@[simp]
theorem tauG_monoN (i : C1In ⊕ CIn) (t1 t2 : (C1 ⊕ₑ C) i → CTree E C R) n :
  (∀ o, CoIndN.le _ ((t1 o).approx n) ((t2 o).approx n)) →
  CoIndN.le _ ((CTree.tauG i t1).approx (n + 1)) ((CTree.tauG i t2).approx (n + 1))
 := by
    intro hs
    simp only [approx_tau_succ, CoIndN.le, PF.unpack]
    right
    constructor <;> try rfl
    grind [coherent1]

@[partial_fixpoint_monotone]
theorem tauG_mono α [PartialOrder α] i (f : α → (C1 ⊕ₑ C) i → CTree E C R) :
  monotone f →
  monotone (λ x => CTree.tauG i (f x)) := by
    intro hf t1 t2 hle
    apply CoInd.le_leN
    rintro ⟨n⟩; simp only [CoIndN.le]
    apply tauG_monoN
    intro o
    have := hf t1 t2 hle o
    grind [CoInd.leN_le]

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

@[simp]
theorem CTree.bot_eq :
  CoInd.bot (CTreeF E C R) = CTree.spin := by
    ext n
    induction n; congr 0
    rw [CoInd.bot_eq, spin]
    simp [PF.map, PF.pack, CoInd.fold, *, PF.unpack, default, tau1]
    rfl

theorem CTree.le_unfold (t1 t2 : CTree E C R) :
  (t1 ⊑ t2) = (t1 = .spin ∨
    (∃ r, t1 = .ret r ∧ t2 = .ret r) ∨
    (∃ i t1' t2', t1 = .tauG i t1' ∧ t2 = .tauG i t2' ∧ ∀ o, t1' o ⊑ t2' o) ∨
    (∃ i t1' t2', t1 = .vis i t1' ∧ t2 = .vis i t2' ∧ ∀ o, t1' o ⊑ t2' o)) := by
    ext
    constructor
    · intro h
      rw [CoInd.le_unfold] at h
      rcases h with (rfl|⟨i, _, _, _, _, h1, h2⟩); simp only [bot_eq, exists_and_left, true_or]
      rw [<-Coinductive.unfold_fold _ t1, <-Coinductive.unfold_fold _ t2]
      rw [<-PF.unpack_pack (CoInd.unfold _ t1), <-PF.unpack_pack (CoInd.unfold _ t2)]
      simp only [h1, h2]
      right
      cases i <;> simp only [PF.pack, ret, fold, and_self, tauG, exists_and_left, vis] <;> grind
    · rintro (rfl| ⟨_, rfl, rfl⟩ | ⟨_, _, _, rfl, rfl, _⟩|⟨_, _, _, rfl, rfl, _⟩)
      · simp [CoInd.le_unfold]
      · apply PartialOrder.rel_refl
      · simp only [CoInd.le_unfold]
        right
        simp only [PF.unpack, tauG, fold, Coinductive.fold_unfold]
        constructor <;> try rfl
        grind
      · simp only [CoInd.le_unfold]
        right
        simp only [PF.unpack, vis, fold, Coinductive.fold_unfold]
        constructor <;> try rfl
        grind

/--
The monadic bind operator, that sequences a CTree and a continuation
-/
def bind (t : CTree E C X) (k : X → CTree E C Y) : CTree E C Y :=
  match t.unfold with
  | .ret r => k r
  | .tau i k' => .tauG i (fun x => CTree.bind (k' x) k)
  | .vis i k' => .vis i (fun x => CTree.bind (k' x) k)
partial_fixpoint

@[simp]
theorem CTree.bind_ret {β} r (t : β → CTree E C α) :
  CTree.bind (.ret r) t = t r := by
    rw [CTree.bind]
    simp [CTree.ret, CTree.fold, CTree.unfold]

@[simp]
theorem CTree.bind_vis {β} i k (t : β → CTree E C α) :
  CTree.bind (.vis i k) t = .vis i (λ o => CTree.bind (k o) t) := by
    rw [CTree.bind]
    simp [CTree.vis, CTree.fold, CTree.unfold]

@[simp]
theorem CTree.bind_tau {β} c k (t : β → CTree E C α) :
  CTree.bind (.tauG c k) t = .tauG c (λ o => CTree.bind (k o) t) := by
    rw [CTree.bind]
    simp [CTree.tauG, CTree.fold, CTree.unfold]

instance : Monad (CTree E C) where
  pure := CTree.ret
  bind := CTree.bind

@[partial_fixpoint_monotone]
theorem bind_mono {γ} [PartialOrder γ]
  (f : γ → CTree E C X) (g : γ → X → CTree E C Y) :
  monotone f →
  monotone g →
  monotone (λ x => CTree.bind (f x) (g x)) := by
    intro hf hg t1 t2 hle
    apply CoInd.le_leN
    intro n
    dsimp only
    have hlef : (f t1) ⊑ (f t2) := by apply hf; assumption
    generalize f t1 = t1, f t2 = t2 at hlef
    induction n generalizing t1 t2; simp only [CoIndN.le]
    unfold CTree.bind
    rw [CTree.le_unfold] at hlef
    rcases hlef with (rfl|⟨x, rfl, rfl⟩|⟨_, _, _, rfl, rfl, _⟩|⟨_, _, _, rfl, rfl, _⟩)
    · unfold CTree.spin
      simp only [unfold_tau1, SumE.eq_inl, approx_tau_succ, CoIndN.le, CoIndN.bot, CTree.bot_eq]
      left
      unfold CTree.spin CTree.tau1
      simp only [SumE.eq_inl, approx_tau_succ]
      congr
      funext
      congr
      ext n
      induction n; congr 0
      unfold CTree.bind CTree.spin CTree.tau1
      simp_all
    · rw [unfold_ret]
      have := hg t1 t2 hle x
      grind [CoInd.leN_le, monotone]
    · simp only [unfold_tauG, approx_tau_succ]
      apply tauG_monoN
      grind [CoInd.leN_le, monotone]
    · simp only [unfold_vis, approx_vis_succ]
      apply vis_monoN
      grind [CoInd.leN_le, monotone]

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

@[simp]
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

