-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception AND BSD-3-Clause

-- definitions and monotonicity proofs partly adapted from the ones in Coinductive and EffectSSA

module

public import Coinductive
public import CTree.Effect

@[expose] public section

namespace CTree
open Coinductive Lean.Order


inductive E1In : Type u where
| e1

def E1 (e : E1In.{u}) : Type u :=
  match e with
  | .e1 => PUnit

inductive CTreeF {EIn : Type u} (E : EIn → Type u) {CIn : Type u'} (C : CIn → Type u')
    (R : Type v) (CTree : Type w) : Type (max u u' v w) where
  | ret (r : R)
  | tau (i : E1In ⊕ CIn) (k : (E1 ⊕ₑ C) i → CTree)
  | vis (i : EIn) (k : E i → CTree)

open Subeffect (mapEff mapCont)

instance {ι : Type u} {ε : ι → Type u} {κ : Type u} {σ : κ → Type u} {α : Type u} : Inhabited (CTreeF ε σ α PUnit) where
  default := .tau (.inl .e1) (fun _ => ⟨⟩)

inductive CTreeF.In {ι : Type u} (ε : ι → Type u) {κ : Type u} (σ : κ → Type u) (α : Type u) : Type u where
  | ret (r : α)
  | tau (i : E1In ⊕ κ)
  | vis (i : ι)

instance {ι : Type u} (ε : ι → Type u) {κ : Type u} (σ : κ → Type u) (α : Type u) : PF (CTreeF ε σ α) where
  P := ⟨CTreeF.In ε σ α, fun
    | .ret _ => PEmpty
    | .tau i => (E1 ⊕ₑ σ) i
    | .vis i => ε i⟩
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

abbrev CTree {ι : Type u} (ε : ι → Type u) {κ : Type u} (σ : κ → Type u) (α : Type u) : Type u := CoInd (CTreeF ε σ α)
abbrev CTreeN {ι : Type u} (ε : ι → Type u) {κ : Type u} (σ : κ → Type u) (α : Type u) (n : Nat) : Type u := CoIndN (CTreeF ε σ α) n


-- FIXME C'/D
variable {EIn FIn CIn C'In DIn : Type u} {E : EIn → Type u} {F : FIn → Type u} {C : CIn → Type u} {C' : C'In → Type u} {D : DIn → Type u} {R R' : Type u} (RR : R → R' → Prop)

def CTree.fold (t : CTreeF E C R (CTree E C R)) : CTree E C R := CoInd.fold _ t
def CTree.ret (r : R) : CTree E C R := CTree.fold (.ret r)
def CTree.tauG (i : E1In ⊕ CIn) (k : (E1 ⊕ₑ C) i → CTree E C R) : CTree E C R := CTree.fold (.tau i k)
def CTree.tau (i : CIn) (k : C i → CTree E C R) : CTree E C R := CTree.fold (.tau (.inr i) k)
def CTree.tau1 (t : CTree E C R) : CTree E C R := CTree.tauG (.inl .e1) λ _ => t
def CTree.vis (i : EIn) (k : E i → CTree E C R) : CTree E C R := CTree.fold (.vis i k)
def CTree.unfold (t : CTree E C R) : CTreeF E C R (CTree E C R) := CoInd.unfold _ t

def CTree.trigger (i : EIn) : CTree E C (E i) := CTree.vis i (fun x => CTree.ret x)
def CTree.choose (i : CIn) : CTree E C (C i) := CTree.tau i (fun x => CTree.ret x)

@[simp]
theorem CTree.unfold_fold (t : CTree E C R) :
  CTree.fold (CTree.unfold t) = t := by simp [CTree.fold, CTree.unfold]

@[simp]
theorem ret_approx_1 (r : R) n :
  (CTree.ret (E := E) (C := C) r).approx (n + 1) = CTreeF.ret r := by
    simp [CTree.ret, CTree.fold, CoInd.fold, PF.map, PF.pack, PF.unpack]

@[simp]
theorem fold_ret_approx_1 (r : R) n :
  (CTree.fold (CTreeF.ret (E := E) (C := C) r)).approx (n + 1) = CTreeF.ret r :=
    ret_approx_1 r n

@[simp]
theorem tau_approx_1 i (k : (E1 ⊕ₑ C) i → CTree E C R) n :
  (CTree.tauG i k).approx (n + 1) = CTreeF.tau i (fun c => (k c).approx n) := by
    simp [CTree.tauG, CTree.fold, CoInd.fold, PF.map, PF.pack, PF.unpack]
    rfl

@[simp]
theorem fold_tau_approx_1 i (k : (E1 ⊕ₑ C) i → CTree E C R) n :
  (CTree.fold (CTreeF.tau i k)).approx (n + 1) = CTreeF.tau i (fun c => (k c).approx n) :=
    tau_approx_1 i k n

@[simp]
theorem vis_approx_1 i (k : E i → CTree E C R) n :
  (CTree.vis i k).approx (n + 1) = CTreeF.vis i (λ e => (k e).approx n) := by
    simp [CTree.vis, CTree.fold, CoInd.fold, PF.map, PF.pack]
    rfl

@[simp]
theorem fold_vis_approx_1 i (t : E i → CTree E C R) n :
  (CTree.fold (CTreeF.vis i t)).approx (n + 1) = CTreeF.vis i (λ o => (t o).approx n) := vis_approx_1 i t n

@[simp]
theorem unfold_ret (r : R) :
  CTree.unfold (CTree.ret r) = CTreeF.ret (E := E) (C := C) r := by
    simp [CTree.ret, CTree.fold, CTree.unfold]

@[simp]
theorem unfold_tauG i (k : (E1 ⊕ₑ C) i → CTree E C R) :
  CTree.unfold (CTree.tauG i k) = CTreeF.tau i k := by
    simp [CTree.tauG, CTree.fold, CTree.unfold]

@[simp]
theorem unfold_tau1 (t : CTree E C R) :
    CTree.unfold (CTree.tau1 t) = CTreeF.tau (.inl .e1) (fun _ => t) := by
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
    simp [CoIndN.le, PF.unpack]
    right
    constructor <;> try rfl
    grind [coherent1]

@[partial_fixpoint_monotone]
theorem vis_mono α [PartialOrder α] i (f : α → E i → CTree E C R) :
  monotone f →
  monotone (λ x => CTree.vis i (f x)) := by
    intro hf t1 t2 hle
    apply CoInd.le_leN
    rintro ⟨n⟩; simp [CoIndN.le]
    apply vis_monoN
    intro o
    have := hf t1 t2 hle o
    grind [CoInd.leN_le]

@[simp]
theorem tauG_monoN (i : E1In ⊕ CIn) (t1 t2 : (E1 ⊕ₑ C) i → CTree E C R) n :
  (∀ o, CoIndN.le _ ((t1 o).approx n) ((t2 o).approx n)) →
  CoIndN.le _ ((CTree.tauG i t1).approx (n + 1)) ((CTree.tauG i t2).approx (n + 1))
 := by
    intro hs
    simp [CoIndN.le, PF.unpack]
    right
    constructor <;> try rfl
    grind [coherent1]

@[partial_fixpoint_monotone]
theorem tauG_mono α [PartialOrder α] i (f : α → (E1 ⊕ₑ C) i → CTree E C R) :
  monotone f →
  monotone (λ x => CTree.tauG i (f x)) := by
    intro hf t1 t2 hle
    apply CoInd.le_leN
    rintro ⟨n⟩; simp [CoIndN.le]
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
    simp [monotone]
    intros x y h'
    simp [PartialOrder.rel]
    intros
    apply h
    apply h'

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
      rcases h with (rfl|⟨i, _, _, _, _, h1, h2⟩); simp
      rw [<-Coinductive.unfold_fold _ t1, <-Coinductive.unfold_fold _ t2]
      rw [<-PF.unpack_pack (CoInd.unfold _ t1), <-PF.unpack_pack (CoInd.unfold _ t2)]
      simp only [h1, h2]
      right
      cases i <;> simp [PF.pack, ret, tauG, vis, fold]
      · grind
      · grind
      · right
        right
        exists ?_, ?_; rotate_left 1
        constructor; rfl
        apply Exists.intro
        constructor; rfl
        simp_all
    · rintro (rfl| ⟨_, rfl, rfl⟩ | ⟨_, _, _, rfl, rfl, _⟩|⟨_, _, _, rfl, rfl, _⟩)
      · simp [CoInd.le_unfold]
      · apply PartialOrder.rel_refl
      · simp [CoInd.le_unfold]
        right
        simp [PF.unpack, CTree.tauG, CTree.fold]
        constructor <;> try rfl
        grind
      · simp [CoInd.le_unfold]
        right
        simp [PF.unpack, CTree.vis, CTree.fold]
        constructor <;> try rfl
        grind

def bind (t : CTree E C X) (k : X → CTree E C Y) : CTree E C Y :=
  match t.unfold with
  | .ret r => k r
  | .tau i k' => .tauG i (fun x => CTree.bind (k' x) k)
  | .vis i k' => .vis i (fun x => CTree.bind (k' x) k)
partial_fixpoint

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
    induction n generalizing t1 t2; simp [CoIndN.le]
    unfold CTree.bind
    rw [CTree.le_unfold] at hlef
    rcases hlef with (rfl|⟨_, rfl, rfl⟩|⟨_, _, _, rfl, rfl, _⟩|⟨_, _, _, rfl, rfl, _⟩)
    · unfold CTree.spin
      simp [CoIndN.le, CoIndN.bot]
      left
      unfold CTree.spin CTree.tau1
      simp
      congr
      funext
      congr
      ext n
      induction n; congr 0
      unfold CTree.bind CTree.spin CTree.tau1
      simp_all
    · rename_i x
      simp
      have := hg t1 t2 hle x
      grind [CoInd.leN_le, monotone]
    · simp
      apply tauG_monoN
      grind [CoInd.leN_le, monotone]
    · simp
      apply vis_monoN
      grind [CoInd.leN_le, monotone]

instance : MonoBind (CTree E C) where
  bind_mono_left := by
    intro _ _ _ _ _ _
    dsimp [Bind.bind]
    apply bind_mono (λ x => x) <;> grind [monotone, PartialOrder.rel_refl]
  bind_mono_right := by
    intro _ _ a _ _ _
    dsimp [Bind.bind]
    apply bind_mono (λ x => a) (λ x => x)
    · grind [monotone, PartialOrder.rel_refl]
    · grind [monotone, PartialOrder.rel_refl]
    · intro _; grind

end CTree

