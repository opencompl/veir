module

public import CTree.Order
public import CTree.Rel
public import CTree.Tower
public import CTree.LTS.Defs

@[expose] public section

namespace LTS

open Tower
open Lean.Order

@[grind]
inductive Rlbl {α : Type u} {β : Type v} (Ro : α → β → Prop) : label α → label β → Prop where
  | obs x y : Ro x y → Rlbl Ro (.obs x) (.obs y)
  | tau : Rlbl Ro .tau .tau

@[reducible]
def DivPresF {S S' : LTS} (Rdiv : S.state → S'.state → Prop) (s : S.state) (t : S'.state) : Prop :=
  ∀ s', S.trans .tau s s' → (∃ t', S'.trans .tau t t' ∧ Rdiv s' t') ∨ DivPresF Rdiv s' t
inductive_fixpoint

theorem DivPresF.mon : monotone (@DivPresF S S') := by
  intros R R' hle s t h
  apply DivPresF.induct (t := t) (pred := fun s => DivPresF R' s t)
  case x =>
    apply h
  case hyp =>
    intros s' ih
    unfold DivPresF
    rw [le_def_binary_rel] at hle
    grind

def DivPres {S S' : LTS} := gfp (@DivPresF S S')

theorem DivPresF.tau_star_r {S S' : LTS} : forall (R : Chain (@DivPresF S S')) s t t',
    R.elem s t' →
    (S'.trans .tau)^* t t' →
    R.elem s t := by
  apply (tower_ind (f := @DivPresF S S') (P := fun R => ∀ s t t', R s t' → (LTS.trans _ label.tau)^* t t' → R s t))
  case a =>
    intros P h s t t' h' h''
    rw [inf_iff_binary_rel]
    intros R' h'''
    apply h <;> try assumption
    rw [inf_iff_binary_rel] at h'
    solve_by_elim
  case a =>
    intros R ch s t t' hdiv htr
    apply DivPresF.induct (t := t') (pred := fun s => DivPresF R.elem s t)
    case hyp =>
      intros s'' ih
      unfold DivPresF
      intros s''' h
      have h := ih _ h
      cases h
      case inl h =>
        left
        cases htr
        case base =>
          apply h
        case iter t1 ht ht1 =>
          exists t1
          constructor; assumption
          rcases h with ⟨t'1, ⟨htr, hR⟩⟩
          apply ch
          apply hR
          apply Star.unfold_r
          exists t'
      case inr h =>
        right
        apply h
    case x =>
      apply hdiv

variable {S S' : LTS}
  (Ro : S.observable → S'.observable → Prop)
  
/-- Divergence-sensitive UB-sensitive weak simulation functor -/
@[reducible]
def SimF (Rdiv Rs : S.state → S'.state → Prop)
    (s : S.state) (t : S'.state) : Prop :=
  (∀ l s', S.trans (.obs l) s s' → ∃ l' t', ((S'.trans .tau)^* ∘ (S'.trans l')) t t' ∧ Rlbl Ro (.obs l) l' ∧ Rs s' t') ∧
  (∀ s', S.trans .tau s s' → ((Rs s' t ∧ Rdiv s' t) ∨ ∃ t', ((S'.trans .tau)^+ t t') ∧ Rs s' t'))

/-- Mutually coinductive simulation functor -/
@[grind]
inductive MuSimF (UB : S'.state → Prop)
    (Rs : Bool → S.state → S'.state → Prop)
  : Bool → S.state → S'.state → Prop where
| sim s s' : SimF Ro (Rs false) (Rs true) s s' → MuSimF UB Rs true s s'
| ub s t tUB : (S'.trans .tau)^* t tUB ∧ UB tUB → MuSimF UB Rs true s t
| div s t : DivPresF (Rs false) s t → MuSimF UB Rs false s t

attribute [simp] MuSimF.div

theorem MuSimF.mon : monotone (MuSimF UB Rs) := by
  unfold monotone
  intros R R' hle
  rw [le_def_ternary_rel] at hle
  intros b s t hm
  cases hm
  case sim hsim =>
    grind
  case ub tUB htr =>
    grind
  case div hdiv =>
    apply MuSimF.div
    apply DivPresF.mon (x := R false) <;> try assumption
    intros y z h
    grind

abbrev Sim {S S' : LTS} (Ro : S.observable → S'.observable → Prop) UB := gfp (MuSimF Ro UB) true

@[refl, grind .]
theorem Rlbl.refl (Ro : α → α → Prop) [h : Std.Refl Ro] l : Rlbl Ro l l := by
  cases l
  · constructor
  · constructor
    apply h.refl

@[refl, grind .]
theorem MuSimF.refl : ∀ (S : LTS) Ro (_hRo : Std.Refl Ro) UB (R : Chain (@MuSimF S S Ro UB)) b x, R.elem b x x := by
  intros S Ro hRo UB
  apply tower_ind (f := MuSimF Ro UB) (P := fun R => ∀ b x, R b x x)
  case a =>
    intros f h b x
    rw [inf_iff_ternary_rel (z := x)]
    intros R' h''
    apply h; assumption
  case a =>
    intros R ch b s
    cases b
    case false =>
      apply MuSimF.div
      unfold DivPresF
      intros s' h
      left
      grind
    case true =>
      apply MuSimF.sim
      constructor
      case left =>
        intros l s' htr
        exists (.obs l), s'
        constructor
        exists s <;> grind
        constructor
        rfl
        apply ch
      case right =>
        intros s' htr
        right
        exists s' <;> grind


-- copied from DivPresF
theorem MuSimF.divpres_tau_star_r {S S' : LTS} Ro UB : forall (R : Chain (@MuSimF S S' Ro UB)) s t t',
    R.elem false s t' →
    (S'.trans .tau)^* t t' →
    R.elem false s t := by
  apply (tower_ind (f := @MuSimF S S' Ro UB) (P := fun R => ∀ s t t', R false s t' → (LTS.trans _ label.tau)^* t t' → R false s t))
  case a =>
    intros P h s t t' h' h''
    rw [inf_iff_ternary_rel]
    intros R' h'''
    apply h <;> try assumption
    rw [inf_iff_ternary_rel] at h'
    solve_by_elim
  case a =>
    intros R ch s t t' hdiv htr
    constructor
    apply DivPresF.induct (t := t') (pred := fun s => DivPresF (R.elem false) s t)
    case hyp =>
      intros s'' ih
      unfold DivPresF
      intros s''' h
      have h := ih _ h
      cases h
      case inl h =>
        left
        cases htr
        case base =>
          apply h
        case iter t1 ht ht1 =>
          exists t1
          constructor; assumption
          rcases h with ⟨t'1, ⟨htr, hR⟩⟩
          apply ch
          apply hR
          apply Star.unfold_r
          exists t'
      case inr h =>
        right
        apply h
    case x =>
      grind

theorem MuSimF.tau_star_r {S S' : LTS} Ro UB : forall (R : Chain (@MuSimF S S' Ro UB)) s t t',
    R.elem true s t' →
    (S'.trans .tau)^* t t' →
    R.elem true s t := by
  apply (tower_ind (f := @MuSimF S S' Ro UB) (P := fun R => ∀ s t t', R true s t' → (LTS.trans _ label.tau)^* t t' → R true s t))
  case a =>
    intros f h s t t' h' htr
    rw [inf_iff_ternary_rel (z := t)]
    intros R' h''
    apply h <;> try assumption
    rw [inf_iff_ternary_rel] at h'
    grind
  case a =>
    intros R ch s t t' hsim htr
    cases hsim
    case sim hsim =>
      apply MuSimF.sim
      constructor
      · intros l s' htr'
        have hsim := hsim.left _ _ htr'
        rcases hsim with ⟨l', t'1, htr', hlbl, hR⟩
        exists l', t'1
        constructor
        · rw [Star.trans', Dot.assoc.assoc]
          exists t'
        · solve_by_elim
      · intros s' htr'
        have hsim := hsim.right _ htr'
        cases hsim
        case inl hsim =>
          rcases hsim with ⟨htrue, hfalse⟩
          left
          constructor
          solve_by_elim
          apply MuSimF.divpres_tau_star_r (t' := t') <;> assumption
        case inr hsim =>
          rcases hsim with ⟨t'', htr, hR⟩
          right
          rw [Plus.unfold_r, Star.trans', Dot.assoc.assoc, ←Plus.unfold_r]
          exists t''
          constructor
          exists t'
          apply hR
    case ub tUB hUB =>
      rcases hUB with ⟨htr', hUB⟩
      apply MuSimF.ub
      case a =>
        constructor
        case left =>
          apply Star.trans (hxy := htr) (hyz := htr')
        case right =>
          apply hUB

end LTS

