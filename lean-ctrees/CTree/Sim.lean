module

public import CTree.Order
public import CTree.Defs
public import CTree.UB
public import CTree.Iter
public import CTree.Interp
public import CTree.CTreeLTS

public section

open scoped Tower

theorem LTS.MuSimF.false_iff {S S' : LTS}
    {Ro : S.observable → S'.observable → Prop} {UB : S'.state → Prop}
    {Rs : Bool → S.state → S'.state → Prop} {s : S.state} {t : S'.state} :
    MuSimF Ro UB Rs false s t ↔ DivPresF (Rs false) s t := by
  constructor
  · intro h
    cases h with
    | div _ _ h => exact h
  · exact MuSimF.div s t

private theorem LTS.MuSimF.fold_gfp {S S' : LTS}
    {Ro : S.observable → S'.observable → Prop} {UB : S'.state → Prop}
    {b : Bool} {s : S.state} {t : S'.state}
    (h : MuSimF Ro UB (Tower.gfp (MuSimF Ro UB)) b s t) :
    Tower.gfp (MuSimF Ro UB) b s t := by
  rw [Tower.gfp_iff_ternary_rel]
  intro R
  apply Tower.Chain.apply_ternary_rel _ MuSimF.mon R
  apply MuSimF.mon (x := Tower.gfp (MuSimF Ro UB))
  · rw [Tower.le_def_ternary_rel]
    intro b s t h
    exact (Tower.gfp_iff_ternary_rel _ _ _ _).mp h R
  · exact h

/-- Without reachable UB on the right, simulation also preserves divergence. -/
private theorem LTS.MuSimF.div_of_sim {S S' : LTS}
    (Ro : S.observable → S'.observable → Prop) (UB : S'.state → Prop) :
    ∀ R : Tower.Chain (MuSimF Ro UB), ∀ s t,
      (¬ ∃ tUB, (S'.trans .tau)^* t tUB ∧ UB tUB) →
      Sim Ro UB s t → R.elem false s t := by
  apply Tower.tower_ind (f := MuSimF Ro UB) (P := fun R => ∀ s t,
    (¬ ∃ tUB, (S'.trans .tau)^* t tUB ∧ UB tUB) → Sim Ro UB s t → R false s t)
  · intro P ih s t hno hs
    rw [Tower.inf_iff_ternary_rel]
    intro R hR
    exact ih R hR s t hno hs
  · intro R ih s t hno hs
    apply MuSimF.div
    unfold DivPresF
    intro s' htr
    have hs := Tower.gfp_apply_ternary_rel _ _ _ _ hs
    rcases MuSimF.true_iff.mp hs with hs | hu
    · rcases hs.2 s' htr with ⟨_, hd⟩ | ⟨t', ⟨mid, hstep, hrest⟩, ht⟩
      · right
        apply DivPresF.mon (x := (Tower.gfp (MuSimF Ro UB)) false)
        · intro x y h
          exact (Tower.gfp_iff_ternary_rel _ _ _ _).mp h R
        · exact MuSimF.false_iff.mp (Tower.gfp_apply_ternary_rel _ _ _ _ hd)
      · left
        refine ⟨mid, hstep, ih s' mid ?_ ?_⟩
        · rintro ⟨tUB, hstar, hUB⟩
          exact hno ⟨tUB, .iter _ _ _ hstep hstar, hUB⟩
        · rw [Sim, Tower.gfp_iff_ternary_rel]
          intro Q
          exact MuSimF.tau_star_r Ro UB Q s' mid t'
            ((Tower.gfp_iff_ternary_rel _ _ _ _).mp ht Q) hrest
    · exact (hno hu).elim

-- Accessibility of the reversed transition relation means that all tau paths
-- are well founded. These lemmas handle the divergence component independently
-- of observable labels, including for infinitely branching trees.
private theorem LTS.MuSimF.acc_of_div {S S' : LTS}
    {Ro : S.observable → S'.observable → Prop} {UB : S'.state → Prop}
    {s : S.state} {t : S'.state}
    (ht : Acc (fun x y => S'.trans .tau y x) t)
    (h : Tower.gfp (MuSimF Ro UB) false s t) :
    Acc (fun x y => S.trans .tau y x) s := by
  induction ht generalizing s with
  | intro t ht ih =>
    have hd := MuSimF.false_iff.mp (Tower.gfp_apply_ternary_rel _ _ _ _ h)
    apply DivPresF.induct (t := t) (pred := fun s => Acc (fun x y => S.trans .tau y x) s)
    · intro s ihdiv
      constructor
      intro s' htr
      rcases ihdiv s' htr with ⟨t', htr', hdiv⟩ | hacc
      · exact ih t' htr' hdiv
      · exact hacc
    · exact hd

private theorem LTS.MuSimF.div_of_acc {S S' : LTS}
    {Ro : S.observable → S'.observable → Prop} {UB : S'.state → Prop}
    (R : Tower.Chain (MuSimF Ro UB)) {s : S.state} (t : S'.state)
    (hs : Acc (fun x y => S.trans .tau y x) s) : R.elem false s t := by
  apply Tower.Chain.apply_ternary_rel _ MuSimF.mon R
  apply MuSimF.div
  induction hs with
  | intro s _ ih =>
    unfold DivPresF
    intro s' htr
    exact Or.inr (ih s' htr)

private theorem LTS.MuSimF.div_of_not_acc {S S' : LTS}
    (Ro : S.observable → S'.observable → Prop) (UB : S'.state → Prop) :
    ∀ R : Tower.Chain (MuSimF Ro UB), ∀ (s : S.state) (t : S'.state),
      (¬ Acc (fun x y => S'.trans .tau y x) t) → R.elem false s t := by
  apply Tower.tower_ind (f := MuSimF Ro UB) (P := fun R => ∀ s t,
    (¬ Acc (fun x y => S'.trans .tau y x) t) → R false s t)
  · intro P ih s t ht
    rw [Tower.inf_iff_ternary_rel]
    intro R hR
    exact ih R hR s t ht
  · intro R ih s t ht
    classical
    have hnext : ∃ t', S'.trans .tau t t' ∧ ¬ Acc (fun x y => S'.trans .tau y x) t' := by
      apply Classical.byContradiction
      intro hn
      apply ht
      constructor
      intro t' htr
      apply Classical.byContradiction
      intro ht'
      exact hn ⟨t', htr, ht'⟩
    obtain ⟨t', htr, ht'⟩ := hnext
    apply MuSimF.div
    unfold DivPresF
    intro s' _
    exact Or.inl ⟨t', htr, ih s' t' ht'⟩

private theorem LTS.MuSimF.acc_of_sim {S S' : LTS}
    {Ro : S.observable → S'.observable → Prop} {UB : S'.state → Prop}
    {s : S.state} {t : S'.state}
    (hno : ¬ ∃ tUB, (S'.trans .tau)^* t tUB ∧ UB tUB)
    (ht : Acc (fun x y => S'.trans .tau y x) t) (h : Sim Ro UB s t) :
    Acc (fun x y => S.trans .tau y x) s := by
  apply MuSimF.acc_of_div ht
  rw [Tower.gfp_iff_ternary_rel]
  intro R
  exact MuSimF.div_of_sim Ro UB R s t hno h

/-- A simulation at the next tower stage already preserves divergence at the
current stage, provided the target cannot reach UB. -/
private theorem LTS.MuSimF.div_of_next {S S' : LTS}
    (Ro : S.observable → S'.observable → Prop) (UB : S'.state → Prop) :
    ∀ R : Tower.Chain (MuSimF Ro UB), ∀ s t,
      (¬ ∃ tUB, (S'.trans .tau)^* t tUB ∧ UB tUB) →
      MuSimF Ro UB R.elem true s t → R.elem false s t := by
  apply Tower.tower_ind (f := MuSimF Ro UB) (P := fun R => ∀ s t,
    (¬ ∃ tUB, (S'.trans .tau)^* t tUB ∧ UB tUB) →
    MuSimF Ro UB R true s t → R false s t)
  · intro P ih s t hno hs
    rw [Tower.inf_iff_ternary_rel]
    intro Q hQ
    apply ih Q hQ s t hno
    apply MuSimF.mon (x := Lean.Order.inf P)
    · exact Lean.Order.inf_le hQ
    · exact hs
  · intro R ih s t hno hs
    apply MuSimF.div
    unfold DivPresF
    intro s' htr
    rcases MuSimF.true_iff.mp hs with hs | hu
    · rcases hs.2 s' htr with ⟨_, hd⟩ | ⟨t', ⟨mid, hstep, hrest⟩, ht⟩
      · exact Or.inr (MuSimF.false_iff.mp hd)
      · left
        refine ⟨mid, hstep, ih s' mid ?_ ?_⟩
        · rintro ⟨tUB, hstar, hUB⟩
          exact hno ⟨tUB, .iter _ _ _ hstep hstar, hUB⟩
        · exact MuSimF.tau_star_r Ro UB (Tower.Chain.next _ R) s' mid t' ht hrest
    · exact (hno hu).elim

private theorem LTS.MuSimF.div_tau_closed {S S' : LTS}
    (Ro : S.observable → S'.observable → Prop) (UB : S'.state → Prop) :
    ∀ R : Tower.Chain (MuSimF Ro UB), ∀ s t,
      (∀ s', S.trans .tau s s' → R.elem false s' t) → R.elem false s t := by
  apply Tower.tower_ind (f := MuSimF Ro UB) (P := fun R => ∀ s t,
    (∀ s', S.trans .tau s s' → R false s' t) → R false s t)
  · intro P ih s t hs
    rw [Tower.inf_iff_ternary_rel]
    intro Q hQ
    apply ih Q hQ s t
    intro s' htr
    exact (Tower.inf_iff_ternary_rel _ _ _ _).mp (hs s' htr) Q hQ
  · intro R _ s t hs
    apply MuSimF.div
    unfold DivPresF
    intro s' htr
    exact Or.inr (MuSimF.false_iff.mp (hs s' htr))

namespace CTree
open Coinductive Lean.Order Tower LTS

variable {EIn FIn CIn C'In DIn X Y X' Y' : Type u}
  {E : EIn → Type u} {F : FIn → Type u} {C : CIn → Type u} {C' : C'In → Type u} {D : DIn → Type u}
  {α β : Type u} (RR : α → β → Prop)
  [UBE : HasUB EIn] [UBF : HasUB FIn]

abbrev MuSimF :
    (Bool → CTree E C α → CTree E C' β → Prop) → Bool → CTree E C α → CTree E C' β → Prop :=
  LTS.MuSimF (S := CTree.lts EIn CIn E C _) (S' := CTree.lts EIn C'In E C' _) (CTree.Robs RR) (CTree.UB (UB := UBE))

abbrev MuSimF.mon := @LTS.MuSimF.mon

variable (R : Chain (MuSimF RR (UBE := UBE)))

@[grind =]
theorem MuSimF.def (RR : α → β → Prop) :
  MuSimF RR = LTS.MuSimF (S := CTree.lts EIn CIn E C _) (S' := CTree.lts EIn C'In E C' _)
    (CTree.Robs RR) (CTree.UB (UB := UBE)) := by
  rfl

theorem MuSimF.refl (RR : α → α → Prop) [hRR : Std.Refl RR] (R : Chain (MuSimF RR)) (t : CTree E C α) :
    R.elem b t t := by
  apply LTS.MuSimF.refl
  apply CTree.instReflObsRobs

theorem MuSimF.empty :
    MuSimF (UBE := UBE) RR Rel true .empty t := by
  apply MuSimF.sim
  constructor
  case left =>
    intros l t htr
    exfalso
    apply trans_empty <;> assumption
  case right =>
    intros t htr
    exfalso
    apply trans_empty <;> assumption

theorem MuSimF.empty' (R : Chain (MuSimF RR)) (t : CTree E C' β) :
    R.elem true (CTree.empty : CTree E C α) t := by
  apply Chain.apply_ternary_rel
  apply MuSimF.mon
  apply MuSimF.empty

theorem MuSimF.ret (r : α) (r' : β) :
  RR r r' →
  Rel true .empty .empty →
  MuSimF RR Rel true (CTree.ret (E := E) (C := C) r) (CTree.ret (C := C') r') := by
  intro h h'
  apply LTS.MuSimF.sim
  constructor
  case left =>
    intros l s' htr
    have htr := trans_ret htr
    cases htr
    exists (.obs $ CTree.Obs.val r')
    exists .empty
    constructor
    · apply Star.skip_l
      constructor
    · constructor
      constructor
      constructor
      assumption
      grind
  case right =>
    intros t' h'
    have h' := trans_ret h'
    grind

theorem MuSimF.ret' (R : Chain (MuSimF RR)) (r : α) (r' : β) :
  RR r r' →
  R.elem true (CTree.ret (E := E) (C := C) r) (CTree.ret (C := C') r') := by
  intros h
  apply Chain.apply_ternary_rel
  apply MuSimF.mon
  apply MuSimF.ret <;> try assumption
  apply Chain.apply (f := MuSimF _)
  apply MuSimF.mon
  apply MuSimF.empty

/-
theorem MuSimF.ret_inv (r : α) (r' : β) :
    MuSimF RR Rel true (CTree.ret (E := E) (C := C) r) (CTree.ret (C := C') r') →
    RR r r' := by
  intros h
  cases h
-/

theorem MuSimF.tau (i : C1In ⊕ CIn) (i' : C1In ⊕ C'In) (k : (C1 ⊕ₑ C) i → CTree E C α) (k' : (C1 ⊕ₑ C') i' → CTree E C' β) :
    (∀ x, ∃ y, R.elem true (k x) (k' y)) →
    MuSimF RR R.elem true (CTree.tauG i k) (CTree.tauG i' k') := by
  intros h
  apply LTS.MuSimF.sim
  constructor
  case left =>
    intros l s' htr
    have htr := trans_tau htr
    grind
  case right =>
    intros t' h'
    have h' := trans_tau' h'
    rcases h' with ⟨o, h'⟩
    subst h'
    right
    have h := h o
    rcases h with ⟨o', h⟩
    exists (k' o')
    constructor
    apply Plus.once
    constructor
    assumption

theorem MuSimF.tau1 (t : CTree E C α) (u : CTree E C' β) :
    R.elem true t u →
    MuSimF RR R.elem true (CTree.tau1 t) (CTree.tau1 u) := by
  intros
  apply tau
  intros x
  cases x
  exists ⟨⟩

theorem MuSimF.tau_r (i' : C1In ⊕ C'In) (t : CTree E C α) (k' : (C1 ⊕ₑ C') i' → CTree E C' β) x :
    R.elem true t (k' x) →
    R.elem true t (CTree.tauG i' k') := by
  intros h
  apply LTS.MuSimF.tau_star_r (t' := k' x)
  · apply h
  · apply Star.once
    constructor

theorem MuSimF.vis (i : EIn) [inh : Inhabited (E i)] (k : E i → CTree E C α) (k' : E i → CTree E C' β) :
    (∀ x, R.elem true (k x) (k' x)) →
    MuSimF RR R.elem true (CTree.vis i k) (CTree.vis i k') := by
  intros h
  apply MuSimF.sim
  constructor
  case left =>
    intros l t htr
    have htr := trans_vis _ _ _ _ htr
    rcases htr with ⟨o, htr⟩
    cases htr
    exists (.obs (.eff i o))
    exists (k' o)
    constructor
    case left =>
      apply Star.skip_l
      constructor
    case right =>
      constructor
      constructor
      constructor
      grind
  case right =>
    intros t' htr
    have htr := trans_vis _ _ _ _ htr
    grind

theorem MuSimF.ub {t : CTree E C α} (e : EIn) {k : E e → CTree E C' β} :
    @HasUB.isUB _ UBE e →
    MuSimF RR R.elem true t (CTree.vis e k) := by
  intros h
  apply LTS.MuSimF.ub (tUB := CTree.vis e k)
  constructor
  · apply Star.base
  · unfold CTree.UB
    simp
    apply h

/--
Simulation between ctrees: the rhs should have at least all
the behaviors of the lhs.
The simulation is parameterized by a relation on return values.
-/
abbrev Sim (RR : α → β → Prop) (t : CTree E C α) (u : CTree E C' β) : Prop :=
  LTS.Sim (S := CTree.lts EIn CIn E C _) (S' := CTree.lts EIn C'In E C' _) (CTree.Robs RR) (CTree.UB (UB := UBE)) t u

namespace Sim

omit UBE in
private theorem tau_star_ret (r : α) {t : CTree E C α}
    (h : (CTree.Trans .tau)^* (CTree.ret r) t) : t = CTree.ret r := by
  cases h with
  | base => rfl
  | iter _ _ _ htr _ => cases trans_ret htr


/-- A tree simulates itself with any reflexive relation. -/
theorem refl (RR : α → α → Prop) (hrefl : ∀ value, RR value value) (t : CTree E C α) :
    Sim RR t t := by
  unfold Sim LTS.Sim
  rw [gfp_iff_ternary_rel]
  intros R
  apply MuSimF.refl (t := t) (b := true) (hRR := ⟨hrefl⟩) (R := R)

@[simp]
theorem ret (r : α) (r' : β) :
    Sim RR (CTree.ret (E := E) (C := C) r) (CTree.ret (C := C') r') ↔
    RR r r' := by
  constructor
  case mp =>
    intros h
    have h := gfp_apply_ternary_rel _ _ _ _ h
    rcases LTS.MuSimF.true_iff.mp h with hs | ⟨tUB, htr, hUB⟩
    · obtain ⟨l', t', ⟨mid, hstar, hstep⟩, hlbl, _⟩ :=
        hs.1 (.val r) CTree.empty CTree.Trans.ret
      have hmid := tau_star_ret r' hstar
      subst mid
      have hl := trans_ret hstep
      cases hl
      cases hlbl with
      | obs _ _ hobs => cases hobs with
        | val _ _ hr => exact hr
    · have ht := tau_star_ret r' htr
      subst tUB
      simp [CTree.UB] at hUB
  case mpr =>
    intros h
    unfold Sim LTS.Sim
    rw [gfp_iff_ternary_rel]
    intros R
    apply MuSimF.ret'
    apply h


@[simp, grind =]
theorem pure (r : α) (r' : β) :
    Sim (C := C) (C' := C') (E := E) RR (pure r) (pure r') ↔ RR r r' := by
  simp only [Pure.pure, ret]

@[simp]
theorem tau_l (i : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) i → CTree E C α)
    (u : CTree E C' β) :
    Sim RR (CTree.tauG i k) u ↔ ∀ x, Sim RR (k x) u := by
  constructor
  · intro h x
    have h := gfp_apply_ternary_rel _ _ _ _ h
    rcases LTS.MuSimF.true_iff.mp h with hs | ⟨tUB, hu⟩
    · rcases hs.2 (k x) CTree.Trans.tau with ⟨ht, _⟩ | ⟨t', hstar, ht⟩
      · exact ht
      · rw [Sim, LTS.Sim, gfp_iff_ternary_rel]
        intro R
        exact LTS.MuSimF.tau_star_r _ _ R _ _ _
          ((gfp_iff_ternary_rel _ _ _ _).mp ht R) (Star.plus _ hstar)
    · exact LTS.MuSimF.fold_gfp (.ub _ _ tUB hu)
  · intro h
    classical
    by_cases hu : ∃ tUB, (CTree.Trans .tau)^* u tUB ∧ CTree.UB tUB
    · obtain ⟨tUB, hu⟩ := hu
      exact LTS.MuSimF.fold_gfp (.ub _ _ tUB hu)
    · apply LTS.MuSimF.fold_gfp
      apply LTS.MuSimF.sim
      constructor
      · intro l s' htr
        cases trans_tau htr
      · intro s' htr
        obtain ⟨x, rfl⟩ := trans_tau' htr
        left
        refine ⟨h x, ?_⟩
        rw [gfp_iff_ternary_rel]
        intro R
        exact LTS.MuSimF.div_of_sim _ _ R _ _ hu (h x)

theorem tau_r (i' : C1In ⊕ C'In) (t : CTree E C α) (k' : (C1 ⊕ₑ C') i' → CTree E C' β) x :
    Sim RR t (k' x) →
    Sim RR t (CTree.tauG i' k') := by
  intros h
  unfold Sim LTS.Sim
  rw [gfp_iff_ternary_rel]
  intros R
  apply MuSimF.tau_r <;> try assumption
  revert R
  rw [← gfp_iff_ternary_rel]
  exact h

@[simp]
theorem pure_tau (r : α) (i' : C1In ⊕ C'In)
    (k' : (C1 ⊕ₑ C') i' → CTree E C' β) :
    Sim RR (Pure.pure (f := CTree E C) r) (CTree.tauG i' k') ↔
      ∃ x, Sim RR (Pure.pure (f := CTree E C) r) (k' x) := by
  change Sim RR (CTree.ret r) (CTree.tauG i' k') ↔
    ∃ x, Sim RR (CTree.ret r) (k' x)
  constructor
  · intro h
    have h := gfp_apply_ternary_rel _ _ _ _ h
    rcases LTS.MuSimF.true_iff.mp h with hs | ⟨tUB, hstar, hUB⟩
    · obtain ⟨l', t', ⟨mid, hstar, hstep⟩, hlbl, hR⟩ :=
        hs.1 (.val r) CTree.empty CTree.Trans.ret
      cases hstar with
      | base =>
        have hl := trans_tau hstep
        rw [hl] at hlbl
        cases hlbl
      | iter _ first _ hfirst hrest =>
        obtain ⟨x, rfl⟩ := trans_tau' hfirst
        refine ⟨x, LTS.MuSimF.fold_gfp (.sim _ _ ?_)⟩
        constructor
        · intro l s' htr
          have hl := trans_ret htr
          have ht := trans_ret' htr
          cases hl
          subst s'
          exact ⟨l', t', ⟨mid, hrest, hstep⟩, hlbl, hR⟩
        · intro s' htr
          cases trans_ret htr
    · cases hstar with
      | base => simp [CTree.UB] at hUB
      | iter _ first _ hfirst hrest =>
        obtain ⟨x, rfl⟩ := trans_tau' hfirst
        exact ⟨x, LTS.MuSimF.fold_gfp (.ub _ _ tUB ⟨hrest, hUB⟩)⟩
  · rintro ⟨x, hx⟩
    exact tau_r RR i' (CTree.ret r) k' x hx

@[simp]
theorem pure_bind_choose_iff
  {SubCIn : Type u} {SubC : SubCIn → Type u} [SubC -< C']
  (value : α) (choice : SubCIn) (after : SubC choice → CTree E C' β) :
    CTree.Sim RR (Pure.pure value : CTree E C α)
        (CTree.bind (CTree.choose choice) after) ↔
      ∃ chosen, CTree.Sim RR (Pure.pure value : CTree E C α) (after chosen) := by
  simp only [CTree.choose_def, Subeffect.mapEff, Subeffect.mapCont, CTree.ret_pure, CTree.tau_def,
    CTree.CTree.bind_tau, SumE.eq_inr, CTree.bind_pure, Sim.pure_tau]
  constructor
  · grind
  · rintro ⟨chosen, h⟩
    grind [Subeffect.map_surj (ε₁ := SubC) (ε₂ := C') choice chosen]

theorem tau (i : C1In ⊕ CIn) (i' : C1In ⊕ C'In) (k : (C1 ⊕ₑ C) i → CTree E C α) (k' : (C1 ⊕ₑ C') i' → CTree E C' β) :
  (∀ x, ∃ y, Sim RR (k x) (k' y)) →
  Sim RR (CTree.tauG i k) (CTree.tauG i' k') := by
  intro h
  apply (tau_l RR i k _).2
  intro x
  obtain ⟨y, hxy⟩ := h x
  exact tau_r RR i' (k x) k' y hxy

theorem tau_id (i : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) i → CTree E C α) (k' : (C1 ⊕ₑ C) i → CTree E C β) :
  (∀ x, Sim RR (k x) (k' x)) →
  Sim RR (CTree.tauG i k) (CTree.tauG i k') := by
  intros
  grind [tau]

theorem vis (i : EIn) [Inhabited (E i)] (k : E i → CTree E C α) (k' : E i → CTree E C' β) :
    (∀ x, Sim RR (k x) (k' x)) →
    Sim RR (CTree.vis i k) (CTree.vis i k') := by
  intros h
  unfold Sim LTS.Sim
  rw [gfp_iff_ternary_rel]
  intros R
  apply Chain.apply_ternary_rel
  apply MuSimF.mon
  apply MuSimF.vis <;> try assumption
  intros e
  revert R
  rw [← gfp_iff_ternary_rel]
  apply h

theorem ub {t : CTree E C α} (e : EIn) {k : E e → CTree E C' β} :
    @HasUB.isUB _ UBE e →
    Sim RR t (CTree.vis e k) := by
  intros h
  unfold Sim LTS.Sim
  rw [gfp_iff_ternary_rel]
  intros R
  apply Chain.apply_ternary_rel
  apply MuSimF.mon
  apply MuSimF.ub
  apply h

omit UBE in
private theorem trans_bind_tau {t t' : CTree E C α}
    (k : α → CTree E C β) (h : CTree.Trans .tau t t') :
    CTree.Trans .tau (CTree.bind t k) (CTree.bind t' k) := by
  cases h with
  | tau => simpa only [CTree.bind_tau] using CTree.Trans.tau

omit UBE in
private theorem bind_empty (k : α → CTree E C β) :
    CTree.bind (CTree.empty : CTree E C α) k = CTree.empty := by
  rw [CTree.empty, CTree.bind_tau]
  congr 1
  funext x
  cases x

omit UBE in
private theorem trans_bind_eff {t t' : CTree E C α} {i : EIn} {x : E i}
    (k : α → CTree E C β) (h : CTree.Trans (.obs (.eff i x)) t t') :
    CTree.Trans (.obs (.eff i x)) (CTree.bind t k) (CTree.bind t' k) := by
  cases h
  simpa only [CTree.bind_vis] using CTree.Trans.vis

omit UBE in
private theorem trans_bind_effEmpty {t t' : CTree E C α} {i : EIn}
    (k : α → CTree E C β) (h : CTree.Trans (.obs (.effEmpty i)) t t') :
    CTree.Trans (.obs (.effEmpty i)) (CTree.bind t k) (CTree.bind t' k) := by
  cases h with
  | visEmpty i ks hempty =>
    simpa only [CTree.bind_vis, bind_empty] using
      CTree.Trans.visEmpty i (fun x => CTree.bind (ks x) k) hempty

omit UBE in
private theorem star_bind_tau {t t' : CTree E C α}
    (k : α → CTree E C β) (h : (CTree.Trans .tau)^* t t') :
    (CTree.Trans .tau)^* (CTree.bind t k) (CTree.bind t' k) := by
  induction h with
  | base => exact .base _
  | iter _ _ _ h _ ih => exact .iter _ _ _ (trans_bind_tau k h) ih

private theorem bind_reaches_ub {t : CTree E C α} (k : α → CTree E C β)
    (h : ∃ tUB, (CTree.Trans .tau)^* t tUB ∧ CTree.UB tUB) :
    ∃ tUB, (CTree.Trans .tau)^* (CTree.bind t k) tUB ∧ CTree.UB tUB := by
  obtain ⟨tUB, hstar, hUB⟩ := h
  refine ⟨CTree.bind tUB k, star_bind_tau k hstar, ?_⟩
  cases tUB with
  | ret => simp [CTree.UB] at hUB
  | tau => simp [CTree.UB] at hUB
  | vis => simpa only [CTree.bind_vis, CTree.UB, unfold_vis] using hUB

omit UBE in
private theorem trans_vis_cases {i : EIn} {k : E i → CTree E C α}
    {l : label (@CTree.Obs EIn E α)} {t' : CTree E C α}
    (h : CTree.Trans l (CTree.vis i k) t') :
    (∃ x, l = .obs (.eff i x) ∧ t' = k x) ∨
      ((E i → False) ∧ l = .obs (.effEmpty i) ∧ t' = CTree.empty) := by
  generalize ht : CTree.vis i k = t at h
  cases h with
  | tau => grind
  | ret => grind
  | vis =>
    rename_i j x k'
    have hi := vis_eq_vis _ _ _ _ ht
    subst j
    have hk := vis_eq_vis' _ _ _ ht
    subst k'
    exact Or.inl ⟨x, rfl, rfl⟩
  | visEmpty j k' hempty =>
    have hi := vis_eq_vis _ _ _ _ ht
    subst j
    exact Or.inr ⟨hempty, rfl, rfl⟩

omit UBE in
private theorem acc_of_bind_acc (k : α → CTree E C β) (t : CTree E C α)
    (h : Acc (fun x y => CTree.Trans .tau y x) (CTree.bind t k)) :
    Acc (fun x y => CTree.Trans .tau y x) t := by
  generalize heq : CTree.bind t k = u at h
  induction h generalizing t with
  | intro u _ ih =>
    constructor
    intro t' htr
    apply ih (CTree.bind t' k) _ t' rfl
    rw [← heq]
    exact trans_bind_tau k htr

private theorem ret_bind_chain {α' β' : Type u} {RS : α → α' → Prop} {RT : β → β' → Prop}
    (R : Chain (MuSimF RT)) (r : α) (u : CTree E C' α')
    (k : α → CTree E C β) (k' : α' → CTree E C' β')
    (h : Sim RS (CTree.ret (C := C) r) u)
    (hk : ∀ x y, RS x y → R.elem true (k x) (k' y)) :
    R.elem true (k r) (CTree.bind u k') := by
  have h := gfp_apply_ternary_rel _ _ _ _ h
  rcases LTS.MuSimF.true_iff.mp h with hs | hu
  · obtain ⟨l', t', ⟨mid, hstar, hstep⟩, hlbl, _⟩ :=
      hs.1 (.val r) CTree.empty CTree.Trans.ret
    cases hlbl with
    | obs _ _ hobs =>
      cases hobs with
      | val _ y hrel =>
        cases hstep
        apply LTS.MuSimF.tau_star_r _ _ R _ _ _ (hk r y hrel)
        simpa only [CTree.bind_ret] using star_bind_tau k' hstar
  · obtain ⟨tUB, hu⟩ := bind_reaches_ub k' hu
    exact Chain.apply_ternary_rel _ MuSimF.mon R _ _ _ (LTS.MuSimF.ub _ _ tUB hu)

private theorem bind_div_next {α' β' : Type u} {RS : α → α' → Prop} {RT : β → β' → Prop}
    (R : Chain (MuSimF RT)) (t : CTree E C α) (u : CTree E C' α')
    (k : α → CTree E C β) (k' : α' → CTree E C' β') (h : Sim RS t u)
    (hk : ∀ x y, RS x y → MuSimF RT R.elem true (k x) (k' y))
    (hno : ¬ ∃ tUB, (CTree.Trans .tau)^* (CTree.bind u k') tUB ∧ CTree.UB tUB) :
    R.elem false (CTree.bind t k) (CTree.bind u k') := by
  classical
  by_cases hu : Acc (fun x y => CTree.Trans .tau y x) (CTree.bind u k')
  · have ht : Acc (fun x y => CTree.Trans .tau y x) t :=
      LTS.MuSimF.acc_of_sim (fun h => hno (bind_reaches_ub k' h)) (acc_of_bind_acc k' u hu) h
    induction ht with
    | intro t ht ih =>
      cases t with
      | ret r =>
        rw [bind_pure]
        apply LTS.MuSimF.div_of_next _ _ R _ _ hno
        exact ret_bind_chain (Chain.next _ R) r u k k' h hk
      | tau i ks =>
        rw [CTree.bind_tau]
        apply LTS.MuSimF.div_tau_closed _ _ R
        intro s' htr
        obtain ⟨x, rfl⟩ := trans_tau' htr
        exact ih (ks x) CTree.Trans.tau ((tau_l RS i ks u).mp h x)
      | vis i ks =>
        rw [CTree.bind_vis]
        apply LTS.MuSimF.div_tau_closed _ _ R
        intro s' htr
        rcases trans_vis_cases htr with ⟨x, hx, _⟩ | ⟨_, hx, _⟩ <;> cases hx
  · exact LTS.MuSimF.div_of_not_acc _ _ R _ _ hu

theorem _root_.CTree.MuSimF.bind {RR'} (t : CTree E C α') (u : CTree E C' β') (k : α' → CTree E C α) (k' : β' → CTree E C' β) :
    Sim RR' t u →
    (∀ x y, RR' x y → R.elem true (k x) (k' y)) →
    R.elem true (bind t k) (bind u k') := by
  intro h hk
  revert t u h hk
  revert R
  apply tower_ind (f := MuSimF RR) (P := fun R => ∀ t u,
    Sim RR' t u → (∀ x y, RR' x y → R true (k x) (k' y)) →
      R true (CTree.bind t k) (CTree.bind u k'))
  · intro P ih t u h hk
    rw [inf_iff_ternary_rel]
    intro Q hQ
    apply ih Q hQ t u h
    intro x y hxy
    exact (inf_iff_ternary_rel _ _ _ _).mp (hk x y hxy) Q hQ
  · intro R ih t u h hk
    have hk' : ∀ x y, RR' x y → R.elem true (k x) (k' y) := by
      intro x y hxy
      exact Chain.apply_ternary_rel _ MuSimF.mon R _ _ _ (hk x y hxy)
    classical
    by_cases hUB : ∃ tUB, (CTree.Trans .tau)^* (CTree.bind u k') tUB ∧ CTree.UB tUB
    · obtain ⟨tUB, hUB⟩ := hUB
      exact LTS.MuSimF.ub _ _ tUB hUB
    have hs := gfp_apply_ternary_rel _ _ _ _ h
    rcases LTS.MuSimF.true_iff.mp hs with hs | hu
    · cases t with
      | ret r =>
        rw [bind_pure]
        exact ret_bind_chain (Chain.next _ R) r u k k' h hk
      | tau i ks =>
        rw [CTree.bind_tau]
        apply LTS.MuSimF.sim
        constructor
        · intro l s' htr
          cases trans_tau htr
        · intro s' htr
          obtain ⟨x, rfl⟩ := trans_tau' htr
          rcases hs.2 (ks x) CTree.Trans.tau with ⟨ht, _⟩ | ⟨u', ⟨mid, hstep, hstar⟩, ht⟩
          · exact Or.inl ⟨ih (ks x) u ht hk', bind_div_next R (ks x) u k k' ht hk hUB⟩
          · right
            exact ⟨CTree.bind u' k', ⟨CTree.bind mid k', trans_bind_tau k' hstep,
              star_bind_tau k' hstar⟩, ih (ks x) u' ht hk'⟩
      | vis i ks =>
        rw [CTree.bind_vis]
        apply LTS.MuSimF.sim
        constructor
        · intro l s' htr
          rcases trans_vis_cases htr with ⟨x, hl, ht⟩ | ⟨hempty, hl, ht⟩
          · cases hl
            subst s'
            obtain ⟨l', u', ⟨mid, hstar, hstep⟩, hlbl, hR⟩ :=
              hs.1 (.eff i x) (ks x) CTree.Trans.vis
            cases hlbl with
            | obs _ _ hobs =>
              cases hobs with
              | eff =>
                exact ⟨.obs (.eff i x), CTree.bind u' k',
                  ⟨CTree.bind mid k', star_bind_tau k' hstar, trans_bind_eff k' hstep⟩,
                  .obs _ _ (.eff _ _), ih (ks x) u' hR hk'⟩
          · cases hl
            subst s'
            obtain ⟨l', u', ⟨mid, hstar, hstep⟩, hlbl, hR⟩ :=
              hs.1 (.effEmpty i) CTree.empty (CTree.Trans.visEmpty i ks hempty)
            cases hlbl with
            | obs _ _ hobs =>
              cases hobs with
              | effEmpty =>
                refine ⟨.obs (.effEmpty i), CTree.bind u' k',
                  ⟨CTree.bind mid k', star_bind_tau k' hstar, trans_bind_effEmpty k' hstep⟩,
                  .obs _ _ (.effEmpty _), ?_⟩
                simpa only [bind_empty] using ih CTree.empty u' hR hk'
        · intro s' htr
          rcases trans_vis_cases htr with ⟨x, hx, _⟩ | ⟨_, hx, _⟩ <;> cases hx
    · exact (hUB (bind_reaches_ub k' hu)).elim

theorem _root_.CTree.MuSimF.bind' {RR'} (t : CTree E C α') (u : CTree E C' β') (k : α' → CTree E C α) (k' : β' → CTree E C' β) :
    Sim RR' t u →
    (∀ x y, RR' x y → MuSimF RR R.elem true (k x) (k' y)) →
    MuSimF RR R.elem true (CTree.bind t k) (CTree.bind u k') := by
  apply MuSimF.bind (R := Chain.next (MuSimF RR) R)

theorem bind {RR RR'} (t : CTree E C α) (u : CTree E C' α') (k : α → CTree E C β) (k' : α' → CTree E C' β') :
  Sim RR t u →
  (∀ x y, RR x y → Sim RR' (k x) (k' y)) →
  Sim RR' (bind t k) (bind u k') := by
  intro h hk
  rw [Sim, LTS.Sim, gfp_iff_ternary_rel]
  intro R
  apply MuSimF.bind _ R t u k k' h
  intro x y hxy
  exact (gfp_iff_ternary_rel _ _ _ _).mp (hk x y hxy) R

/-- A simulation remains valid when its relation on return values is weakened. -/
theorem mono {RR RS : α → β → Prop} {t : CTree E C α} {u : CTree E C' β}
    (h : Sim RR t u) (hrel : ∀ x y, RR x y → RS x y) : Sim RS t u := by
  have hbind := bind t u CTree.ret CTree.ret h
    (fun x y hxy => (ret RS x y).mpr (hrel x y hxy))
  change Sim RS (t >>= Pure.pure) (u >>= Pure.pure) at hbind
  simpa only [_root_.bind_pure] using hbind

private theorem tau_step_left {t t' : CTree E C α} {u : CTree E C' β}
    (h : Sim RR t u) (htr : CTree.Trans .tau t t') : Sim RR t' u := by
  cases htr
  exact (tau_l RR _ _ u).mp h _

private theorem tau_star_left {t t' : CTree E C α} {u : CTree E C' β}
    (h : Sim RR t u) (htr : (CTree.Trans .tau)^* t t') : Sim RR t' u := by
  induction htr with
  | base => exact h
  | iter _ _ _ hstep _ ih => exact ih (tau_step_left RR h hstep)

/-- A tree simulating a reachable UB must itself be able to reach UB silently. -/
private theorem ub_reaches_of_sim
    {t : CTree E C α} {u : CTree E C' β} (h : Sim RR t u)
    (hu : ∃ tUB, (CTree.Trans .tau)^* t tUB ∧ CTree.UB tUB) :
    ∃ uUB, (CTree.Trans .tau)^* u uUB ∧ CTree.UB uUB := by
  obtain ⟨tUB, hstar, hUB⟩ := hu
  have hs := tau_star_left RR h hstar
  cases tUB with
  | ret => simp [CTree.UB] at hUB
  | tau => simp [CTree.UB] at hUB
  | vis i ks =>
    simp only [CTree.UB, unfold_vis] at hUB
    have hs := gfp_apply_ternary_rel _ _ _ _ hs
    rcases LTS.MuSimF.true_iff.mp hs with hs | hu
    · classical
      by_cases he : Nonempty (E i)
      · obtain ⟨x⟩ := he
        obtain ⟨l', u', ⟨mid, hstar, hstep⟩, hlbl, _⟩ :=
          hs.1 (.eff i x) (ks x) CTree.Trans.vis
        cases hlbl with
        | obs _ _ hobs =>
          cases hobs with
          | eff =>
            cases hstep
            refine ⟨_, hstar, ?_⟩
            simp only [CTree.UB, unfold_vis]
            exact hUB
      · obtain ⟨l', u', ⟨mid, hstar, hstep⟩, hlbl, _⟩ :=
          hs.1 (.effEmpty i) CTree.empty (CTree.Trans.visEmpty i ks (fun x => he ⟨x⟩))
        cases hlbl with
        | obs _ _ hobs =>
          cases hobs with
          | effEmpty =>
            cases hstep
            refine ⟨_, hstar, ?_⟩
            simpa only [CTree.UB, unfold_vis] using hUB
    · exact hu

omit UBE in
private theorem robs_comp {γ : Type u} {RS : α → β → Prop} {RT : β → γ → Prop}
    {x : @CTree.Obs EIn E α} {y : @CTree.Obs EIn E β} {z : @CTree.Obs EIn E γ}
    (h : CTree.Robs RS x y) (h' : CTree.Robs RT y z) :
    CTree.Robs (fun x z => ∃ y, RS x y ∧ RT y z) x z := by
  cases h with
  | eff =>
    cases h'
    exact .eff _ _
  | effEmpty i =>
    cases h'
    exact .effEmpty i
  | val x y hRS =>
    cases h' with
    | val _ z hRT => exact .val _ _ ⟨y, hRS, hRT⟩

private theorem trans_div_chain
    {R₁ R₂ R₃ : Type u} {RS : R₁ → R₂ → Prop} {RT : R₂ → R₃ → Prop}
    (R : Chain (MuSimF (C := C) (C' := D)
      (fun x z => ∃ y, RS x y ∧ RT y z)))
    {t : CTree E C R₁} {u : CTree E C' R₂} {v : CTree E D R₃}
    (h : Sim RS t u) (h' : Sim RT u v)
    (hno : ¬ ∃ vUB, (CTree.Trans .tau)^* v vUB ∧ CTree.UB vUB) :
    R.elem false t v := by
  classical
  by_cases hv : Acc (fun x y => CTree.Trans .tau y x) v
  · have hnu : ¬ ∃ uUB, (CTree.Trans .tau)^* u uUB ∧ CTree.UB uUB :=
      fun hu => hno (ub_reaches_of_sim RT h' hu)
    have hu := LTS.MuSimF.acc_of_sim hno hv h'
    exact LTS.MuSimF.div_of_acc R v (LTS.MuSimF.acc_of_sim hnu hu h)
  · exact LTS.MuSimF.div_of_not_acc _ _ R _ _ hv

/-- Simulations compose by relating their return values through an intermediate outcome. -/
theorem trans_rel {R₁ R₂ R₃ : Type u} {RS : R₁ → R₂ → Prop} {RT : R₂ → R₃ → Prop}
    {t : CTree E C R₁} {u : CTree E C' R₂} {v : CTree E D R₃} :
    Sim RS t u → Sim RT u v →
    Sim (fun x z => ∃ y, RS x y ∧ RT y z) t v := by
  intro h h'
  rw [Sim, LTS.Sim, gfp_iff_ternary_rel]
  intro R
  revert t u v h h'
  revert R
  apply tower_ind (f := MuSimF
    (fun x z => ∃ y, RS x y ∧ RT y z)) (P := fun R => ∀ t u v,
      Sim RS t u → Sim RT u v → R true t v)
  · intro P ih t u v h h'
    rw [inf_iff_ternary_rel]
    intro R hR
    exact ih R hR t u v h h'
  · intro R ih t u v h h'
    classical
    by_cases hUB : ∃ vUB, (CTree.Trans .tau)^* v vUB ∧ CTree.UB vUB
    · obtain ⟨vUB, hUB⟩ := hUB
      exact LTS.MuSimF.ub _ _ vUB hUB
    have hs := gfp_apply_ternary_rel _ _ _ _ h
    rcases LTS.MuSimF.true_iff.mp hs with hs | hu
    · apply LTS.MuSimF.sim
      constructor
      · intro l t' htr
        obtain ⟨m, u', ⟨mid, hstar, hstep⟩, hlbl, hR⟩ := hs.1 l t' htr
        cases hlbl with
        | obs _ m hobs =>
          have hm := tau_star_left RT h' hstar
          have hm := gfp_apply_ternary_rel _ _ _ _ hm
          rcases LTS.MuSimF.true_iff.mp hm with hm | hv
          · obtain ⟨n, v', ⟨mid', hstar', hstep'⟩, hlbl', hR'⟩ := hm.1 m u' hstep
            cases hlbl' with
            | obs _ n hobs' =>
              exact ⟨.obs n, v', ⟨mid', hstar', hstep'⟩,
                .obs _ _ (robs_comp hobs hobs'), ih t' u' v' hR hR'⟩
          · exact (hUB hv).elim
      · intro t' htr
        have ht := tau_step_left RS h htr
        exact Or.inl ⟨ih t' u v ht h', trans_div_chain R ht h' hUB⟩
    · exact (hUB (ub_reaches_of_sim RT h' hu)).elim

/-- Compose simulations when the two return relations imply the desired relation. -/
theorem trans {R₁ R₂ R₃ : Type u} {RS : R₁ → R₂ → Prop} {RT : R₂ → R₃ → Prop}
    {RU : R₁ → R₃ → Prop} {t : CTree E C R₁} {u : CTree E C' R₂} {v : CTree E D R₃}
    (htu : Sim RS t u) (huv : Sim RT u v)
    (hrel : ∀ x y z, RS x y → RT y z → RU x z) : Sim RU t v := by
  apply (trans_rel htu huv).mono
  rintro x z ⟨y, hxy, hyz⟩
  exact hrel x y z hxy hyz

theorem iter {I I'} {RRi : I → I' → Prop} {RRo : α → β → Prop}
    (body : I → CTree E C (I ⊕ α)) (body' : I' → CTree E C (I' ⊕ β)) i i' :
    RRi i i' →
    (∀ x y, RRi x y → Sim (Sum.LiftRel RRi RRo) (body x) (body' y)) →
    Sim (β := β) RRo (CTree.iter body i) (CTree.iter (X := β) body' i') := by
  intros h h'
  unfold Sim LTS.Sim
  rw [gfp_iff_ternary_rel]
  intros R
  revert i i' h h'
  change Chain (MuSimF RRo (UBE := UBE)) at R
  revert R
  apply tower_ind (f := MuSimF RRo (UBE := UBE)) (P := fun R => ∀ i i', RRi i i' → (∀ x y, RRi x y → Sim (Sum.LiftRel RRi RRo) (body x) (body' y)) → R true (CTree.iter body i) (CTree.iter body' i'))
  · intros P h i i' hi h'
    rw [inf_iff_ternary_rel]
    intros R h''
    apply h
    apply h''
    apply hi
    apply h'
  · intros R ch i i' hi hsim
    unfold CTree.iter
    simp only [Bind.bind]
    apply MuSimF.bind' (RR' := Sum.LiftRel RRi RRo)
    apply hsim
    apply hi
    intros x y hRR
    cases x
    case inl x =>
      cases y
      case inl y =>
        apply MuSimF.tau1
        apply ch
        grind
        apply hsim
      case inr y =>
        grind
    case inr x =>
      cases y
      case inl y =>
        grind
      case inr y =>
        simp only
        apply MuSimF.ret
        grind
        apply MuSimF.empty'

-- UB preservation alone is insufficient for arbitrary handlers. See the checked
-- counterexample in UnitTest/CTreeSimInterp.lean. VeIR still assumes this rule.
axiom interp {RR}
  (h : (i : EIn) → CTree F C (E i))
  (preservesUB : ∀ i, UBE.isUB i → CTree.UB (UB := UBF) (h i))
  (t : CTree E C α) (u : CTree E C β) :
  Sim RR t u →
  Sim RR (CTree.interp h t) (CTree.interp h u)

/--
Product of two relations
-/
@[expose]
def ProdRel {A B C D} (RR : A → B → Prop) (RS : C → D → Prop) :
    A × C → B × D → Prop :=
  fun (x, σ) (y, σ') => RR x y ∧ RS σ σ'

axiom interp_state {RR RR'} {RS : σ → σ → Prop}
    (h : (i : EIn) → StateT σ (CTree F C) (E i)) (t : CTree E C α) (u : CTree E C β) :
  ProdRel RR RS ⊑ RR' →
  RS s s' →
  Sim RR t u →
  Sim RR' (CTree.interp_state h t s) (CTree.interp_state h u s')

end Sim

end CTree
