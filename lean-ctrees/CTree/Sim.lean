module

public import CTree.Order
public import CTree.Defs
public import CTree.UB
public import CTree.Iter
public import CTree.Interp
public import CTree.CTreeLTS

public section

open scoped Tower

theorem LTS.MuSimF.true_iff {S S' : LTS}
    {Ro : S.observable → S'.observable → Prop} {UB : S'.state → Prop}
    {Rs : Bool → S.state → S'.state → Prop} {s : S.state} {t : S'.state} :
    MuSimF Ro UB Rs true s t ↔
      SimF Ro (Rs false) (Rs true) s t ∨
        ∃ tUB, (S'.trans .tau)^* t tUB ∧ UB tUB := by
  constructor
  · intro h
    cases h with
    | sim _ _ hs => exact Or.inl hs
    | ub _ _ tUB hu => exact Or.inr ⟨tUB, hu⟩
  · rintro (h | ⟨tUB, h⟩)
    · exact .sim _ _ h
    · exact .ub _ _ tUB h

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
  {α β : Type u} (RE RF : ∀ i i', E i → E i' → Prop) (RR : α → β → Prop)
  [UBE : HasUB EIn] [UBF : HasUB FIn]

abbrev MuSimF :
    (Bool → CTree E C α → CTree E C' β → Prop) → Bool → CTree E C α → CTree E C' β → Prop :=
  LTS.MuSimF (S := CTree.lts EIn CIn E C _) (S' := CTree.lts EIn C'In E C' _) (CTree.Robs @RE RR) (CTree.UB (UB := UBE))

abbrev MuSimF.mon := @LTS.MuSimF.mon

variable (R : Chain (MuSimF RE RR (UBE := UBE)))

@[grind =]
theorem MuSimF.def RE (RR : α → β → Prop) :
  MuSimF RE RR = LTS.MuSimF (S := CTree.lts EIn CIn E C _) (S' := CTree.lts EIn C'In E C' _)
    (CTree.Robs @RE RR) (CTree.UB (UB := UBE)) := by
  rfl

theorem MuSimF.refl RE (RR : α → α → Prop) [hRE : ∀ i, Std.Refl (@RE i i)] [hRR : Std.Refl RR] (R : Chain (MuSimF RE RR)) (t : CTree E C α) :
    R.elem b t t := by
  apply LTS.MuSimF.refl
  apply CTree.instReflObsRobs

theorem MuSimF.empty :
    MuSimF (UBE := UBE) RE RR Rel true .empty t := by
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

theorem MuSimF.empty' (R : Chain (MuSimF RE RR)) (t : CTree E C' β) :
    R.elem true (CTree.empty : CTree E C α) t := by
  apply Chain.apply_ternary_rel
  apply MuSimF.mon
  apply MuSimF.empty

theorem MuSimF.ret (r : α) (r' : β) :
  RR r r' →
  Rel true .empty .empty →
  MuSimF RE RR Rel true (CTree.ret (E := E) (C := C) r) (CTree.ret (C := C') r') := by
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

theorem MuSimF.ret' (R : Chain (MuSimF RE RR)) (r : α) (r' : β) :
  RR r r' →
  R.elem true (CTree.ret (E := E) (C := C) r) (CTree.ret (C := C') r') := by
  intros h
  apply Chain.apply_ternary_rel
  apply MuSimF.mon
  apply MuSimF.ret <;> try assumption
  apply Chain.apply (f := MuSimF _ _)
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
    MuSimF RE RR R.elem true (CTree.tauG i k) (CTree.tauG i' k') := by
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
    MuSimF RE RR R.elem true (CTree.tau1 t) (CTree.tau1 u) := by
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

theorem MuSimF.vis' (i i' : EIn) [inh : Inhabited (E i)] (k : E i → CTree E C α) (k' : E i' → CTree E C' β) :
    (∀ x : E i, ∃ y : E i', RE i i' x y ∧ R.elem true (k x) (k' y)) →
    MuSimF RE RR R.elem true (CTree.vis i k) (CTree.vis i' k') := by
  intros h
  apply MuSimF.sim
  constructor
  case left =>
    intros l t htr
    have htr := trans_vis _ _ _ _ htr
    rcases htr with ⟨o, htr⟩
    cases htr
    rcases h o with ⟨o', hRE, hR⟩
    exists (.obs (.eff i' o'))
    exists (k' o')
    constructor
    case left =>
      apply Star.skip_l
      constructor
    case right =>
      constructor
      constructor
      constructor
      apply hRE
      have htr := trans_vis' htr
      grind
  case right =>
    intros t' htr
    have htr := trans_vis _ _ _ _ htr
    grind

theorem MuSimF.vis (i : EIn) [inh : Inhabited (E i)] [hRE : ∀ i, Std.Refl (@RE i i)] (k : E i → CTree E C α) (k' : E i → CTree E C' β) :
    (∀ x, R.elem true (k x) (k' x)) →
    MuSimF RE RR R.elem true (CTree.vis i k) (CTree.vis i k') := by
  intros h
  apply vis'
  intros x
  exists x
  constructor
  · apply (hRE i).refl
  · apply h

theorem MuSimF.ub {t : CTree E C α} (e : EIn) {k : E e → CTree E C' β} :
    @HasUB.isUB _ UBE e →
    MuSimF RE RR R.elem true t (CTree.vis e k) := by
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
abbrev Sim (RE : (i i' : EIn) → E i → E i' → Prop) (RR : α → β → Prop) (t : CTree E C α) (u : CTree E C' β) : Prop :=
  LTS.Sim (S := CTree.lts EIn CIn E C _) (S' := CTree.lts EIn C'In E C' _) (CTree.Robs @RE RR) (CTree.UB (UB := UBE)) t u

axiom MuSimF.bind {RR'} (t : CTree E C α') (u : CTree E C' β') (k : α' → CTree E C α) (k' : β' → CTree E C' β) :
    Sim RE RR' t u →
    (∀ x y, RR' x y → R.elem true (k x) (k' y)) →
    R.elem true (bind t k) (bind u k')

theorem MuSimF.bind' {RR'} (t : CTree E C α') (u : CTree E C' β') (k : α' → CTree E C α) (k' : β' → CTree E C' β) :
    Sim RE RR' t u →
    (∀ x y, RR' x y → MuSimF RE RR R.elem true (k x) (k' y)) →
    MuSimF RE RR R.elem true (CTree.bind t k) (CTree.bind u k') := by
  apply MuSimF.bind (R := Chain.next (MuSimF RE RR) R)

namespace Sim

omit UBE in
private theorem tau_star_ret (r : α) {t : CTree E C α}
    (h : (CTree.Trans .tau)^* (CTree.ret r) t) : t = CTree.ret r := by
  cases h with
  | base => rfl
  | iter _ _ _ htr _ => cases trans_ret htr

/-- A tree simulates itself with any reflexive relation. -/
theorem refl [hRE : ∀ i, Std.Refl (@RE i i)] (RR : α → α → Prop) (hrefl : ∀ value, RR value value) (t : CTree E C α) :
    Sim RE RR t t := by
  unfold Sim LTS.Sim
  rw [gfp_iff_ternary_rel]
  intros R
  apply MuSimF.refl (t := t) (b := true) (hRR := ⟨hrefl⟩) (R := R)

@[simp]
theorem ret (r : α) (r' : β) :
    Sim RE RR (CTree.ret (E := E) (C := C) r) (CTree.ret (C := C') r') ↔
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
    Sim (C := C) (C' := C') (E := E) RE RR (pure r) (pure r') ↔ RR r r' := by
  simp only [Pure.pure, ret]

@[simp]
axiom tau_l (i : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) i → CTree E C α) (u : CTree E C' β) :
  Sim RE RR (CTree.tauG i k) u ↔
  ∀ x, Sim RE RR (k x) u

/-- Independent proof of `tau_l`, leaving the axiom unchanged. -/
theorem tau_l_proof (i : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) i → CTree E C α)
    (u : CTree E C' β) :
    Sim RE RR (CTree.tauG i k) u ↔ ∀ x, Sim RE RR (k x) u := by
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
    Sim RE RR t (k' x) →
    Sim RE RR t (CTree.tauG i' k') := by
  intros h
  unfold Sim LTS.Sim
  rw [gfp_iff_ternary_rel]
  intros R
  apply MuSimF.tau_r <;> try assumption
  revert R
  rw [← gfp_iff_ternary_rel]
  exact h

@[simp]
axiom pure_tau (r : α) (i' : C1In ⊕ C'In)
    (k' : (C1 ⊕ₑ C') i' → CTree E C' β) :
    Sim RE RR (Pure.pure (f := CTree E C) r) (CTree.tauG i' k') ↔
    ∃ x, Sim RE RR (Pure.pure (f := CTree E C) r) (k' x)

/-- Independent proof of `pure_tau`, leaving the axiom unchanged. -/
theorem pure_tau_proof (r : α) (i' : C1In ⊕ C'In)
    (k' : (C1 ⊕ₑ C') i' → CTree E C' β) :
    Sim RE RR (Pure.pure (f := CTree E C) r) (CTree.tauG i' k') ↔
      ∃ x, Sim RE RR (Pure.pure (f := CTree E C) r) (k' x) := by
  change Sim RE RR (CTree.ret r) (CTree.tauG i' k') ↔
    ∃ x, Sim RE RR (CTree.ret r) (k' x)
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
    exact tau_r RE RR i' (CTree.ret r) k' x hx

theorem tau (i : C1In ⊕ CIn) (i' : C1In ⊕ C'In) (k : (C1 ⊕ₑ C) i → CTree E C α) (k' : (C1 ⊕ₑ C') i' → CTree E C' β) :
  (∀ x, ∃ y, Sim RE RR (k x) (k' y)) →
  Sim RE RR (CTree.tauG i k) (CTree.tauG i' k') := by
  intro h
  apply (tau_l RE RR i k _).2
  intro x
  obtain ⟨y, hxy⟩ := h x
  exact tau_r RE RR i' (k x) k' y hxy

theorem tau_id (i : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) i → CTree E C α) (k' : (C1 ⊕ₑ C) i → CTree E C β) :
  (∀ x, Sim RE RR (k x) (k' x)) →
  Sim RE RR (CTree.tauG i k) (CTree.tauG i k') := by
  intros
  grind [tau]

theorem vis' (i i' : EIn) [inh : Inhabited (E i)] (k : E i → CTree E C α) (k' : E i' → CTree E C' β) :
    (∀ x : E i, ∃ y : E i', RE i i' x y ∧ Sim RE RR (k x) (k' y)) →
    Sim RE RR (CTree.vis i k) (CTree.vis i' k') := by
  intros h
  unfold Sim LTS.Sim
  rw [gfp_iff_ternary_rel]
  intros R
  apply Chain.apply_ternary_rel
  apply MuSimF.mon
  apply MuSimF.vis' <;> try assumption
  intros x
  rcases h x with ⟨y, h, h'⟩
  exists y
  constructor
  apply h
  revert R
  rw [← gfp_iff_ternary_rel]
  apply h'

theorem vis (i : EIn) [Inhabited (E i)] [hRE : ∀ i : EIn, Std.Refl (@RE i i)] (k : E i → CTree E C α) (k' : E i → CTree E C' β) :
    (∀ x, Sim RE RR (k x) (k' x)) →
    Sim RE RR (CTree.vis i k) (CTree.vis i k') := by
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
    Sim RE RR t (CTree.vis e k) := by
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

private theorem tau_star_right {t : CTree E C α} {u u' : CTree E C' β}
    (h : Sim RE RR t u') (hstar : (CTree.Trans .tau)^* u u') : Sim RE RR t u := by
  rw [Sim, LTS.Sim, gfp_iff_ternary_rel]
  intro R
  exact LTS.MuSimF.tau_star_r _ _ R _ _ _
    ((gfp_iff_ternary_rel _ _ _ _).mp h R) hstar

private theorem ret_bind_sim {α' β' : Type u} {RS : α → α' → Prop} {RT : β → β' → Prop}
    (r : α) (u : CTree E C' α') (k : α → CTree E C β) (k' : α' → CTree E C' β')
    (h : Sim RE RS (CTree.ret (C := C) r) u)
    (hk : ∀ x y, RS x y → Sim RE RT (k x) (k' y)) :
    Sim RE RT (k r) (CTree.bind u k') := by
  have h := gfp_apply_ternary_rel _ _ _ _ h
  rcases LTS.MuSimF.true_iff.mp h with hs | hu
  · obtain ⟨l', t', ⟨mid, hstar, hstep⟩, hlbl, _⟩ :=
      hs.1 (.val r) CTree.empty CTree.Trans.ret
    cases hlbl with
    | obs _ _ hobs =>
      cases hobs with
      | val _ y hrel =>
        cases hstep
        apply tau_star_right RE RT (hk r y hrel)
        simpa only [CTree.bind_ret] using star_bind_tau k' hstar
  · obtain ⟨tUB, hu⟩ := bind_reaches_ub k' hu
    exact LTS.MuSimF.fold_gfp (.ub _ _ tUB hu)

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

/-- If the bound target has well-founded tau paths and cannot reach UB, the
source has well-founded tau paths both before and after its continuation. -/
private theorem acc_bind_of_sim {α' β' : Type u} {RS : α → α' → Prop} {RT : β → β' → Prop}
    (t : CTree E C α) (u : CTree E C' α') (k : α → CTree E C β) (k' : α' → CTree E C' β')
    (h : Sim RE RS t u) (hk : ∀ x y, RS x y → Sim RE RT (k x) (k' y))
    (hno : ¬ ∃ tUB, (CTree.Trans .tau)^* (CTree.bind u k') tUB ∧ CTree.UB tUB)
    (hu : Acc (fun x y => CTree.Trans .tau y x) (CTree.bind u k')) :
    Acc (fun x y => CTree.Trans .tau y x) (CTree.bind t k) := by
  have ht : Acc (fun x y => CTree.Trans .tau y x) t :=
    LTS.MuSimF.acc_of_sim (fun h => hno (bind_reaches_ub k' h)) (acc_of_bind_acc k' u hu) h
  induction ht with
  | intro t ht ih =>
    cases t with
    | ret r =>
      rw [bind_pure]
      exact LTS.MuSimF.acc_of_sim hno hu (ret_bind_sim RE r u k k' h hk)
    | tau i ks =>
      rw [CTree.bind_tau]
      constructor
      intro s' htr
      obtain ⟨x, rfl⟩ := trans_tau' htr
      exact ih (ks x) CTree.Trans.tau ((tau_l_proof RE RS i ks u).mp h x)
    | vis i ks =>
      rw [CTree.bind_vis]
      constructor
      intro s' htr
      rcases trans_vis_cases htr with ⟨x, hx, _⟩ | ⟨_, hx, _⟩ <;> cases hx

private theorem bind_div_chain {α' β' : Type u} {RS : α → α' → Prop} {RT : β → β' → Prop}
    (R : Chain (MuSimF RE RT)) (t : CTree E C α) (u : CTree E C' α')
    (k : α → CTree E C β) (k' : α' → CTree E C' β') (h : Sim RE RS t u)
    (hk : ∀ x y, RS x y → Sim RE RT (k x) (k' y))
    (hno : ¬ ∃ tUB, (CTree.Trans .tau)^* (CTree.bind u k') tUB ∧ CTree.UB tUB) :
    R.elem false (CTree.bind t k) (CTree.bind u k') := by
  classical
  by_cases hu : Acc (fun x y => CTree.Trans .tau y x) (CTree.bind u k')
  · exact LTS.MuSimF.div_of_acc R _ (acc_bind_of_sim RE t u k k' h hk hno hu)
  · exact LTS.MuSimF.div_of_not_acc _ _ R _ _ hu

axiom bind {RR RR'} (t : CTree E C α) (u : CTree E C' α') (k : α → CTree E C β) (k' : α' → CTree E C' β') :
  Sim RE RR t u →
  (∀ x y, RR x y → Sim RE RR' (k x) (k' y)) →
  Sim RE RR' (bind t k) (bind u k')

/-- Independent proof of `bind`, leaving the axiom unchanged. -/
theorem bind_proof {α' β' : Type u} {RS : α → α' → Prop} {RT : β → β' → Prop}
    (t : CTree E C α) (u : CTree E C' α') (k : α → CTree E C β) (k' : α' → CTree E C' β')
    (h : Sim RE RS t u) (hk : ∀ x y, RS x y → Sim RE RT (k x) (k' y)) :
    Sim RE RT (CTree.bind t k) (CTree.bind u k') := by
  rw [Sim, LTS.Sim, gfp_iff_ternary_rel]
  intro R
  revert t u h
  revert R
  apply tower_ind (f := MuSimF RE RT) (P := fun R => ∀ t u,
    Sim RE RS t u → R true (CTree.bind t k) (CTree.bind u k'))
  · intro P ih t u h
    rw [inf_iff_ternary_rel]
    intro R hR
    exact ih R hR t u h
  · intro R ih t u h
    classical
    by_cases hUB : ∃ tUB, (CTree.Trans .tau)^* (CTree.bind u k') tUB ∧ CTree.UB tUB
    · obtain ⟨tUB, hUB⟩ := hUB
      exact LTS.MuSimF.ub _ _ tUB hUB
    have hs := gfp_apply_ternary_rel _ _ _ _ h
    rcases LTS.MuSimF.true_iff.mp hs with hs | hu
    · cases t with
      | ret r =>
        rw [bind_pure]
        exact (gfp_iff_ternary_rel _ _ _ _).mp
          (ret_bind_sim RE r u k k' h hk) (Chain.next _ R)
      | tau i ks =>
        rw [CTree.bind_tau]
        apply LTS.MuSimF.sim
        constructor
        · intro l s' htr
          cases trans_tau htr
        · intro s' htr
          obtain ⟨x, rfl⟩ := trans_tau' htr
          rcases hs.2 (ks x) CTree.Trans.tau with ⟨ht, _⟩ | ⟨u', ⟨mid, hstep, hstar⟩, ht⟩
          · exact Or.inl ⟨ih (ks x) u ht, bind_div_chain RE R (ks x) u k k' ht hk hUB⟩
          · right
            refine ⟨CTree.bind u' k', ⟨CTree.bind mid k', trans_bind_tau k' hstep,
              star_bind_tau k' hstar⟩, ih (ks x) u' ht⟩
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
              | eff _ j _ y hRE =>
                exact ⟨.obs (.eff j y), CTree.bind u' k',
                  ⟨CTree.bind mid k', star_bind_tau k' hstar, trans_bind_eff k' hstep⟩,
                  .obs _ _ (.eff _ _ _ _ hRE), ih (ks x) u' hR⟩
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
                simpa only [bind_empty] using ih CTree.empty u' hR
        · intro s' htr
          rcases trans_vis_cases htr with ⟨x, hx, _⟩ | ⟨_, hx, _⟩ <;> cases hx
    · exact (hUB (bind_reaches_ub k' hu)).elim

private theorem ret_bind_chain {α' β' : Type u} {RS : α → α' → Prop} {RT : β → β' → Prop}
    (R : Chain (MuSimF RE RT)) (r : α) (u : CTree E C' α')
    (k : α → CTree E C β) (k' : α' → CTree E C' β')
    (h : Sim RE RS (CTree.ret (C := C) r) u)
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
    (R : Chain (MuSimF RE RT)) (t : CTree E C α) (u : CTree E C' α')
    (k : α → CTree E C β) (k' : α' → CTree E C' β') (h : Sim RE RS t u)
    (hk : ∀ x y, RS x y → MuSimF RE RT R.elem true (k x) (k' y))
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
        exact ret_bind_chain RE (Chain.next _ R) r u k k' h hk
      | tau i ks =>
        rw [CTree.bind_tau]
        apply LTS.MuSimF.div_tau_closed _ _ R
        intro s' htr
        obtain ⟨x, rfl⟩ := trans_tau' htr
        exact ih (ks x) CTree.Trans.tau ((tau_l_proof RE RS i ks u).mp h x)
      | vis i ks =>
        rw [CTree.bind_vis]
        apply LTS.MuSimF.div_tau_closed _ _ R
        intro s' htr
        rcases trans_vis_cases htr with ⟨x, hx, _⟩ | ⟨_, hx, _⟩ <;> cases hx
  · exact LTS.MuSimF.div_of_not_acc _ _ R _ _ hu

/-- Independent proof of the corrected `MuSimF.bind` statement. -/
theorem _root_.CTree.MuSimF.bind_proof {α' β' : Type u} {RS : α' → β' → Prop}
    (t : CTree E C α') (u : CTree E C' β') (k : α' → CTree E C α) (k' : β' → CTree E C' β)
    (h : Sim RE RS t u) (hk : ∀ x y, RS x y → R.elem true (k x) (k' y)) :
    R.elem true (CTree.bind t k) (CTree.bind u k') := by
  revert t u h hk
  revert R
  apply tower_ind (f := MuSimF RE RR) (P := fun R => ∀ t u,
    Sim RE RS t u → (∀ x y, RS x y → R true (k x) (k' y)) →
      R true (CTree.bind t k) (CTree.bind u k'))
  · intro P ih t u h hk
    rw [inf_iff_ternary_rel]
    intro Q hQ
    apply ih Q hQ t u h
    intro x y hxy
    exact (inf_iff_ternary_rel _ _ _ _).mp (hk x y hxy) Q hQ
  · intro R ih t u h hk
    have hk' : ∀ x y, RS x y → R.elem true (k x) (k' y) := by
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
        exact ret_bind_chain RE (Chain.next _ R) r u k k' h hk
      | tau i ks =>
        rw [CTree.bind_tau]
        apply LTS.MuSimF.sim
        constructor
        · intro l s' htr
          cases trans_tau htr
        · intro s' htr
          obtain ⟨x, rfl⟩ := trans_tau' htr
          rcases hs.2 (ks x) CTree.Trans.tau with ⟨ht, _⟩ | ⟨u', ⟨mid, hstep, hstar⟩, ht⟩
          · exact Or.inl ⟨ih (ks x) u ht hk', bind_div_next RE R (ks x) u k k' ht hk hUB⟩
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
              | eff _ j _ y hRE =>
                exact ⟨.obs (.eff j y), CTree.bind u' k',
                  ⟨CTree.bind mid k', star_bind_tau k' hstar, trans_bind_eff k' hstep⟩,
                  .obs _ _ (.eff _ _ _ _ hRE), ih (ks x) u' hR hk'⟩
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

private theorem tau_step_left {t t' : CTree E C α} {u : CTree E C' β}
    (h : Sim RE RR t u) (htr : CTree.Trans .tau t t') : Sim RE RR t' u := by
  cases htr
  exact (tau_l_proof RE RR _ _ u).mp h _

private theorem tau_star_left {t t' : CTree E C α} {u : CTree E C' β}
    (h : Sim RE RR t u) (htr : (CTree.Trans .tau)^* t t') : Sim RE RR t' u := by
  induction htr with
  | base => exact h
  | iter _ _ _ hstep _ ih => exact ih (tau_step_left RE RR h hstep)

/-- A UB-preserving effect relation transports reachable UB across simulation. -/
private theorem ub_reaches_of_sim
    (hRE : ∀ i i' x y, RE i i' x y → UBE.isUB i → UBE.isUB i')
    {t : CTree E C α} {u : CTree E C' β} (h : Sim RE RR t u)
    (hu : ∃ tUB, (CTree.Trans .tau)^* t tUB ∧ CTree.UB tUB) :
    ∃ uUB, (CTree.Trans .tau)^* u uUB ∧ CTree.UB uUB := by
  obtain ⟨tUB, hstar, hUB⟩ := hu
  have hs := tau_star_left RE RR h hstar
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
          | eff _ j _ y hrel =>
            cases hstep
            refine ⟨_, hstar, ?_⟩
            simp only [CTree.UB, unfold_vis]
            exact hRE i j x y hrel hUB
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
    (h : CTree.Robs @RE RS x y) (h' : CTree.Robs @RF RT y z) :
    CTree.Robs (fun {i k} x z => ∃ (j : EIn) (y : E j), RE i j x y ∧ RF j k y z)
      (fun x z => ∃ y, RS x y ∧ RT y z) x z := by
  cases h with
  | eff i j x y hRE =>
    cases h' with
    | eff _ k _ z hRF => exact .eff _ _ _ _ ⟨j, y, hRE, hRF⟩
  | effEmpty i =>
    cases h'
    exact .effEmpty i
  | val x y hRS =>
    cases h' with
    | val _ z hRT => exact .val _ _ ⟨y, hRS, hRT⟩

private theorem trans_div_chain
    {R₁ R₂ R₃ : Type u} {RS : R₁ → R₂ → Prop} {RT : R₂ → R₃ → Prop}
    (hRF : ∀ i i' x y, RF i i' x y → UBE.isUB i → UBE.isUB i')
    (R : Chain (MuSimF (C := C) (C' := D)
      (fun i k x z => ∃ (j : EIn) (y : E j), RE i j x y ∧ RF j k y z)
      (fun x z => ∃ y, RS x y ∧ RT y z)))
    {t : CTree E C R₁} {u : CTree E C' R₂} {v : CTree E D R₃}
    (h : Sim RE RS t u) (h' : Sim RF RT u v)
    (hno : ¬ ∃ vUB, (CTree.Trans .tau)^* v vUB ∧ CTree.UB vUB) :
    R.elem false t v := by
  classical
  by_cases hv : Acc (fun x y => CTree.Trans .tau y x) v
  · have hnu : ¬ ∃ uUB, (CTree.Trans .tau)^* u uUB ∧ CTree.UB uUB :=
      fun hu => hno (ub_reaches_of_sim RF RT hRF h' hu)
    have hu := LTS.MuSimF.acc_of_sim hno hv h'
    exact LTS.MuSimF.div_of_acc R v (LTS.MuSimF.acc_of_sim hnu hu h)
  · exact LTS.MuSimF.div_of_not_acc _ _ R _ _ hv

/-- Simulations compose by relating their return values through an intermediate outcome. -/
axiom trans_rel (hRE : ∀ i i' x y, RE i i' x y → UBE.isUB i → UBE.isUB i')
    (hRF : ∀ i i' x y, RF i i' x y → UBE.isUB i → UBE.isUB i')
    {R₁ R₂ R₃ : Type u} {RS : R₁ → R₂ → Prop} {RT : R₂ → R₃ → Prop}
    {t : CTree E C R₁} {u : CTree E C' R₂} {v : CTree E D R₃} :
    Sim RE RS t u → Sim RF RT u v →
    Sim (fun i i'' x z => ∃ (i' : EIn) (y : E i'), RE i i' x y ∧ RF i' i'' y z) (fun x z => ∃ y, RS x y ∧ RT y z) t v

/-- Independent proof of `trans_rel`, leaving its axiom unchanged. -/
theorem trans_rel_proof (_hRE : ∀ i i' x y, RE i i' x y → UBE.isUB i → UBE.isUB i')
    (hRF : ∀ i i' x y, RF i i' x y → UBE.isUB i → UBE.isUB i')
    {R₁ R₂ R₃ : Type u} {RS : R₁ → R₂ → Prop} {RT : R₂ → R₃ → Prop}
    {t : CTree E C R₁} {u : CTree E C' R₂} {v : CTree E D R₃}
    (h : Sim RE RS t u) (h' : Sim RF RT u v) :
    Sim (fun i k x z => ∃ (j : EIn) (y : E j), RE i j x y ∧ RF j k y z)
      (fun x z => ∃ y, RS x y ∧ RT y z) t v := by
  rw [Sim, LTS.Sim, gfp_iff_ternary_rel]
  intro R
  revert t u v h h'
  revert R
  apply tower_ind (f := MuSimF
    (fun i k x z => ∃ (j : EIn) (y : E j), RE i j x y ∧ RF j k y z)
    (fun x z => ∃ y, RS x y ∧ RT y z)) (P := fun R => ∀ t u v,
      Sim RE RS t u → Sim RF RT u v → R true t v)
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
          have hm := tau_star_left RF RT h' hstar
          have hm := gfp_apply_ternary_rel _ _ _ _ hm
          rcases LTS.MuSimF.true_iff.mp hm with hm | hv
          · obtain ⟨n, v', ⟨mid', hstar', hstep'⟩, hlbl', hR'⟩ := hm.1 m u' hstep
            cases hlbl' with
            | obs _ n hobs' =>
              exact ⟨.obs n, v', ⟨mid', hstar', hstep'⟩,
                .obs _ _ (robs_comp RE RF hobs hobs'), ih t' u' v' hR hR'⟩
          · exact (hUB hv).elim
      · intro t' htr
        have ht := tau_step_left RE RS h htr
        exact Or.inl ⟨ih t' u v ht h', trans_div_chain RE RF hRF R ht h' hUB⟩
    · exact (hUB (ub_reaches_of_sim RF RT hRF h' hu)).elim

theorem iter {I I'} {RRi : I → I' → Prop} {RRo : α → β → Prop}
    (body : I → CTree E C (I ⊕ α)) (body' : I' → CTree E C (I' ⊕ β)) i i' :
    RRi i i' →
    (∀ x y, RRi x y → Sim RE (Sum.LiftRel RRi RRo) (body x) (body' y)) →
    Sim (β := β) RE RRo (CTree.iter body i) (CTree.iter (X := β) body' i') := by
  intros h h'
  unfold Sim LTS.Sim
  rw [gfp_iff_ternary_rel]
  intros R
  revert i i' h h'
  change Chain (MuSimF RE RRo (UBE := UBE)) at R
  revert R
  apply tower_ind (f := MuSimF RE RRo (UBE := UBE)) (P := fun R => ∀ i i', RRi i i' → (∀ x y, RRi x y → Sim RE (Sum.LiftRel RRi RRo) (body x) (body' y)) → R true (CTree.iter body i) (CTree.iter body' i'))
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

end Sim

end CTree
