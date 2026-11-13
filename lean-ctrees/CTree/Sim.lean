module

public import CTree.Order
public import CTree.Defs
public import CTree.UB
public import CTree.Iter
public import CTree.Interp
public import CTree.CTreeLTS

public section

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
    -- FIXME lean bug
    -- cases h
    sorry
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

axiom bind {RR RR'} (t : CTree E C α) (u : CTree E C' α') (k : α → CTree E C β) (k' : α' → CTree E C' β') :
  Sim RE RR t u →
  (∀ x y, RR x y → Sim RE RR' (k x) (k' y)) →
  Sim RE RR' (bind t k) (bind u k')

/-- Simulations compose by relating their return values through an intermediate outcome. -/
axiom trans_rel (hRE : ∀ i i' x y, RE i i' x y → UBE.isUB i → UBE.isUB i')
    (hRF : ∀ i i' x y, RF i i' x y → UBE.isUB i → UBE.isUB i')
    {R₁ R₂ R₃ : Type u} {RS : R₁ → R₂ → Prop} {RT : R₂ → R₃ → Prop}
    {t : CTree E C R₁} {u : CTree E C' R₂} {v : CTree E D R₃} :
    Sim RE RS t u → Sim RF RT u v →
    Sim (fun i i'' x z => ∃ (i' : EIn) (y : E i'), RE i i' x y ∧ RF i' i'' y z) (fun x z => ∃ y, RS x y ∧ RT y z) t v

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
