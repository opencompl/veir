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

theorem MuSimF.ret (r : α) (r' : β) :
  RR r r' →
  MuSimF RR Rel true (CTree.ret (E := E) (C := C) r) (CTree.ret (C := C') r') := by
  intro h
  apply LTS.MuSimF.sim
  constructor
  case left =>
    intros l s' htr
    have htr := trans_ret htr
    cases htr
    exists (.obs $ CTree.Obs.val r')
    exists (CTree.ret r')
    constructor
    · apply Star.skip_l
      constructor
    · constructor
      constructor
      constructor
      assumption
      have htr := trans_ret' htr
      sorry
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
  apply MuSimF.ret <;> assumption

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

theorem MuSimF.vis (i : EIn) [Inhabited (E i)] (k : E i → CTree E C α) (k' : E i → CTree E C' β) :
    (∀ x, R.elem true (k x) (k' x)) →
    MuSimF RR R.elem true (CTree.vis i k) (CTree.vis i k') := by
  intros h
  apply MuSimF.sim
  constructor
  case left =>
    intros l t htr
    have htr := trans_vis htr
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
    have htr := trans_vis htr
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

axiom MuSimF.bind {RR'} (t : CTree E C α') (u : CTree E C' β') (k : α' → CTree E C α) (k' : β' → CTree E C' β) :
    Sim RR' t u →
    (∀ x y, RR' x y → R.elem true (k x) (k' y)) →
    R.elem true (bind t k) (bind u k')

axiom MuSimF.bind' {RR'} (t : CTree E C α') (u : CTree E C' β') (k : α' → CTree E C α) (k' : β' → CTree E C' β) :
    Sim RR' t u →
    (∀ x y, RR' x y → MuSimF RR R.elem true (k x) (k' y)) →
    MuSimF RR R.elem true (CTree.bind t k) (CTree.bind u k')

namespace Sim

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
    Sim (C := C) (C' := C') (E := E) RR (pure r) (pure r') ↔ RR r r' := by
  simp only [Pure.pure, ret]

@[simp]
axiom tau_l (i : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) i → CTree E C α) (u : CTree E C' β) :
  Sim RR (CTree.tauG i k) u ↔
  ∀ x, Sim RR (k x) u

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
axiom pure_tau (r : α) (i' : C1In ⊕ C'In)
    (k' : (C1 ⊕ₑ C') i' → CTree E C' β) :
    Sim RR (Pure.pure (f := CTree E C) r) (CTree.tauG i' k') ↔
    ∃ x, Sim RR (Pure.pure (f := CTree E C) r) (k' x)

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

axiom bind {RR RR'} (t : CTree E C α) (u : CTree E C' α') (k : α → CTree E C β) (k' : α' → CTree E C' β') :
  Sim RR t u →
  (∀ x y, RR x y → Sim RR' (k x) (k' y)) →
  Sim RR' (bind t k) (bind u k')

/-- Simulations compose by relating their return values through an intermediate outcome. -/
axiom trans_rel {R₁ R₂ R₃ : Type u} {RS : R₁ → R₂ → Prop} {RT : R₂ → R₃ → Prop}
    {t : CTree E C R₁} {u : CTree E C' R₂} {v : CTree E D R₃} :
    Sim RS t u → Sim RT u v →
    Sim (fun x z => ∃ y, RS x y ∧ RT y z) t v

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

axiom interp {RR} (h : (i : EIn) → CTree F C (E i)) (t : CTree E C α) (u : CTree E C β) :
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
