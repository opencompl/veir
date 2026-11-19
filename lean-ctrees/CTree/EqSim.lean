module

public import CTree.Sim

public section

namespace CTree
open Coinductive Lean.Order Tower

variable {EIn FIn CIn C'In DIn X Y X' Y' : Type u}
  {E : EIn → Type u} {F : FIn → Type u} {C : CIn → Type u} {C' : C'In → Type u} {D : DIn → Type u}
  {R R' : Type u} (RR : R → R' → Prop)

/-- Two event responses agree on both the event index and its dependent value. -/
@[expose]
def EventEq (E : EIn → Type u) (i j : EIn) (x : E i) (y : E j) : Prop :=
  (⟨i, x⟩ : Sigma E) = ⟨j, y⟩

instance (i : EIn) : Std.Refl (EventEq E i i) := ⟨fun _ => rfl⟩

/-- Simulation matching visible events exactly, with a user-supplied return relation. -/
@[expose]
def EqSim [HasUB EIn] (RR : R → R' → Prop) (t : CTree E C R) (u : CTree E C' R') : Prop :=
  Sim (EventEq E) RR t u

namespace EqSim

variable [UB : HasUB EIn] [HasUB FIn]

theorem refl (RR : R → R → Prop) (hrefl : ∀ value, RR value value) (t : CTree E C R) :
    EqSim RR t t :=
  Sim.refl (EventEq E) RR hrefl t

@[simp]
theorem ret (r : R) (r' : R') :
  EqSim RR (CTree.ret (E := E) (C := C) r) (CTree.ret (C := C') r') ↔
  RR r r' :=
  Sim.ret (EventEq E) RR r r'

@[simp, grind =]
theorem pure (r : R) (r' : R') :
    EqSim (C := C) (C' := C') (E := E) RR (pure r) (pure r') ↔ RR r r' :=
  Sim.pure (EventEq E) RR r r'

@[simp]
theorem tau_l (i : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) i → CTree E C R) (u : CTree E C' R') :
  EqSim RR (CTree.tauG i k) u ↔
  ∀ x, EqSim RR (k x) u :=
  Sim.tau_l_proof (EventEq E) RR i k u

theorem tau_r (i' : C1In ⊕ C'In) (t : CTree E C R) (k' : (C1 ⊕ₑ C') i' → CTree E C' R') x :
  EqSim RR t (k' x) →
  EqSim RR t (CTree.tauG i' k') :=
  Sim.tau_r (EventEq E) RR i' t k' x

@[simp]
theorem pure_tau (r : R) (i' : C1In ⊕ C'In)
    (k' : (C1 ⊕ₑ C') i' → CTree E C' R') :
    EqSim RR (Pure.pure (f := CTree E C) r) (CTree.tauG i' k') ↔
    ∃ x, EqSim RR (Pure.pure (f := CTree E C) r) (k' x) :=
  Sim.pure_tau_proof (EventEq E) RR r i' k'

@[simp]
theorem pure_bind_choose_iff
  {SubCIn : Type u} {SubC : SubCIn → Type u} [SubC -< C']
  (value : R) (choice : SubCIn) (after : SubC choice → CTree E C' R') :
    CTree.EqSim RR (Pure.pure value : CTree E C R)
        (CTree.bind (CTree.choose choice) after) ↔
      ∃ chosen, CTree.EqSim RR (Pure.pure value : CTree E C R) (after chosen) :=
  Sim.pure_bind_choose_iff (EventEq E) RR value choice after

theorem tau (i : C1In ⊕ CIn) (i' : C1In ⊕ C'In) (k : (C1 ⊕ₑ C) i → CTree E C R) (k' : (C1 ⊕ₑ C') i' → CTree E C' R') :
  (∀ x, ∃ y, EqSim RR (k x) (k' y)) →
  EqSim RR (CTree.tauG i k) (CTree.tauG i' k') :=
  Sim.tau (EventEq E) RR i i' k k'

theorem tau_id (i : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) i → CTree E C R) (k' : (C1 ⊕ₑ C) i → CTree E C R') :
  (∀ x, EqSim RR (k x) (k' x)) →
  EqSim RR (CTree.tauG i k) (CTree.tauG i k') :=
  Sim.tau_id (EventEq E) RR i k k'

theorem vis (i : EIn) [Inhabited (E i)] (k : E i → CTree E C R) (k' : E i → CTree E C' R') :
  (∀ x, EqSim RR (k x) (k' x)) →
  EqSim RR (CTree.vis i k) (CTree.vis i k') :=
  Sim.vis (EventEq E) RR i k k'

theorem ub {t : CTree E C R} (e : EIn) {k : E e → CTree E C' R'} :
  @HasUB.isUB _ UB e →
  EqSim RR t (CTree.vis e k) :=
  Sim.ub (EventEq E) RR e

theorem bind {RR RR'} (t : CTree E C X) (u : CTree E C' X') (k : X → CTree E C Y) (k' : X' → CTree E C' Y') :
  EqSim RR t u →
  (∀ x y, RR x y → EqSim RR' (k x) (k' y)) →
  EqSim RR' (bind t k) (bind u k') :=
  Sim.bind_proof (EventEq E) t u k k'

theorem mono {RR RS : R → R' → Prop} {t : CTree E C R} {u : CTree E C' R'}
    (h : EqSim RR t u) (hrel : ∀ x y, RR x y → RS x y) : EqSim RS t u :=
  Sim.mono (EventEq E) h hrel

theorem trans_rel {R₁ R₂ R₃ : Type u} {RS : R₁ → R₂ → Prop} {RT : R₂ → R₃ → Prop}
    {t : CTree E C R₁} {u : CTree E C' R₂} {v : CTree E D R₃} :
    EqSim RS t u → EqSim RT u v →
    EqSim (fun x z => ∃ y, RS x y ∧ RT y z) t v := by
  intro h₁ h₂
  have preserves : ∀ i j (x : E i) (y : E j), EventEq E i j x y → UB.isUB i → UB.isUB j := by
    intro i j x y h
    rw [(Sigma.mk.inj h).1]
    exact id
  have composed := Sim.trans_rel_proof (EventEq E) (EventEq E) preserves preserves h₁ h₂
  have eqRel : (fun i k (x : E i) (z : E k) =>
      ∃ (j : EIn) (y : E j), EventEq E i j x y ∧ EventEq E j k y z) = EventEq E := by
    funext i k x z
    apply propext
    exact ⟨fun ⟨_, _, h, h'⟩ => h.trans h', fun h => ⟨i, x, rfl, h⟩⟩
  rwa [eqRel] at composed

theorem trans {R₁ R₂ R₃ : Type u} {RS : R₁ → R₂ → Prop} {RT : R₂ → R₃ → Prop}
    {RU : R₁ → R₃ → Prop} {t : CTree E C R₁} {u : CTree E C' R₂} {v : CTree E D R₃}
    (htu : EqSim RS t u) (huv : EqSim RT u v)
    (hrel : ∀ x y z, RS x y → RT y z → RU x z) : EqSim RU t v := by
  apply mono (trans_rel htu huv)
  rintro x z ⟨y, hxy, hyz⟩
  exact hrel x y z hxy hyz

theorem iter {I I'} {RRi : I → I' → Prop} {RRo : X → Y → Prop}
    (body : I → CTree E C (I ⊕ X)) (body' : I' → CTree E C (I' ⊕ Y)) i i' :
  RRi i i' →
  (∀ x y, RRi x y → EqSim (Sum.LiftRel RRi RRo) (body x) (body' y)) →
  EqSim (R' := Y) RRo (CTree.iter body i) (CTree.iter (X := Y) body' i') :=
  Sim.iter (EventEq E) body body' i i'

/-- The interpreter congruence assumed by VeIR. This also assumes congruence for
handlers that can erase UB events. -/
axiom interp {RR : X → Y → Prop} (h : (i : EIn) → CTree F C (E i))
    (t : CTree E C X) (u : CTree E C Y) :
    EqSim RR t u → EqSim RR (CTree.interp h t) (CTree.interp h u)

end EqSim

end CTree
