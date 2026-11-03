module

public import CTree.Order
public import CTree.Defs
public import CTree.UB
public import CTree.Iter
public import CTree.Interp

public section

namespace CTree
open Coinductive Lean.Order Tower

variable {EIn FIn CIn C'In DIn X Y X' Y' : Type u}
  {E : EIn → Type u} {F : FIn → Type u} {C : CIn → Type u} {C' : C'In → Type u} {D : DIn → Type u}
  {R R' : Type u} (RR : R → R' → Prop)

/--
Simulation between ctrees: the rhs should have at least all
the behaviors of the lhs.
The simulation is parameterized by a relation on return values.
-/
axiom Sim [UB : HasUB EIn] (RR : R → R' → Prop) (t : CTree E C R) (u : CTree E C' R') : Prop

namespace Sim

variable [UB : HasUB EIn] [HasUB FIn]

/-- A tree simulates itself with any reflexive relation. -/
axiom refl (RR : R → R → Prop) (hrefl : ∀ value, RR value value) (t : CTree E C R) :
    Sim RR t t

@[simp]
axiom ret (r : R) (r' : R') :
  Sim RR (CTree.ret (E := E) (C := C) r) (CTree.ret (C := C') r') ↔
  RR r r'

@[simp, grind =]
theorem pure (r : R) (r' : R') :
    Sim (C := C) (C' := C') (E := E) RR (pure r) (pure r') ↔ RR r r' := by
  simp only [Pure.pure, ret]

@[simp]
axiom tau_l (i : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) i → CTree E C R) (u : CTree E C' R') :
  Sim RR (CTree.tauG i k) u ↔
  ∀ x, Sim RR (k x) u

axiom tau_r (i' : C1In ⊕ C'In) (t : CTree E C R) (k' : (C1 ⊕ₑ C') i' → CTree E C' R') x :
  Sim RR t (k' x) →
  Sim RR t (CTree.tauG i' k')

@[simp]
axiom pure_tau (r : R) (i' : C1In ⊕ C'In)
    (k' : (C1 ⊕ₑ C') i' → CTree E C' R') :
    Sim RR (Pure.pure (f := CTree E C) r) (CTree.tauG i' k') ↔
    ∃ x, Sim RR (Pure.pure (f := CTree E C) r) (k' x)

theorem tau (i : C1In ⊕ CIn) (i' : C1In ⊕ C'In) (k : (C1 ⊕ₑ C) i → CTree E C R) (k' : (C1 ⊕ₑ C') i' → CTree E C' R') :
  (∀ x, ∃ y, Sim RR (k x) (k' y)) →
  Sim RR (CTree.tauG i k) (CTree.tauG i' k') := by
  intro h
  apply (tau_l RR i k _).mpr
  intro x
  obtain ⟨y, hxy⟩ := h x
  exact tau_r RR i' (k x) k' y hxy

theorem tau_id (i : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) i → CTree E C R) (k' : (C1 ⊕ₑ C) i → CTree E C R') :
  (∀ x, Sim RR (k x) (k' x)) →
  Sim RR (CTree.tauG i k) (CTree.tauG i k') := by
  grind [tau]

axiom vis (i : EIn) [Inhabited (E i)] (k : E i → CTree E C R) (k' : E i → CTree E C' R') :
  (∀ x, Sim RR (k x) (k' x)) →
  Sim RR (CTree.vis i k) (CTree.vis i k')

axiom ub {t : CTree E C R} (e : EIn) {k : E e → CTree E C' R'} :
  @HasUB.isUB _ UB e →
  Sim RR t (CTree.vis e k)

axiom bind {RR RR'} (t : CTree E C X) (u : CTree E C' X') (k : X → CTree E C Y) (k' : X' → CTree E C' Y') :
  Sim RR t u →
  (∀ x y, RR x y → Sim RR' (k x) (k' y)) →
  Sim RR' (bind t k) (bind u k')

axiom iter {I I'} {RRi : I → I' → Prop} {RRo : X → Y → Prop}
    (body : I → CTree E C (I ⊕ X)) (body' : I' → CTree E C (I' ⊕ Y)) i i' :
  RRi i i' →
  (∀ x y, RRi x y → Sim (Sum.LiftRel RRi RRo) (body x) (body' y)) →
  Sim (R' := Y) RRo (CTree.iter body i) (CTree.iter (X := Y) body' i')

axiom interp {RR} (h : (i : EIn) → CTree F C (E i)) (t : CTree E C X) (u : CTree E C Y) :
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
    (h : (i : EIn) → StateT σ (CTree F C) (E i)) (t : CTree E C X) (u : CTree E C Y) :
  ProdRel RR RS ⊑ RR' →
  RS s s' →
  Sim RR t u →
  Sim RR' (CTree.interp_state h t s) (CTree.interp_state h u s')

end Sim

end CTree
