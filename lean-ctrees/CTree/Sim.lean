module

public import CTree.Order
public import CTree.Defs
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
axiom Sim (RR : R → R' → Prop) (t : CTree E C R) (u : CTree E C' R') : Prop

namespace Sim

axiom ret (r : R) (r' : R') :
  RR r r' →
  Sim RR (CTree.ret (E := E) (C := C) r) (CTree.ret (C := C') r')

axiom tau_l (i : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) i → CTree E C R) (u : CTree E C' R') :
  (∀ x, Sim RR (k x) u) →
  Sim RR (CTree.tauG i k) u

axiom tau_r (i' : C1In ⊕ C'In) (t : CTree E C R) (k' : (C1 ⊕ₑ C') i' → CTree E C' R') x :
  Sim RR t (k' x) →
  Sim RR t (CTree.tauG i' k')

axiom tau (i : C1In ⊕ CIn) (i' : C1In ⊕ C'In) (k : (C1 ⊕ₑ C) i → CTree E C R) (k' : (C1 ⊕ₑ C') i' → CTree E C' R') :
  (∀ x, ∃ y, Sim RR (k x) (k' y)) →
  Sim RR (CTree.tauG i k) (CTree.tauG i' k')

axiom tau_id (i : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) i → CTree E C R) (k' : (C1 ⊕ₑ C) i → CTree E C R') :
  (∀ x, Sim RR (k x) (k' x)) →
  Sim RR (CTree.tauG i k) (CTree.tauG i k')

axiom vis (i : EIn) [Inhabited (E i)] (k : E i → CTree E C R) (k' : E i → CTree E C' R') :
  (∀ x, Sim RR (k x) (k' x)) →
  Sim RR (CTree.vis i k) (CTree.vis i k')

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

