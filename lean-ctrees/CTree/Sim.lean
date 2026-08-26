module

public import CTree.Definition
public import CTree.Iter
public import CTree.Interp

public section

namespace CTree
open Coinductive Lean.Order

variable {EIn FIn CIn C'In DIn X Y : Type u} {E : EIn → Type u} {F : FIn → Type u} {C : CIn → Type u} {C' : C'In → Type u} {D : DIn → Type u} {R R' : Type u} (RR : R → R' → Prop)

def sim (t : CTree E C R) (u : CTree E C' R') : Prop := let _ := RR; sorry

theorem sim_ret (r : R) (r' : R') :
  RR r r' →
  sim RR (CTree.ret (E := E) (C := C) r) (CTree.ret (C := C') r') := sorry

theorem sim_tau (i : CIn) (i' : C'In) (k : C i → CTree E C R) (k' : C' i' → CTree E C' R') :
  (∀ x, ∃ y, sim RR (k x) (k' y)) →
  sim RR (CTree.tau i k) (CTree.tau i' k') := sorry

-- this is not divergence-sensitive yet
theorem sim_tau_l (i : CIn) (k : C i → CTree E C R) (u : CTree E C' R') :
  (∀ x, sim RR (k x) u) →
  sim RR (CTree.tau i k) u := sorry

theorem sim_tau_r (i' : C'In) (t : CTree E C R) (k' : C' i' → CTree E C' R') x :
  sim RR t (k' x) →
  sim RR t (CTree.tau i' k') := sorry

theorem sim_vis (i : EIn) (k : E i → CTree E C R) (k' : E i → CTree E C R') :
  (∀ x, sim RR (k x) (k' x)) →
  sim RR (CTree.vis i k) (CTree.vis i k') := sorry

-- stated only in the homogeneous case for now
theorem sim_bind {RR RR'} (t : CTree E C X) (u : CTree E C' X) (k : X → CTree E C Y) (k' : X → CTree E C' Y) :
  sim RR t u →
  (∀ x y, RR x y → sim RR' (k x) (k' x)) →
  sim RR' (bind t k) (bind u k') := sorry

theorem sim_iter {I I'} {RRi : I → I' → Prop} {RRo : X → Y → Prop} {RR} (body : I → CTree E C (I ⊕ X)) (body' : I' → CTree E C (I' ⊕ Y)) i i' :
  RRi i i' →
  (∀ x y, RRi x y → sim RR (body x) (body' y)) →
  sim (R' := Y) RRo (CTree.iter body i) (CTree.iter (X := Y) body' i') := sorry

-- stated only in the homogeneous case for now
theorem sim_interp {RR} (h : (i : EIn) → CTree F C (E i)) (t u : CTree E C X) :
    sim RR t u →
    sim RR (CTree.interp h t) (CTree.interp h u) := sorry

-- stated only in the homogeneous case for now
theorem sim_refine {RR} (h : (i : CIn) → CTree E D (C i)) (t u : CTree E C X) :
    sim RR t u →
    sim RR (CTree.refine h t) (CTree.refine h u) := sorry

end CTree

