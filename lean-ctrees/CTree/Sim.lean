module

public import CTree.Defs
public import CTree.Iter
public import CTree.Interp

public section

namespace CTree
open Coinductive Lean.Order

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

/-- One matching layer of two trees. Recursive branches are related by `next`,
so each coinductive step consumes a constructor on both sides. -/
inductive Step (RR : R → R' → Prop)
    (next : CTree E C R → CTree E C R' → Prop) :
    CTreeF E C R (CTree E C R) → CTreeF E C R' (CTree E C R') → Prop where
  | ret {r r'} : RR r r' → Step RR next (.ret r) (.ret r')
  | tau {i k k'} : (∀ x, next (k x) (k' x)) → Step RR next (.tau i k) (.tau i k')
  | vis {i k k'} : (∀ x, next (k x) (k' x)) → Step RR next (.vis i k) (.vis i k')

/-- Lockstep coinduction is sufficient for simulation, including infinite trees.
Unlike one-sided silent-step introduction, every step here advances both trees. -/
axiom coinduct (next : CTree E C R → CTree E C R' → Prop)
    (step : ∀ t u, next t u → Step RR next t.unfold u.unfold)
    {t u} (h : next t u) : Sim RR t u

/-- Any reflexive return relation simulates a tree by itself, without a
termination assumption or restrictions on event response types. -/
theorem refl (RR : R → R → Prop) (hrefl : ∀ value, RR value value) (t : CTree E C R) :
    Sim RR t t := by
  apply coinduct RR Eq _ rfl
  intro t u h
  subst u
  cases hhead : t.unfold with
  | ret value => exact Step.ret (hrefl value)
  | tau i k => exact Step.tau (fun _ => rfl)
  | vis i k => exact Step.vis (fun _ => rfl)

@[simp]
axiom ret (r : R) (r' : R') :
  Sim RR (CTree.ret (E := E) (C := C) r) (CTree.ret (C := C') r') ↔
  RR r r'

@[simp, grind =]
theorem pure (r : R) (r' : R') :
    Sim (C := C) (C' := C') (E := E) RR (pure r) (pure r') ↔ RR r r' := by
  simp only [Pure.pure, ret]

/-- Every left-hand choice must be simulated; right-hand choices may depend on it. -/
@[simp]
axiom tau_l (i : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) i → CTree E C R) (u : CTree E C' R') :
  Sim RR (CTree.tauG i k) u ↔
  ∀ x, Sim RR (k x) u

axiom tau_r (i' : C1In ⊕ C'In) (t : CTree E C R) (k' : (C1 ⊕ₑ C') i' → CTree E C' R') x :
  Sim RR t (k' x) →
  Sim RR t (CTree.tauG i' k')

/-- A returned value has one behavior, so a single right-hand branch suffices.
For an arbitrary left-hand tree this is only an implication (`tau_r`): different
left-hand behaviors may need different right-hand branches. -/
@[simp]
axiom ret_tau_r (r : R) (i' : C1In ⊕ C'In)
    (k' : (C1 ⊕ₑ C') i' → CTree E C' R') :
  Sim RR (CTree.ret (C := C) r) (CTree.tauG i' k') ↔
  ∃ x, Sim RR (CTree.ret (C := C) r) (k' x)

@[simp]
theorem pure_tau_r (r : R) (i' : C1In ⊕ C'In)
    (k' : (C1 ⊕ₑ C') i' → CTree E C' R') :
    Sim RR (Pure.pure (f := CTree E C) r) (CTree.tauG i' k') ↔
    ∃ x, Sim RR (Pure.pure (f := CTree E C) r) (k' x) := by
  simpa only [Pure.pure] using ret_tau_r RR (C := C) r i' k'

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
  intro h
  exact tau RR i i k k' (fun x => ⟨x, h x⟩)

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

end Sim

end CTree
