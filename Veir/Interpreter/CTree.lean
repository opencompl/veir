module

public import CTree.Defs
import all CTree.Defs
public import CTree.Iter
public import CTree.Interp

public import Veir.Interpreter.Interp

public section

open CTree

/-!
  Infrastructure for CTree-based interpretation.

  A CTree-based interpreter can give semantics to effects, to nondeterminism and to non-termination.
-/

namespace Veir

/-- Effect representing an immediate undefined behavior -/
structure UBEIn : Type u where

/-- Effect representing an immediate undefined behavior -/
@[expose]
def UBE (e : UBEIn.{u}) :=
  match e with
  | .mk => Empty

/-- Emit an immediate undefined behavior -/
def ub {EIn CIn} {E : EIn → Type} {C : CIn → Type} {R} [UBE -< E] : CTree E C R := do
  let x ← CTree.trigger (SubE := UBE) UBEIn.mk
  by cases x

/-- Effect materializing an ill-formed program -/
structure ErrorEIn : Type u where

/-- Effect materializing an ill-formed program -/
@[expose]
def ErrorE (e : ErrorEIn.{u}) :=
  match e with
  | .mk => Empty

/-- Emit an effect materializing an ill-formed program -/
def fail {EIn CIn} {E : EIn → Type} {C : CIn → Type} {R} [ErrorE -< E] : CTree E C R := do
  let x ← CTree.trigger (SubE := ErrorE) ErrorEIn.mk
  by cases x

instance [ErrorE -< E] : MonadLift Option (CTree E C) where
  monadLift
    | .none => fail
    | .some v => return v

instance [ErrorE -< E] [UBE -< E] : MonadLift Interp (CTree E C) where
  monadLift
    | .ub _ => ub
    | .fail _ => fail
    | .ok v => return v

/--
A `PureOrErr` CTree has a finite depth, and no visible effect except for failure or UB.
-/
inductive PureOrErr {EIn CIn R} {E : EIn → Type} {C : CIn → Type}
    [ErrorE -< E] [UBE -< E] :
  CTree E C R → Prop where
| ret (r : R) : PureOrErr (CTree.ret r)
| tau (c : C1In ⊕ CIn) k : (forall x, PureOrErr (k x)) → PureOrErr (CTree.tauG c k)
| fail {k} : PureOrErr (CTree.vis (Subeffect.mapEff ErrorE E ErrorEIn.mk) k)
| ub {k} : PureOrErr (CTree.vis (Subeffect.mapEff UBE E UBEIn.mk) k)

attribute [simp, grind .] PureOrErr.tau PureOrErr.ret PureOrErr.fail PureOrErr.ub

theorem PureOrErr.bind {EIn CIn X Y} {E : EIn → Type} {C : CIn → Type}
    [ErrorE -< E] [UBE -< E] (t : CTree E C Y) (k : Y → CTree E C X) :
  PureOrErr t →
  (forall x, PureOrErr (k x)) →
  PureOrErr (Bind.bind t k) := by
  intros ht
  induction ht <;> grind

inductive PureOrErr.CanInterpretTo {EIn CIn R} {E : EIn → Type} {C : CIn → Type}
    [ErrorE -< E] [UBE -< E] : CTree E C R → Interp R → Prop where
| ret (r : R) : CanInterpretTo (CTree.ret r) (.ok r)
| tau (c : C1In ⊕ CIn) k : ∀ x r, CanInterpretTo (k x) r → CanInterpretTo (CTree.tauG c k) r
| fail {k} : CanInterpretTo (CTree.vis (Subeffect.mapEff ErrorE E ErrorEIn.mk) k) (.fail none)
| ub {k} : CanInterpretTo (CTree.vis (Subeffect.mapEff UBE E UBEIn.mk) k) (.ub none)

namespace PureOrErr.CanInterpretTo

variable {EIn CIn R} {E : EIn → Type} {C : CIn → Type}
    [ErrorE -< E] [UBE -< E]

/-- A return node has exactly its successful return value as an outcome. -/
@[simp, grind =]
theorem pure_iff (v : R) (r : Interp R) :
    CanInterpretTo (pure v : CTree E C R) r ↔ r = .ok v := by
  constructor
  · intro h
    generalize heq : (pure v : CTree E C R) = t at h
    cases h <;> have hhead := congrArg CTree.unfold heq <;>
      simp only [unfold_ret, unfold_tauG, unfold_vis, unfold_pure] at hhead <;> grind
  · rintro rfl
    exact .ret _

/-- A choice node can produce an outcome exactly when one of its branches can. -/
@[simp, grind =]
theorem tauG_iff (c : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) c → CTree E C R)
    (r : Interp R) :
    CanInterpretTo (CTree.tauG c k) r ↔ ∃ x, CanInterpretTo (k x) r := by
  constructor
  · intro h
    generalize heq : CTree.tauG c k = t at h
    cases h <;> have hhead := congrArg CTree.unfold heq <;>
      simp only [unfold_ret, unfold_tauG, unfold_vis] at hhead <;> cases hhead <;> grind
  · rintro ⟨x, h⟩
    exact .tau c k x r h

/-- A custom choice can produce an outcome exactly when one of its branches can. -/
@[simp, grind =]
theorem tau_iff (c : CIn) (k : C c → CTree E C R) (r : Interp R) :
    CanInterpretTo (CTree.tau c k) r ↔ ∃ x, CanInterpretTo (k x) r := by
  exact tauG_iff (.inr c) k r

/-- A sub-choice can successfully return any value of its choice type. -/
@[simp, grind =]
theorem choose_iff {SubCIn} {SubC : SubCIn → Type} [SubC -< C]
    (c : SubCIn) (r : Interp (SubC c)) :
    CanInterpretTo (CTree.choose (E := E) (C := C) c) r ↔ ∃ x, r = .ok x := by
  simp only [CTree.choose, tau_iff, CTree.ret_pure, pure_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, hx⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := Subeffect.map_surj (ε₁ := SubC) (ε₂ := C) c x
    exact ⟨y, congrArg Interp.ok hy.symm⟩

/-- Binding continues successful outcomes and propagates failure or UB. -/
@[grind =]
theorem bind_iff {X} (t : CTree E C X) (k : X → CTree E C R)
    (r : Interp R) :
    CanInterpretTo (CTree.bind t k) r ↔
      (∃ x, CanInterpretTo t (.ok x) ∧ CanInterpretTo (k x) r) ∨
      (CanInterpretTo t (.fail none) ∧ r = .fail none) ∨
      (CanInterpretTo t (.ub none) ∧ r = .ub none) := by
  constructor
  · intro h
    have hbound := h
    generalize heq : CTree.bind t k = tk at h hbound
    induction h generalizing t <;> cases t <;>
      simp only [← CTree.ret_pure, CTree.bind_ret,
        CTree.CTree.bind_tau, CTree.CTree.bind_vis] at heq
    all_goals first
      | exact .inl ⟨_, .ret _, heq.symm ▸ hbound⟩
      | have hhead := congrArg CTree.unfold heq
        simp only [unfold_ret, unfold_tauG, unfold_vis] at hhead
        cases hhead <;> grind [← CanInterpretTo.fail, ← CanInterpretTo.ub]
  · have compose {s : Interp X} (ht : CanInterpretTo t s) :
        (match (generalizing := false) s with
          | .ok x => CanInterpretTo (k x) r
          | .fail op => r = .fail op
          | .ub op => r = .ub op) → CanInterpretTo (CTree.bind t k) r := by
      induction ht <;> simp only [CTree.bind_ret, CTree.CTree.bind_tau, CTree.CTree.bind_vis] <;>
        grind [← CanInterpretTo.fail, ← CanInterpretTo.ub]
    grind

end PureOrErr.CanInterpretTo

end Veir
