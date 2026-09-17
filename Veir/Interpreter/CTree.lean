module

public import CTree.Defs
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
    | .ub => ub
    | .fail => fail
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
  intros ht hk
  induction ht generalizing hk <;> grind
end Veir
