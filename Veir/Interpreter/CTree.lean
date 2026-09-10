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

/- Effect representing an immediate undefined behavior -/

structure UBEIn : Type u where

@[expose]
def UBE (e : UBEIn.{u}) :=
  match e with
  | .mk => Empty

/- Effect materializing an ill-formed program -/

structure ErrorEIn : Type u where

@[expose]
def ErrorE (e : ErrorEIn.{u}) :=
  match e with
  | .mk => Empty

def fail {EIn CIn} {E : EIn → Type} {C : CIn → Type} {R} [ErrorE -< E] : CTree E C R := do
  let x ← CTree.trigger (SubE := ErrorE) ErrorEIn.mk
  by cases x

def ub {EIn CIn} {E : EIn → Type} {C : CIn → Type} {R} [UBE -< E] : CTree E C R := do
  let x ← CTree.trigger (SubE := UBE) UBEIn.mk
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

end Veir
