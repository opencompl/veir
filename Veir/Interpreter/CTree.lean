module

public import CTree.Defs
public import CTree.Iter
public import CTree.Interp

public import Veir.Interpreter.Interp
public import Veir.Interpreter.RuntimeValue

public section

open CTree

/-!
  Infrastructure for CTree-based interpretation.

  A CTree-based interpreter can give semantics to effects, to nondeterminism and to non-termination.
-/

namespace Veir

/-! ## Undefined Behavior Effect -/

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

/-! ## Error Effect -/

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

/-! ## Freeze Effect -/

/-- Choice of a bitvector of a given bitwidth (input type) -/
structure FreezeCIn : Type u where
  bw : Nat

/-- Choice of a bitvector of a given bitwidth (output type) -/
abbrev FreezeC (c : FreezeCIn.{u}) : Type :=
  match c with
  | .mk bw => BitVec bw

/-! ## Region Runner Effect -/

/-- A region call effect (input type), including its arguments and the state visible to its body. -/
structure RunRegionEIn (ctx : WfIRContext OpCode) (σ : Type) where
  region : RegionPtr
  values : Array RuntimeValue
  state : σ
  regionInBounds : region.InBounds ctx.raw := by grind

/-- A region call effect output type. A region returns its final state and its yielded values. -/
abbrev RunRegionE (ctx : WfIRContext OpCode) (σ : Type) (_ : RunRegionEIn ctx σ) : Type :=
  σ × Array RuntimeValue

/-- Trees whose region calls have not yet been interpreted. -/
abbrev RegionTree (ctx : WfIRContext OpCode) (σ α : Type) :=
  CTree (RunRegionE ctx σ ⊕ₑ (ErrorE ⊕ₑ UBE)) FreezeC α

/-- Request region execution without choosing its recursive interpretation. -/
def runRegion (region : RegionPtr) (values : Array RuntimeValue) (state : σ)
    (inBounds : region.InBounds ctx.raw := by grind) : RegionTree ctx σ (σ × Array RuntimeValue) :=
  CTree.trigger (SubE := RunRegionE ctx σ) ⟨region, values, state, inBounds⟩

/-- A CTree with the error and UB effect, and the freeze choice. -/
abbrev Tree (α : Type) := CTree (ErrorE ⊕ₑ UBE) FreezeC α

/-! ## Monad Lifting To CTrees -/

instance [ErrorE -< E] : MonadLift Option (CTree E C) where
  monadLift
    | .none => fail
    | .some v => return v

instance [ErrorE -< E] [UBE -< E] : MonadLift Interp (CTree E C) where
  monadLift
    | .ub _ => ub
    | .fail _ => fail
    | .ok v => return v

/-! ## Definition of Pure CTrees -/

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

end Veir
