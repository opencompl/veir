module

public meta import Veir.Meta.Tactic.PBVDecide.Config
import Lean.CoreM
import Lean.Meta.Basic


public section

open Lean Meta Std

namespace Veir.Meta.Tactic.PBVDecide

meta def mkNatLT (a b : Expr) : Expr :=
  mkApp2 (mkApp2 (mkConst ``LT.lt [0]) Nat.mkType Nat.mkInstLT) a b

/--
Type to capture the expressions this tactic handles: `Nat` width terms and
the propositions relating them.
-/
inductive TmKind
| width
| prop

meta inductive Tm : TmKind → Type
| widthLit (val : Nat) : Tm .width
| widthAtom (id : Nat) : Tm .width
| widthFVar (id : Nat) (fid : FVarId) : Tm .width
| widthAdd (v w : Tm .width) : Tm .width
| widthLt (v w : Tm .width) : Tm .prop
| widthLe (v w : Tm .width) : Tm .prop
| widthEq (v w : Tm .width) : Tm .prop
| and (v w : Tm .prop) : Tm .prop
deriving BEq, Hashable

abbrev WidthTm := Tm .width
abbrev WidthProp := Tm .prop
abbrev TmWidthEnv := Array Expr

meta def Tm.toExpr {k : TmKind} (this : Tm k) (env : TmWidthEnv) : Expr :=
  match this with
  | .widthLit val => mkNatLit val
  | .widthAtom id | .widthFVar id _ => env[id]!
  | .widthAdd v w => mkNatAdd (v.toExpr env) (w.toExpr env)
  | .widthLt  v w => mkNatLT (v.toExpr env) (w.toExpr env)
  | .widthLe  v w => mkNatLE (v.toExpr env) (w.toExpr env)
  | .widthEq  v w => mkNatEq (v.toExpr env) (w.toExpr env)
  | .and      a b => mkAnd (a.toExpr env) (b.toExpr env)

/--
Generate a `Name` from a `Tm`. Uses the index of the atoms as the basic variable name.
-/
meta def Tm.toName {k : TmKind} (tm : Tm k) : Name :=
  match tm with
  | .widthLit val => Name.mkSimple s!"lit{val}"
  | .widthAtom id | .widthFVar id _ => Name.mkSimple s!"w{id}"
  | .widthAdd v w => Name.mkSimple s!"{v.toName}_add_{w.toName}"
  | .widthLt  v w => Name.mkSimple s!"{v.toName}_lt_{w.toName}"
  | .widthLe  v w => Name.mkSimple s!"{v.toName}_le_{w.toName}"
  | .widthEq  v w => Name.mkSimple s!"{v.toName}_eq_{w.toName}"
  | .and      a b => Name.mkSimple s!"{a.toName}_and_{b.toName}"

/--
Compute an upper bound on the widths in this term: an atom is bounded by the
bmc bound, a sum by the sum of the bounds of its parts, and a prop by the
maximum of the bounds of its parts.
The maximum over all widths and width props gives the blast width used for the
whole goal.
-/
meta def Tm.getUpperBound {k : TmKind} (tm : Tm k) (bound : Nat) : Nat :=
  match tm with
  | .widthLit val => val
  | .widthAtom _ | .widthFVar _ _ => bound
  | .widthAdd wa wb => (wa.getUpperBound bound) + (wb.getUpperBound bound)
  | .widthLt  v w
  | .widthLe  v w
  | .widthEq  v w
  | .and      v w => (v.getUpperBound bound).max (w.getUpperBound bound)

/-- The set of width terms found in the goal. -/
abbrev WidthTms := HashSet WidthTm

/-- Get the maximum width needed for blasting across all widths. -/
meta def WidthTms.getUpperBound (this : WidthTms) (bound : Nat) : Nat :=
  this.fold (init := bound) fun acc wTm =>
    acc.max <| wTm.getUpperBound bound

/-- A map from a `Tm .prop` to the `Nat` proof it was reified from -/
abbrev WidthProps := HashMap WidthProp Expr

meta def WidthProps.getUpperBound (this : WidthProps) (bound : Nat) : Nat :=
  this.fold (init := bound) fun acc wTm _ =>
    acc.max <| wTm.getUpperBound bound

abbrev BitVecFVarsToRevert := HashMap FVarId WidthTm

structure ReifyState where
  env : TmWidthEnv := #[]
  widthTms : WidthTms := {}
  bvs : BitVecFVarsToRevert := {}
  props : WidthProps := {}

abbrev ReifyM := ReaderT PbvDecideContext <| StateRefT ReifyState MetaM

@[inline] meta def ReifyM.run (ctx : PbvDecideContext) (x : ReifyM α) : MetaM (α × ReifyState) :=
  ReaderT.run x ctx |>.run {}

@[inline] meta def getWidthEnv : ReifyM TmWidthEnv := return (← get).env
@[inline] meta def getPbvCtx : ReifyM PbvDecideContext := read

end Veir.Meta.Tactic.PBVDecide
