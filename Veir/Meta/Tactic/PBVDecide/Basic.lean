module

public meta import Veir.Meta.Tactic.PBVDecide.Config
import Lean.CoreM
import Lean.Meta.Basic


public section

open Lean Meta Std

namespace Veir.Meta.Tactic.PBVDecide

meta def mkNatLT (a b : Expr) : Expr :=
  mkApp2 (mkApp2 (mkConst ``LT.lt [0]) Nat.mkType Nat.mkInstLT) a b

inductive TmKind
| width
| prop

/--
The expressions this tactic handles: `Nat` width terms (`Tm .width`) and the
propositions relating them (`Tm .prop`). Width atoms are referred to by their
index in a `TmWidthEnv`.
-/
meta inductive Tm : TmKind → Type
| widthLit (val : Nat) : Tm .width
| widthAtom (id : Nat) : Tm .width
| widthFVar (id : Nat) (fid : FVarId) : Tm .width
| widthAdd (v w : Tm .width) : Tm .width
| widthSub (v w : Tm .width) : Tm .width
| widthLt (v w : Tm .width) : Tm .prop
| widthLe (v w : Tm .width) : Tm .prop
| widthEq (v w : Tm .width) : Tm .prop
| and (v w : Tm .prop) : Tm .prop
deriving BEq, Hashable

abbrev WidthTm := Tm .width
abbrev WidthProp := Tm .prop
/-- The `Expr`s of the width atoms of a `Tm`, indexed by the atom's id. -/
abbrev TmWidthEnv := Array Expr

meta def Tm.toExpr {k : TmKind} (this : Tm k) (env : TmWidthEnv) : Expr :=
  match this with
  | .widthLit val => mkNatLit val
  | .widthAtom id | .widthFVar id _ => env[id]!
  | .widthAdd v w => mkNatAdd (v.toExpr env) (w.toExpr env)
  | .widthSub v w => mkNatSub (v.toExpr env) (w.toExpr env)
  | .widthLt  v w => mkNatLT (v.toExpr env) (w.toExpr env)
  | .widthLe  v w => mkNatLE (v.toExpr env) (w.toExpr env)
  | .widthEq  v w => mkNatEq (v.toExpr env) (w.toExpr env)
  | .and      a b => mkAnd (a.toExpr env) (b.toExpr env)

/--
Generate a `Name` from a `Tm`. Width variables keep their user name (`w{id}` if
it is inaccessible), opaque atoms are named `a{id}` after their index.
-/
meta def Tm.toName {k : TmKind} (tm : Tm k) : MetaM Name :=
  match tm with
  | .widthLit val => return Name.mkSimple s!"lit{val}"
  | .widthFVar id fvarid => do
    let name ← fvarid.getUserName
    if name.hasMacroScopes then return Name.mkSimple s!"w{id}" else return name
  | .widthAtom id => return Name.mkSimple s!"a{id}"
  | .widthAdd v w => return Name.mkSimple s!"{← v.toName}_add_{← w.toName}"
  | .widthSub v w => return Name.mkSimple s!"{← v.toName}_sub_{← w.toName}"
  | .widthLt  v w => return Name.mkSimple s!"{← v.toName}_lt_{← w.toName}"
  | .widthLe  v w => return Name.mkSimple s!"{← v.toName}_le_{← w.toName}"
  | .widthEq  v w => return Name.mkSimple s!"{← v.toName}_eq_{← w.toName}"
  | .and      a b => return Name.mkSimple s!"{← a.toName}_and_{← b.toName}"

/--
Compute an upper bound on the widths in this term: an atom is bounded by
`bound` (the bmc bound), a sum by the sum of the bounds of its parts, and a prop by the
maximum of the bounds of its parts.
The maximum over all widths and width props gives the blast width used for the
whole goal.
-/
meta def Tm.getUpperBound {k : TmKind} (tm : Tm k) (bound : Nat) : Nat :=
  match tm with
  | .widthLit val => val
  | .widthAtom _ | .widthFVar _ _ => bound
  | .widthAdd wa wb => (wa.getUpperBound bound) + (wb.getUpperBound bound)
  | .widthSub wa wb => wa.getUpperBound bound
  | .widthLt  v w
  | .widthLe  v w
  | .widthEq  v w
  | .and      v w => (v.getUpperBound bound).max (w.getUpperBound bound)

/-- The set of width terms found in the goal. -/
abbrev WidthTms := HashSet WidthTm

meta def WidthTms.getUpperBound (this : WidthTms) (bound : Nat) : Nat :=
  this.fold (init := bound) fun acc wTm =>
    acc.max <| wTm.getUpperBound bound

/-- A map from a `Tm .prop` to the `Nat` proof it was reified from -/
abbrev WidthProps := HashMap WidthProp Expr

meta def WidthProps.getUpperBound (this : WidthProps) (bound : Nat) : Nat :=
  this.fold (init := bound) fun acc wTm _ =>
    acc.max <| wTm.getUpperBound bound

/-- The `BitVec` variables to eliminate, mapped to the width term of their type. -/
abbrev BitVecFVarsToRevert := HashMap FVarId WidthTm

structure ReifyState where
  env : TmWidthEnv := #[]
  widthTms : WidthTms := {}
  bvs : BitVecFVarsToRevert := {}
  /-- The props on widths found in the local context (the preconditions). -/
  props : WidthProps := {}

meta def ReifyState.dependsOnBvs (self : ReifyState) (ldecl : LocalDecl) : MetaM Bool :=
  localDeclDependsOnPred ldecl (fun fvar => self.bvs.contains fvar)

abbrev ReifyM := ReaderT PbvDecideContext <| StateRefT ReifyState MetaM

@[inline] meta def ReifyM.run (ctx : PbvDecideContext) (x : ReifyM α) : MetaM (α × ReifyState) :=
  ReaderT.run x ctx |>.run {}

/-- The mask a width term was translated into, and the hypotheses about it. -/
structure WidthInfo where
  widthMaskFVar : FVarId
  /-- The FVarId of the pure-BV hypothesis that this width is a mask variable. -/
  widthMaskHypFvar : FVarId
  /-- The hypothesis that the width variable is less than or equal to the blast
      bound. -/
  hypWidthLeBoundNote : FVarId

abbrev WidthInfos := HashMap WidthTm WidthInfo

/--
The `BitVec` variable that a parametric-width variable was converted into,
together with the hypothesis constraining it.
-/
meta structure BitVecInfo where
  /-- The FVarId corresponding to the new concrete-width variable. -/
  bvVar : FVarId
  /-- The FVarId of the hypothesis encoding the mask constraint on the variable. -/
  bvHyp : FVarId
  bvWidthTm : WidthTm

abbrev BitVecInfos := Array BitVecInfo

public structure TranslateState where
  /-- The side goals generated by the translation, proving that the widths are
      bounded by the blast width. -/
  freshMVars : HashMap WidthProp MVarId := {}
  widthInfos : WidthInfos := {}
  /-- The `BitVec` variables converted to masked form. -/
  bitvecInfos : BitVecInfos := #[]

meta def TranslateState.subgoals (self : TranslateState) : List MVarId := self.freshMVars.values

/-- The frozen output of reification, read throughout the translation. -/
structure Reified extends ReifyState where
  /-- The width every `BitVec` is lifted to: an upper bound on all the widths. -/
  blastWidth : Nat

abbrev TranslateM := ReaderT Reified <| StateRefT TranslateState MetaM

structure Translated extends TranslateState, Reified

/--
Run a `TranslateM` computation from an empty state, returning the `Reified`
input and the final state together as a `Translated`.
-/
@[inline] meta def TranslateM.run (reifiedState : Reified) (x : TranslateM α) : MetaM (α × Translated) := do
  let (a, s) ← ReaderT.run x reifiedState |>.run {}
  return (a, { toReified := reifiedState, toTranslateState := s })


end Veir.Meta.Tactic.PBVDecide
