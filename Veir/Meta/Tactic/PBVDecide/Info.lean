module

public meta import Lean
public meta import Std
public meta import Veir.Meta.Tactic.PBVDecide.Config
public meta import Veir.Meta.Tactic.PBVDecide.Reify

open Lean Meta Std

public section

namespace Veir.Meta.Tactic.PBVDecide

/--
Information about the width variable and associated hypotheses.
-/
structure WidthInfo where
  /-- The `Tm` corresponding to this width. -/
  widthTm : Tm .width
  /-- The FVarId of the mask. -/
  widthMaskFVar : FVarId
  /-- The FVarId of the pure-BV hypothesis that this width is a mask variable. -/
  widthMaskHypFvar : FVarId
  /-- The proof obligation that the width variable is less than or equal to
      the blast bound. -/
  hypWidthLeBoundMVarId : Option MVarId
  /-- The hypothesis that the width variable is less than or equal to the blast
      bound. -/
  hypWidthLeBoundNote : FVarId

meta def WidthInfo.name (this : WidthInfo) : Name :=
  this.widthTm.toName

structure WidthInfos where
  /-- One WidthInfo per width -/
  infos : HashMap Name WidthInfo := {}
  /-- Width environment. -/
  env : TmWidthEnv
  /-- Width at which the bit-blasting occurs. -/
  blastWidth : Nat

meta def WidthInfos.push (this : WidthInfos) (info : WidthInfo) : WidthInfos :=
  { this with infos := this.infos.insert (info.widthTm.toName) info }

/--
Get WidthInfo from a Term.
-/
meta def WidthInfos.getFromTm? (this : WidthInfos) (wTm : Tm .width) : Option WidthInfo :=
  this.infos[wTm.toName]?

/--
Get WidthInfo from an Expr.
-/
meta def WidthInfos.getFromExpr? (this : WidthInfos) (wExpr : Expr)
    : MetaM (Option WidthInfo) := do
  -- Reduce the expression (allows for cases such as (w + 0) to be reduced to w).
  let reducedExpr ← whnf wExpr
  -- Reify the expr using the env and then look for it in the Hashmap.
  let some reified ← Tm.reifyWidth this.env reducedExpr | pure none
  return this.infos[reified.toName]?

/--
The `BitVec` variable that a parametric-width variable was converted into,
together with the hypothesis constraining it.
-/
meta structure BitVecInfo where
  /-- The FVarId corresponding to the new concrete-width variable. -/
  bvVar : FVarId
  /-- The FVarId of the hypothesis encoding the mask constraint on the variable. -/
  bvHyp : FVarId
  /-- The `Tm` corresponding to this BitVec's width. -/
  bvWidthTm : Tm .width

/--
Store information for all translated `BitVec`s.
-/
meta structure BitVecInfos where
  /-- The Array containing facts about each variable. -/
  infos : Array BitVecInfo := #[]

meta def BitVecInfos.push (this : BitVecInfos) (val : BitVecInfo) : BitVecInfos :=
  { this with infos := this.infos.push val }

end Veir.Meta.Tactic.PBVDecide
