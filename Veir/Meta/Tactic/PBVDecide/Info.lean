module

public meta import Lean
public meta import Std
public meta import Veir.Meta.Tactic.PBVDecide.Config
public meta import Veir.Meta.Tactic.PBVDecide.Reify

open Lean Meta Std

public section

namespace Veir.Meta.Tactic.PBVDecide

structure WidthInfo where
  widthTm : Tm .width
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
  infos : HashMap WidthTm WidthInfo := {}
  env : TmWidthEnv
  blastWidth : Nat

meta def WidthInfos.push (this : WidthInfos) (info : WidthInfo) : WidthInfos :=
  { this with infos := this.infos.insert info.widthTm info }

meta def WidthInfos.getFromTm? (this : WidthInfos) (wTm : Tm .width) : Option WidthInfo :=
  this.infos[wTm]?

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

meta structure BitVecInfos where
  infos : Array BitVecInfo := #[]

meta def BitVecInfos.push (this : BitVecInfos) (val : BitVecInfo) : BitVecInfos :=
  { this with infos := this.infos.push val }

end Veir.Meta.Tactic.PBVDecide
