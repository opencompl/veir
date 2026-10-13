module

public meta import Lean
public meta import Std
public import Veir.Data.PBV
public meta import Veir.Meta.Tactic.PBVDecide.Reify
public meta import Veir.Meta.Tactic.PBVDecide.WidthInfo

open Lean Meta Std

open Veir.Data.PBV

namespace Veir.Meta.Tactic.PBVDecide

/--
The `BitVec` variable that a parametric-width variable was converted into,
together with the hypothesis constraining it.
-/
public meta structure BitVecInfo where
  /-- The FVarId corresponding to the new concrete-width variable. -/
  bvVar : FVarId
  /-- The FVarId of the hypothesis encoding the mask constraint on the variable. -/
  bvHyp : FVarId
  /-- The `Tm` corresponding to this BitVec's width. -/
  bvWidthTm : Tm .width

/--
Store information for all translated `BitVec`s.
-/
public meta structure BitVecInfos where
  /-- The Array containing facts about each variable. -/
  infos : Array BitVecInfo := #[]

meta def BitVecInfos.push (this : BitVecInfos) (val : BitVecInfo) : BitVecInfos :=
  { this with infos := this.infos.push val }

/--
Analyze a single bitvector FVarId, and introduce it as a `BitVec` variable in
our larger universe. `Unchecked` because `widthTm` is trusted to be the width of
`bvFVarId`; it is not re-derived from the local context.
-/
meta def introBitvecFVarUnchecked (widthInfos : WidthInfos) (g : MVarId)
      (bvInfos : BitVecInfos) (bvFVarId : FVarId) (widthTm : WidthTm) :
      MetaM (MVarId × BitVecInfos) := g.withContext do
  -- Revert any hypothesis in the local context that depend on this bitvec var.
  let g ← (← getLCtx).foldlM (init := g) fun g' ldecl => do
    if ← localDeclDependsOn ldecl bvFVarId then
      let (#[_hyp], g') ← g'.revert #[ldecl.fvarId]
        | throwError m!"Reverting {ldecl.toExpr} should produce a single var."
      return g'
    return g'
  -- Revert to expose forall with the BitVec.
  let (#[oldVar], g) ← g.revert #[bvFVarId]
    | throwError m!"Reverting {g} should produce a var."
  let wExpr := widthTm.term.toExpr widthInfos.env
  -- Apply ``var_elim.
  let some infos := widthInfos.getFromTm? widthTm.term
    | throwError m!"{wExpr} should have been defined in widthInfos."
  let [g] ← g.withContext <| g.apply <| ← mkAppM ``var_elim #[.fvar infos.hypWidthLeBoundNote, .fvar infos.widthMaskHypFvar]
    | throwError m!"{``var_elim} should generate a single goal. Produced {g}"

  let name ← oldVar.getUserName
  let (#[bvVar, bvHyp], g) ← g.withContext <| g.introN 2
    [name, Name.mkSimple s!"h_{name}_maskOfWidth_{widthTm.term.toName}"]
    | throwError m!"Expecting two intros from {g}"

  return (g, bvInfos.push { bvVar, bvHyp, bvWidthTm := widthTm.term })

/--
A plan of the bitvector fvars to be reverted, and their corresponding widths.
-/
public structure BitVecFVarsToRevert where
  bvs : HashMap FVarId WidthTm := {}

meta def BitVecFVarsToRevert.push (this : BitVecFVarsToRevert) (fvar : FVarId) (widthTm : WidthTm) : BitVecFVarsToRevert :=
  if this.bvs.contains fvar then this
  else { bvs := this.bvs.insert fvar widthTm }

/--
Given an expression, if it is of `BitVec w` type then create a term `Tm` for the
width `w`. If it is also an FVar then it is a variable, and hence has to be
added to the set of FVars to be reverted.
-/
meta def visitExprNonrec (g : MVarId)
    (widthTms : WidthTms) (bvs : BitVecFVarsToRevert)
    (e : Expr) :
    MetaM (MVarId × WidthTms × BitVecFVarsToRevert) := g.withContext do
  let te ← g.withContext do inferType e
  if let some wExpr := getBitvecType? te then
    let (g, widthTm, widthTms) ← widthTms.getOrCreateTm g wExpr
    if let some fvarId := e.fvarId? then
      return (g, widthTms, bvs.push fvarId widthTm)
    else
      return (g, widthTms, bvs)
  else
    return (g, widthTms, bvs)

/--
Visit an expression, collecting all widths and all bitvectors `FVars` that
correspond to individual bitvector variables.
-/
public meta partial def visitExprRec (g : MVarId)
    (widthTms : WidthTms) (bvs : BitVecFVarsToRevert)
    (e : Expr) :
    MetaM (MVarId × WidthTms × BitVecFVarsToRevert) := g.withContext do
  let (g, widthTms, bvs) ← visitExprNonrec g widthTms bvs e
  if e.isApp then
    let (f, args) := (e.getAppFn, e.getAppArgs)
    let (g, widthTms, bvs) ← g.withContext do
      args.foldlM (init := (g, widthTms, bvs)) fun (g, widthTms, bvs) arg =>
      g.withContext do visitExprRec g widthTms bvs arg
    visitExprRec g widthTms bvs f
  else
    return (g, widthTms, bvs)

/--
Visit the hypotheses that depend on the collected `BitVec` variables. These are
reverted into the goal when the variables are eliminated, so the `BitVec`s and
widths they mention must be collected too. Repeat until no new variables are found.
-/
public meta partial def visitDependentHyps (g : MVarId)
    (widthTms : WidthTms) (bvs : BitVecFVarsToRevert)
    (visited : FVarIdSet := {}) :
    MetaM (MVarId × WidthTms × BitVecFVarsToRevert) := g.withContext do
  let (g, widthTms, newBvs, visited) ← (← getLCtx).foldlM
    (init := (g, widthTms, bvs, visited)) fun (g, widthTms, newBvs, visited) ldecl => do
      if ldecl.isImplementationDetail || visited.contains ldecl.fvarId then
        return (g, widthTms, newBvs, visited)
      unless ← bvs.bvs.toList.anyM (fun (fvar, _) => localDeclDependsOn ldecl fvar) do
        return (g, widthTms, newBvs, visited)
      let (g, widthTms, newBvs) ← visitExprRec g widthTms newBvs ldecl.type
      return (g, widthTms, newBvs, visited.insert ldecl.fvarId)
  if newBvs.bvs.size == bvs.bvs.size then
    return (g, widthTms, newBvs)
  visitDependentHyps g widthTms newBvs visited

/--
Eliminate the bitvector variables to introduce the masked versions.
-/
public meta def introMaskedBitvectors (bvs : BitVecFVarsToRevert) (g : MVarId)
    (widthInfos : WidthInfos) : MetaM (MVarId × BitVecInfos) := do
  bvs.bvs.foldM (init := (g, {})) fun (g, bvInfos) bvFvarId widthTm => do
    introBitvecFVarUnchecked widthInfos g bvInfos bvFvarId widthTm

end Veir.Meta.Tactic.PBVDecide
