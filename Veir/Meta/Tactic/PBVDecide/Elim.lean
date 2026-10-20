module

public meta import Lean
public import Veir.Data.PBV
public meta import Veir.Meta.Tactic.PBVDecide.Basic

open Lean Meta Std

open Veir.Data.PBV

namespace Veir.Meta.Tactic.PBVDecide

/--
Get the side goal for `prop`, creating a fresh mvar for it if there is none yet.
-/
meta def getOrCreateFreshMVar (g : MVarId)
  (prop : WidthProp) : TranslateM Expr := do
  if let some mvar := (← get).freshMVars.get? prop then
    return .mvar mvar
  else
    let freshMVar ← g.withContext do mkFreshExprMVar (prop.toExpr (← read).env)
    modifyGet fun s =>
      (freshMVar, { s with freshMVars := s.freshMVars.insert prop freshMVar.mvarId! })

/--
Given a width term (`widthTm`), introduce a `BitVec` variable corresponding
to the mask of that width. Then introduce a hypothesis bounding the width by the
blast width and enforce it as a mask with `and_add_one_eq_zero_of_maskOfWidth`.
-/
meta def introMaskWidth (g : MVarId) (widthTm : WidthTm)
  : TranslateM (MVarId × WidthInfo) := g.withContext do
    -- Apply width_elim
    let [g] ← g.apply <| ← mkAppM ``width_elim
        #[mkNatLit (← read).blastWidth, widthTm.toExpr (← read).env, ← g.getType]
      | throwError m!"{``width_elim} should generate a goal"
    -- Intros
    let name := widthTm.toName
    let maskName := Name.mkSimple s!"m_{name}"
    let (#[mask, maskHyp], g) ← g.introN 2 [maskName, Name.mkSimple s!"h_{maskName}"]
      | throwError m!"Failed to intro {``width_elim}"
    -- Introduce width bound on the variable.
    let hypWidthLeBound ← getOrCreateFreshMVar g (.widthLe widthTm (.widthLit (← read).blastWidth))
    let (hypWidthLeBoundNote, g) ← g.note (Name.mkSimple s!"h_{maskName}_le_blast") hypWidthLeBound
    -- Assert the BitVec mask constraint.
    let hypExpr ← g.withContext do mkAppM ``and_add_one_eq_zero_of_maskOfWidth #[mkFVar maskHyp]
    let (_, g) ← g.note (Name.mkSimple s!"h_{maskName}_bv_mask") hypExpr

    let info : WidthInfo := {
      widthMaskFVar := mask,
      widthMaskHypFvar := maskHyp
      hypWidthLeBoundNote
    }
    modifyGet fun s =>
      ((g, info), { s with widthInfos := s.widthInfos.insert widthTm info })

/--
Introduce the mask of a width literal. Its value is known, so the mask is
defined directly, and the proofs that it is a mask and is within the blast width
are computed.
-/
meta def introMaskLit (g : MVarId) (widthLit : WidthTm) : TranslateM (MVarId × WidthInfo) := g.withContext do
  let .widthLit val := widthLit | throwError m!"{widthLit.toExpr (← read).env} is not a width literal."
  if val > (← read).blastWidth then
    throwError m!"Literal width {val} is greater than blast width ({(← read).blastWidth})"
  let o := mkNatLit (← read).blastWidth
  let n := mkNatLit val
  -- Create the concrete BitVec value corresponding to the mask of this Lit
  let lit ← mkAppM ``BitVec.ofNat #[o, mkNatLit (2 ^ val - 1)]
  let maskTy ← mkAppM ``BitVec #[o]
  -- Define the mask
  let maskName := Name.mkSimple s!"m_{widthLit.toName}"
  let g ← g.assertExt maskName maskTy lit
  let (mask, g) ← g.intro1P
  let (_maskValue, g) ← g.introN 1 [Name.mkSimple s!"{maskName}_val"]
  -- Prove that the mask is indeed a maskOfWidth
  let applyMask ← mkAppM ``maskOfWidth #[o, n]
  let proof ← g.withContext do mkExpectedTypeHint (← mkEqRefl (mkFVar mask)) (← mkEq (mkFVar mask) applyMask)
  let (maskHyp, g) ← g.note (Name.mkSimple s!"h_m_{widthLit.toName}") proof
  -- Prove that the lit respects the bound
  let (hypWidthLeBound, g) ←
    g.note (Name.mkSimple s!"h_m_{widthLit.toName}_le_blast") <| ← mkDecideProof (mkNatLE n o)

  let info : WidthInfo := {
    widthMaskFVar := mask,
    widthMaskHypFvar := maskHyp,
    hypWidthLeBoundNote := hypWidthLeBound,
  }
  modifyGet fun s =>
    ((g, info), { s with widthInfos := s.widthInfos.insert widthLit info })

/--
Get the mask of a width term, creating it if needed. The mask of a sum is
created from the masks of its parts, together with a hypothesis relating them.
-/
meta def getOrCreateWidthMask (g : MVarId) (widthTm : WidthTm) : TranslateM (MVarId × WidthInfo) := do
  -- Check if this width term is already in widthInfos
  if let some info := (← get).widthInfos[widthTm]? then
    return (g, info)
  -- Otherwise, recurse through the term to create it
  match widthTm with
  | .widthAtom _ | .widthFVar _ _ => introMaskWidth g widthTm
  | .widthLit _ => introMaskLit g widthTm
  | .widthAdd v w => do
    -- Get or create masks of the children
    let (g, vInfo) ← getOrCreateWidthMask g v
    let (g, wInfo) ← getOrCreateWidthMask g w
    -- Intro the mask for this term
    let (g, thisInfo) ← introMaskWidth g widthTm
    -- Rewrite the mask of a sum of widths in terms of the underlying masks.
    let (_hyp, g) ← g.withContext do
      g.note (Name.mkSimple s!"bv_{widthTm.toName}") <| ← mkAppM ``add_eq_shift_sum_of_maskOfWidth #[
        .fvar vInfo.hypWidthLeBoundNote,
        .fvar wInfo.hypWidthLeBoundNote,
        .fvar thisInfo.hypWidthLeBoundNote,
        .fvar vInfo.widthMaskHypFvar,
        .fvar wInfo.widthMaskHypFvar,
        .fvar thisInfo.widthMaskHypFvar
      ]

    return (g, thisInfo)

/--
Given a `Tm .prop` and a `proof` of it, construct a proof of the same prop
stated in terms of the masks.
-/
meta def getMaskedExprFromProp (g : MVarId) (prop : WidthProp) (proof : Expr)
    : TranslateM (MVarId × Expr) := g.withContext do
  -- Ensure the proof and prop match.
  unless ← isDefEq (← inferType proof) (prop.toExpr (← read).env)
    do throwError m!"Prop : {prop.toExpr (← read).env} doesn't match the proof : {← inferType proof}"
  -- Helper to apply a theorem for a binary operation on widths.
  let applyPropBinop (thm : Name) (v w : WidthTm) : TranslateM (MVarId × Expr) := do
    let (g, vInfo) ← getOrCreateWidthMask g v
    let (g, wInfo) ← getOrCreateWidthMask g w
    let expr ← g.withContext <| mkAppM thm #[
          .fvar vInfo.hypWidthLeBoundNote,
          .fvar wInfo.hypWidthLeBoundNote,
          .fvar vInfo.widthMaskHypFvar,
          .fvar wInfo.widthMaskHypFvar,
          proof,
        ]
    return (g, expr)
  -- Recurse over the prop structure
  match prop with
  | .widthLt v w => applyPropBinop ``lt_of_lt_of_eq_maskOfWidth v w
  | .widthLe v w => applyPropBinop ``le_of_le_of_eq_maskOfWidth v w
  | .widthEq v w => applyPropBinop ``eq_of_eq_of_eq_maskOfWidth v w
  | .and a b => do
    let (g, aExpr) ←
      getMaskedExprFromProp g a (← mkAppM ``And.left  #[proof])
    let (g, bExpr) ←
      getMaskedExprFromProp g b (← mkAppM ``And.right #[proof])
    let expr ← g.withContext <| mkAppM ``And.intro #[aExpr, bExpr]
    return (g, expr)

/-- State each reified width prop in terms of the masks, adding it to the context. -/
public meta def translatePropsToMask (g : MVarId) : TranslateM MVarId := do
  (← read).props.foldM (init := g) fun g widthProp proof => do
    -- Obtain the `Expr` of the prop in terms of the mask.
    let (g, expr) ← getMaskedExprFromProp g widthProp proof
    -- State the prop in terms of the masks.
    let (_, g) ← g.note (Name.mkSimple s!"bv_{widthProp.toName}") expr
    return g

/--
Given the width terms in the formula, translate all `Nat` widths into `BitVec`
masks and introduce the hypotheses that model the masks.
-/
public meta def introMaskWidths (g : MVarId) : TranslateM MVarId
  := g.withContext do
  -- Intro all the masks
  (← read).widthTms.foldM
    (init := g)
    fun g widthTm => do
      let (g, _) ← getOrCreateWidthMask g widthTm
      return g

/--
Eliminate a single `BitVec` variable, replacing it with a variable at the blast
width constrained by the mask of its width. `Unchecked` because `widthTm` is trusted to be the width of
`bvFVarId`; it is not re-derived from the local context.
-/
meta def introBitvecFVarUnchecked (g : MVarId) (bvFVarId : FVarId) (widthTm : WidthTm) :
      TranslateM MVarId := g.withContext do
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
  let wExpr := widthTm.toExpr (← read).env
  -- Apply ``var_elim.
  let some infos := (← get).widthInfos[widthTm]?
    | throwError m!"{wExpr} should have been defined in widthInfos."
  let [g] ← g.withContext <| g.apply <| ← mkAppM ``var_elim #[.fvar infos.hypWidthLeBoundNote, .fvar infos.widthMaskHypFvar]
    | throwError m!"{``var_elim} should generate a single goal. Produced {g}"

  let name ← oldVar.getUserName
  let (#[bvVar, bvHyp], g) ← g.withContext <| g.introN 2
    [name, Name.mkSimple s!"h_{name}_maskOfWidth_{widthTm.toName}"]
    | throwError m!"Expecting two intros from {g}"

  modifyGet fun s =>
    (g, { s with bitvecInfos := s.bitvecInfos.push { bvVar, bvHyp, bvWidthTm := widthTm } })

/--
Eliminate the bitvector variables to introduce the masked versions.
-/
public meta def introMaskedBitvectors (g : MVarId) : TranslateM MVarId := do
  (← read).bvs.foldM (init := g) fun g bvFvarId widthTm => do
    introBitvecFVarUnchecked g bvFvarId widthTm

end Veir.Meta.Tactic.PBVDecide
