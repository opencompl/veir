module

public meta import Lean
public meta import Std
public import Veir.Data.PBV
public meta import Veir.Meta.Tactic.PBVDecide.Config
public meta import Veir.Meta.Tactic.PBVDecide.Reify

open Lean Meta Std

open Veir.Data.PBV

namespace Veir.Meta.Tactic.PBVDecide

/--
Information about the width variable and associated hypotheses.
-/
public structure WidthInfo where
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

public meta def WidthInfo.name (this : WidthInfo) : Name :=
  this.widthTm.toName

public structure WidthInfos where
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
public meta def WidthInfos.getFromTm? (this : WidthInfos) (wTm : Tm .width) : Option WidthInfo :=
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
Given a width term (`widthTm`), introduce a `BitVec` variable corresponding
to the mask of that width. Then introduce a hypothesis bounding the width to the
provided `blastWidth` and enforce it as a mask with `and_add_one_eq_zero_of_maskOfWidth`.
-/
meta def introMaskWidth (g : MVarId) (widthTm : Tm .width) (infos : WidthInfos)
  : MetaM (MVarId × WidthInfo × WidthInfos) := g.withContext do
    -- Apply width_elim
    let [g] ← g.withContext do
      g.apply <| ← mkAppM ``width_elim
        #[mkNatLit infos.blastWidth, widthTm.toExpr infos.env, ← g.getType]
      | throwError m!"{``width_elim} should generate a goal"
    -- Intros
    let name := widthTm.toName
    let maskName := Name.mkSimple s!"m_{name}"
    let (#[mask, maskHyp], g) ← g.withContext
      <| g.introN 2 [maskName, Name.mkSimple s!"h_{maskName}"]
      | throwError m!"Failed to intro {``width_elim}"
    -- Introduce width bound on the variable.
    let hypWidthLeBound ← g.withContext do
      mkFreshExprMVar (mkAppN (Expr.const ``LE.le [.zero])
        #[mkConst ``Nat,
          mkConst ``instLENat,
          widthTm.toExpr infos.env,
          mkNatLit infos.blastWidth])
    g.withContext <| check hypWidthLeBound
    let (hypWidthLeBoundNote, g) ← g.withContext do g.note (Name.mkSimple s!"h_{maskName}_le_blast") hypWidthLeBound
    g.withContext <| check (mkFVar hypWidthLeBoundNote)
    -- Assert the BitVec mask constraint.
    let hypExpr ← g.withContext do mkAppM ``and_add_one_eq_zero_of_maskOfWidth #[mkFVar maskHyp]
    let (_, g) ← g.withContext do g.note (Name.mkSimple s!"h_{maskName}_bv_mask") hypExpr

    let info : WidthInfo := {
      widthTm := widthTm,
      widthMaskFVar := mask,
      widthMaskHypFvar := maskHyp
      hypWidthLeBoundMVarId := some hypWidthLeBound.mvarId!,
      hypWidthLeBoundNote
    }
    return (g, info, infos.push info)

meta def introMaskLit (g : MVarId) (widthLit : Tm .width) (infos : WidthInfos) : MetaM (MVarId × WidthInfo × WidthInfos) := g.withContext do
  let .widthLit val := widthLit | throwError m!"{widthLit.toExpr infos.env} is not a width literal."
  if val > infos.blastWidth then
    throwError m!"Literal width {val} is greater than blast width ({infos.blastWidth})"
  let o := mkNatLit infos.blastWidth
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
  let (maskHyp, g) ← g.withContext do g.note (Name.mkSimple s!"h_m_{widthLit.toName}") proof
  -- Prove that the lit respects the bound
  let (hypWidthLeBound, g) ← g.withContext do
    g.note (Name.mkSimple s!"h_m_{widthLit.toName}_le_blast") <| ← mkDecideProof (mkNatLE n o)

  let info : WidthInfo := {
    widthTm := widthLit,
    widthMaskFVar := mask,
    widthMaskHypFvar := maskHyp,
    hypWidthLeBoundNote := hypWidthLeBound,
    hypWidthLeBoundMVarId := none
  }

  return (g, info, infos.push info)


/--
Recurse through a `.width Tm`, converting `Nat` term into a `BitVec` mask, and
translating relations on the terms into relations on the `BitVec` (eg. add).
-/
meta def getOrCreateWidthMask (g : MVarId) (widthTm : Tm .width) (infos : WidthInfos)
  : MetaM (MVarId × WidthInfo × WidthInfos) := do
  -- Check if this width term is already in widthInfos
  if let some info := infos.getFromTm? widthTm then
    return (g, info, infos)
  -- Otherwise, recurse through the term to create it
  match widthTm with
  | .widthAtom _ => introMaskWidth g widthTm infos
  | .widthLit _ => introMaskLit g widthTm infos
  | .widthAdd v w => do
    -- Get or create masks of the children
    let (g, vInfo, infos) ← getOrCreateWidthMask g v infos
    let (g, wInfo, infos) ← getOrCreateWidthMask g w infos
    -- Intro the mask for this term
    let (g, thisInfo, infos) ← introMaskWidth g widthTm infos
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

    return (g, thisInfo, infos)

/--
Given a `Tm .prop` and the `Expr` it was reified from, construct the expr that
corresponds to the `Prop` expressed in terms of the masks.
-/
meta def getMaskedExprFromProp (g : MVarId) (prop : Tm .prop) (proof : Expr)
    (widthInfos : WidthInfos) : MetaM (MVarId × WidthInfos × Expr) := g.withContext do
  -- Ensure the proof and prop match.
  unless ← isDefEq (← inferType proof) (prop.toExpr widthInfos.env)
    do throwError m!"Prop : {prop.toExpr widthInfos.env} doesn't match the proof : {← inferType proof}"
  -- Helper to apply a theorem for a binary operation on widths.
  let applyPropBinop (thm : Name) (v w : Tm .width) : MetaM (MVarId × WidthInfos × Expr) := do
    let (g, vInfo, widthInfos) ← getOrCreateWidthMask g v widthInfos
    let (g, wInfo, widthInfos) ← getOrCreateWidthMask g w widthInfos
    let expr ← g.withContext <| mkAppM thm #[
          .fvar vInfo.hypWidthLeBoundNote,
          .fvar wInfo.hypWidthLeBoundNote,
          .fvar vInfo.widthMaskHypFvar,
          .fvar wInfo.widthMaskHypFvar,
          proof,
        ]
    return (g, widthInfos, expr)
  -- Recurse over the prop structure
  match prop with
  | .widthLt v w => applyPropBinop ``lt_of_lt_of_eq_maskOfWidth v w
  | .widthLe v w => applyPropBinop ``le_of_le_of_eq_maskOfWidth v w
  | .widthEq v w => applyPropBinop ``eq_of_eq_of_eq_maskOfWidth v w
  | .and a b => do
    let (g, widthInfos, aExpr) ←
      getMaskedExprFromProp g a (← mkAppM ``And.left  #[proof]) widthInfos
    let (g, widthInfos, bExpr) ←
      getMaskedExprFromProp g b (← mkAppM ``And.right #[proof]) widthInfos
    let expr ← g.withContext <| mkAppM ``And.intro #[aExpr, bExpr]
    return (g, widthInfos, expr)

/-- Construct the mask `Expr` for each `WidthProp` and add it to the context. -/
public meta def WidthProps.translateToMask (this : WidthProps) (g : MVarId) (widthInfos : WidthInfos) : MetaM (MVarId × WidthInfos) := do
  this.props.foldM (init := (g, widthInfos)) fun (g, infos) name widthProp => do
    -- Obtain the `Expr` of the prop in terms of the mask.
    let (g, infos, expr) ← getMaskedExprFromProp g widthProp.term widthProp.proof infos
    -- State the prop in terms of the masks.
    let (_, g) ← g.note (Name.mkSimple s!"bv_{name}") expr
    return (g, infos)

/--
Given the width terms in the formula, translate all `Nat` widths into `BitVec`
masks and introduce the hypotheses that model the masks.
-/
public meta def introMaskWidths (g : MVarId) (widthTms : WidthTms) (blastWidth : Nat)
  : MetaM (MVarId × WidthInfos)
  := g.withContext do
  -- Intro all the masks
  widthTms.terms.foldM
    (init := (g, { env := widthTms.env, blastWidth }))
    fun (g, widthInfos) _ widthTm => do
      let (g, _, infos) ← getOrCreateWidthMask g widthTm.term widthInfos
      return (g, infos)

end Veir.Meta.Tactic.PBVDecide
