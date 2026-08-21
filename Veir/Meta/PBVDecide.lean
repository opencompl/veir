import Lean
import Veir.Data.PBV

open Lean Elab Tactic Meta

namespace Veir.Data.PBV

/-! # `pbv_decide`: reify the goal, then rewrite it into a single concrete width.

The translation is directed: the goal is reified into `Tm`, and every node of that AST has
exactly one rule attached to it in `Veir.Data.PBV.Cert`. Each rule is a lemma whose hypotheses
are the certificates for the subterms, so a node's proof is a single application and the proof
term for the whole goal is built directly. Nothing is searched for, and an operation the reifier
does not know is an error naming the subterm rather than an opaque atom that reaches `bv_decide`
and fails as though the goal were false.
-/

/-- The sorts of the reified language. -/
inductive TmKind where
  | bool
  | width
  | bv
  deriving DecidableEq, Repr

/--
A reified goal. Propositions live at `bool`, because the translation sends them to `Bool`
formulas; that is what keeps every certificate an equality (see `Veir.Data.PBV.Cert`).

Deliberately untyped in the widths: a `Tm .bv` does not record its width in its Lean type,
`bvAtom` records it as a field instead, which makes `Tm.bvWidth` structural.
-/
inductive Tm : TmKind → Type where
  /-- A decidable leaf the translation has no rule for. -/
  | boolAtom (e : Expr) : Tm .bool
  /-- A `Nat` width variable. -/
  | widthAtom (e : Expr) : Tm .width
  /-- An opaque bitvector, tagged with the width it lives at. -/
  | bvAtom (w : Tm .width) (e : Expr) : Tm .bv
  /-- A literal width. -/
  | widthLit (n : Nat) : Tm .width
  /-- Implication, which becomes `!h || c`. -/
  | imp (a b : Tm .bool) : Tm .bool
  /-- Equality of bitvectors. -/
  | eq (a b : Tm .bv) : Tm .bool
  /-- `w₁ ≤ w₂` between widths. -/
  | le (a b : Tm .width) : Tm .bool
  /-- `w₁ < w₂` between widths. -/
  | lt (a b : Tm .width) : Tm .bool
  | add (a b : Tm .bv) : Tm .bv
  | and (a b : Tm .bv) : Tm .bv
  /-- `BitVec.setWidth`, and hence `BitVec.zeroExtend`, an `abbrev` for it. -/
  | zeroExtend (tgt : Tm .width) (a : Tm .bv) : Tm .bv
  | signExtend (tgt : Tm .width) (a : Tm .bv) : Tm .bv

instance : Inhabited (Tm k) where
  default :=
    match k with
    | .bool => .boolAtom default
    | .width => .widthAtom default
    | .bv => .bvAtom (.widthAtom default) default

/-- The width a bitvector term lives at. Total and structural, because `bvAtom` carries its own
width and every width-changing operation names its target. -/
def Tm.bvWidth : Tm .bv → Tm .width
  | .bvAtom w _ => w
  | .add a _ => a.bvWidth
  | .and a _ => a.bvWidth
  | .zeroExtend tgt _ => tgt
  | .signExtend tgt _ => tgt

/-- The `Nat` this width was reified from. -/
def Tm.widthToExpr : Tm .width → Expr
  | .widthAtom e => e
  | .widthLit n => mkNatLit n

/-! ## Reification -/

/-- Reify a `Nat` occurring in width position. -/
def reifyWidth (e : Expr) : MetaM (Tm .width) := do
  match e.nat? with
  | some n => return .widthLit n
  | none => return .widthAtom e

/-- Reify an opaque bitvector, reading its width off its type. -/
def reifyBvAtom (e : Expr) : MetaM (Tm .bv) := do
  let ty ← whnf (← inferType e)
  match ty.getAppFnArgs with
  | (``BitVec, #[w]) => return .bvAtom (← reifyWidth w) e
  | _ => throwError "pbv_decide: expected a `BitVec`, got{indentExpr ty}"

/-- Bitvector constants are legitimate leaves. -/
private def isBvLeafHead (fn : Name) : Bool :=
  fn == ``BitVec.ofNat || fn == ``BitVec.ofNatLT || fn == ``BitVec.ofFin

/--
Heads that denote a bitvector operation. Reaching one that `reifyBv` did not handle means the
translation has no rule for it; treating it as an atom would hand `bv_decide` an opaque term at a
parametric width, which fails as though the goal were false. An error naming the operation is far
more useful, and says exactly which rule needs adding.
-/
private def isBvOpHead (fn : Name) : Bool :=
  ((`BitVec).isPrefixOf fn && !isBvLeafHead fn)
    || [``HMul.hMul, ``HSub.hSub, ``HDiv.hDiv, ``HMod.hMod, ``HXor.hXor, ``HOr.hOr,
        ``HShiftLeft.hShiftLeft, ``HShiftRight.hShiftRight, ``HAppend.hAppend,
        ``Neg.neg, ``Complement.complement].contains fn

partial def reifyBv (e : Expr) : MetaM (Tm .bv) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return .add (← reifyBv a) (← reifyBv b)
  | (``HAnd.hAnd, #[_, _, _, _, a, b]) => return .and (← reifyBv a) (← reifyBv b)
  | (``BitVec.setWidth, #[_, v, a]) => return .zeroExtend (← reifyWidth v) (← reifyBv a)
  | (``BitVec.zeroExtend, #[_, v, a]) => return .zeroExtend (← reifyWidth v) (← reifyBv a)
  | (``BitVec.signExtend, #[_, v, a]) => return .signExtend (← reifyWidth v) (← reifyBv a)
  | (fn, _) =>
    if isBvOpHead fn then
      throwError "pbv_decide: unsupported bitvector operation `{fn}` in{indentExpr e}"
    reifyBvAtom e

/-- A leaf with no rule of its own is still usable if it is decidable. -/
private def reifyDecidableAtom? (e : Expr) : MetaM (Option (Tm .bool)) := do
  if (← synthInstance? (← mkAppM ``Decidable #[e])).isSome then
    return some (.boolAtom e)
  return none

/-- Reify a proposition. `none` means the translation has no way to express it as a `Bool`, in
which case the caller leaves it alone rather than folding it into the goal. -/
partial def reifyBool? (e : Expr) : MetaM (Option (Tm .bool)) := do
  if e.isArrow then
    let some a ← reifyBool? e.bindingDomain! | return none
    let some b ← reifyBool? e.bindingBody! | return none
    return some (.imp a b)
  match e.getAppFnArgs with
  | (``Eq, #[ty, a, b]) =>
    match (← whnf ty).getAppFnArgs with
    | (``BitVec, _) => return some (.eq (← reifyBv a) (← reifyBv b))
    | _ => reifyDecidableAtom? e
  | (``LE.le, #[ty, _, a, b]) =>
    if ty.isConstOf ``Nat then return some (.le (← reifyWidth a) (← reifyWidth b))
    else reifyDecidableAtom? e
  | (``LT.lt, #[ty, _, a, b]) =>
    if ty.isConstOf ``Nat then return some (.lt (← reifyWidth a) (← reifyWidth b))
    else reifyDecidableAtom? e
  | _ => reifyDecidableAtom? e

/-! ## The environment produced by steps 3-5 -/

structure WidthInfo where
  /-- The `Nat` width variable this stands for. -/
  widthExpr : Expr
  /-- `m : BitVec o`, the mask naming the width. -/
  maskFVar : FVarId
  /-- `h : m = maskOfWidth o w`. -/
  maskHyp : FVarId
  /-- `?_ : w ≤ o`, returned as a side goal. -/
  bound : MVarId

structure Env where
  /-- The concrete width everything is translated to. -/
  blastWidth : Nat
  widths : Array WidthInfo

def Env.oExpr (env : Env) : Expr := mkNatLit env.blastWidth

/--
Resolve a width to `(mask, h : mask = maskOfWidth o w, h : w ≤ o)`, the three facts every
certificate lemma needs about it.
-/
def Env.resolve (env : Env) (t : Tm .width) : MetaM (Expr × Expr × Expr) := do
  match t with
  | .widthLit n =>
    -- Spelled as the concrete literal rather than `maskOfWidth o n`, so that `bv_decide` can
    -- evaluate it instead of abstracting it as an atom. The two are definitionally equal.
    let mask := mkApp2 (mkConst ``BitVec.ofNat) env.oExpr (mkNatLit (2 ^ n - 1))
    let maskOf ← mkAppM ``maskOfWidth #[env.oExpr, mkNatLit n]
    let hMask ← mkExpectedTypeHint (← mkEqRefl mask) (← mkEq mask maskOf)
    let hBound ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit n, env.oExpr])
    return (mask, hMask, hBound)
  | .widthAtom e =>
    -- Matched up to defeq, so that a width written `w + 0` finds the mask introduced for `w`.
    for info in env.widths do
      if ← isDefEq info.widthExpr e then
        return (mkFVar info.maskFVar, mkFVar info.maskHyp, .mvar info.bound)
    throwError "pbv_decide: no mask was introduced for the width{indentExpr e}"

/-! ## Directed rewriting

Each function returns the certificate for its node; the rewritten term is read off the
certificate's type, so nothing is constructed twice.
-/

/-- `pushBv env t : ⟦t⟧.setWidth o = t'`. -/
partial def pushBv (env : Env) (t : Tm .bv) : MetaM Expr := do
  match t with
  | .bvAtom w e =>
    if ← isDefEq w.widthToExpr env.oExpr then
      mkAppM ``atom_cert #[e]
    else
      -- An opaque leaf at a parametric width: widening it is the honest translation.
      mkEqRefl (← mkAppM ``BitVec.setWidth #[env.oExpr, e])
  | .add a b =>
    let (_, hMask, hBound) ← env.resolve a.bvWidth
    mkAppM ``add_cert #[hBound, ← pushBv env a, ← pushBv env b, hMask]
  | .and a b =>
    mkAppM ``and_cert #[← pushBv env a, ← pushBv env b]
  | .zeroExtend tgt a =>
    let (_, hMask, hBound) ← env.resolve tgt
    mkAppM ``setWidth_cert #[hBound, ← pushBv env a, hMask]
  | .signExtend tgt a =>
    let (_, hMaskSrc, hBoundSrc) ← env.resolve a.bvWidth
    let (_, hMaskTgt, _) ← env.resolve tgt
    let ca ← pushBv env a
    -- The `bool` certificate for the sign bit, the one place that kind is consumed.
    let cmsb ← mkAppM ``msb_cert #[hBoundSrc, ca, hMaskSrc]
    mkAppM ``signExtend_cert #[hBoundSrc, ca, cmsb, hMaskSrc, hMaskTgt]

/-- `pushBool env t : ⟦t⟧ = (t' = true)`. One direction, because the target is a `Bool` formula:
`imp` becomes `!h || c`, so the hypothesis side no longer travels against the grain. -/
partial def pushBool (env : Env) (t : Tm .bool) : MetaM Expr := do
  match t with
  | .boolAtom e => mkAppM ``decide_cert #[e]
  | .imp a b => mkAppM ``imp_cert #[← pushBool env a, ← pushBool env b]
  | .eq a b =>
    let (_, _, hBound) ← env.resolve a.bvWidth
    mkAppM ``eq_cert #[hBound, ← pushBv env a, ← pushBv env b]
  | .le a b =>
    let (_, hMaskA, hBoundA) ← env.resolve a
    let (_, hMaskB, hBoundB) ← env.resolve b
    mkAppM ``le_cert #[hBoundA, hBoundB, hMaskA, hMaskB]
  | .lt a b =>
    let (_, hMaskA, hBoundA) ← env.resolve a
    let (_, hMaskB, hBoundB) ← env.resolve b
    mkAppM ``lt_cert #[hBoundA, hBoundB, hMaskA, hMaskB]

/-- Whether a hypothesis can be folded into the goal at all. `reifyBv` throws on an operation
with no rule, which for a hypothesis just means leaving it in the local context. -/
private def reifiesAsBool (e : Expr) : MetaM Bool := do
  try
    return (← reifyBool? e).isSome
  catch _ =>
    return false

/-! ## Steps 3-4: naming masks and eliminating parametric-width variables -/

/-- Read-only configuration for the tactic. -/
structure PbvTranslateContext where
  /-- The width up to which we bitblast, and the width everything is translated to. -/
  bmcBound : Nat

/-- Eliminate one width variable, producing its mask and the masking constraint. -/
def introMaskWidth (ctx : PbvTranslateContext) (g : MVarId) (ldecl : LocalDecl) :
    MetaM (MVarId × WidthInfo) := do
  let [g] ← g.withContext do
      g.apply <| ← mkAppM ``width_elim #[mkNatLit ctx.bmcBound, ldecl.toExpr, ← g.getType]
    | throwError "width_elim should generate a goal"
  let maskName := Name.mkSimple s!"m{ldecl.userName}"
  let (mask, g) ← g.withContext do g.intro maskName
  let (maskHyp, g) ← g.withContext do g.intro (Name.mkSimple s!"h_{maskName}")
  -- The bound is a side goal. It is created here, while the user's hypotheses about the widths
  -- are still in scope, since that is what discharges it.
  let bound ← g.withContext do
    mkFreshExprMVar (← mkAppM ``LE.le #[ldecl.toExpr, mkNatLit ctx.bmcBound])
      (kind := .syntheticOpaque)
      (userName := Name.mkSimple s!"h_{ldecl.userName}_le_bound")
  -- The mask constraint, with `IsMask` unfolded, else `bv_decide` cannot use it.
  let hypExpr ← g.withContext do
    mkAppM ``and_add_one_eq_zero_of_eq_maskOfWidth #[mkFVar maskHyp]
  let (_hIsMask, g) ← g.note (Name.mkSimple s!"h_isMask_{maskName}") hypExpr
  return (g, {
    widthExpr := ldecl.toExpr
    maskFVar := mask
    maskHyp := maskHyp
    bound := bound.mvarId!
  })

/-- Every `Nat` in the context is treated as a width. -/
def natWidthDecls (g : MVarId) : MetaM (Array LocalDecl) := g.withContext do
  (← getLCtx).foldlM (init := #[]) fun acc ldecl => do
    if ldecl.isImplementationDetail then return acc
    if ← isDefEq ldecl.type (mkConst ``Nat) then return acc.push ldecl
    return acc

def introMaskWidths (ctx : PbvTranslateContext) (g : MVarId) :
    MetaM (MVarId × Array WidthInfo) := do
  let natDecls ← natWidthDecls g
  if natDecls.isEmpty then
    throwError "pbv_decide: unable to find a valid width variable."
  let mut g := g
  let mut infos : Array WidthInfo := #[]
  for ldecl in natDecls do
    let (g', info) ← introMaskWidth ctx g ldecl
    g := g'
    infos := infos.push info
  return (g, infos)

/-- Replace one parametric-width variable by a masked variable of the blast width. -/
def introVar (ctx : PbvTranslateContext) (widths : Array WidthInfo) (g : MVarId)
    (ldecl : LocalDecl) : MetaM MVarId := g.withContext do
  unless ldecl.isImplementationDetail do
    for info in widths do
      if ← isDefEq ldecl.type (mkApp (mkConst ``BitVec) info.widthExpr) then
        let (_, g) ← g.revert #[ldecl.fvarId]
        let (g :: _) ← g.withContext <| g.apply <| ← mkAppM ``var_elim
            #[mkNatLit ctx.bmcBound, info.widthExpr, .mvar info.bound]
          | throwError m!"{``var_elim} should generate a goal"
        let (_bvVar, g) ← g.intro ldecl.userName
        let (_bvHyp, g) ← g.intro <| Name.mkSimple s!"h_m{ldecl.userName}"
        return g
  return g

def introVars (ctx : PbvTranslateContext) (g : MVarId) (widths : Array WidthInfo) :
    MetaM MVarId := do
  let decls : LocalContext ← g.withContext getLCtx
  decls.foldlM (init := g) fun g ldecl => introVar ctx widths g ldecl

/-! ## The tactic -/

def pbvTranslate (g : MVarId) (ctx : PbvTranslateContext) : MetaM (List MVarId) := do
  -- The hypotheses to fold into the goal, snapshotted before we add any of our own.
  let hyps ← g.withContext do
    (← getLCtx).foldlM (init := #[]) fun acc (ldecl : LocalDecl) => do
      if ldecl.isImplementationDetail then return acc
      if ← isProp ldecl.type then return acc.push ldecl.fvarId
      return acc
  -- Steps 3-5: name a mask for every width, replace every parametric-width variable.
  let (g, widths) ← introMaskWidths ctx g
  let g ← introVars ctx g widths
  let env : Env := { blastWidth := ctx.bmcBound, widths }
  g.withContext do
    -- Only fold in hypotheses the translation can express as a `Bool`; the rest stay in the
    -- local context, where `bv_decide` can still read them.
    let mut folded : Array Expr := #[]
    for h in hyps do
      if ← reifiesAsBool (← h.getType) then folded := folded.push (mkFVar h)
    -- Step 6: reify the goal with those hypotheses in front of it, and rewrite the lot into a
    -- single `Bool` formula.
    let reverted ← mkForallFVars folded (← g.getType)
    let some tm ← reifyBool? reverted
      | throwError "pbv_decide: cannot reify the goal{indentExpr reverted}"
    let cert ← pushBool env tm
    let some (_, _, newTarget) := (← inferType cert).eq?
      | throwError "pbv_decide: expected an equality certificate for the goal"
    -- The certificate is applied back to the hypotheses immediately, so that the side goals
    -- created above keep those hypotheses in scope.
    let newG ← mkFreshExprMVar newTarget
    g.assign (mkAppN (← mkEqMPR cert newG) folded)
    return newG.mvarId! :: (widths.map (·.bound)).toList

/--
`pbv_decide` takes a `Nat` bound as input argument and uses it to translate a parametric
bitvector formula into a concrete width formula. The tactic generates one goal per width
parameter, plus one for the translated formula: the first, containing the desired concrete width
formula that can be decided using `bv_decide`; the rest containing side-goals to prove that each
width parameter is bounded by the provided bound, in the order the width parameters appear in the
local context.
-/
syntax (name := pbvDecide) "pbv_decide" optConfig (ppSpace colGt num)? : tactic

@[tactic pbvDecide]
def evalPbvDecide : Tactic := fun stx => do
  match stx with
  | `(tactic| pbv_decide $n:num) => do
      let ctx : PbvTranslateContext := { bmcBound := n.getNat }
      replaceMainGoal (← pbvTranslate (← getMainGoal) ctx)
  | _ => throwUnsupportedSyntax
