import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas

set_option warn.sorry false

namespace Veir
namespace Example

variable {OpInfo : Type} [HasOpInfo OpInfo]

theorem matchOp_implies :
  matchOp op ctx opType numOperands = some (operands, properties) →
  op.getOpType! ctx = opType ∧
  op.getNumOperands! ctx = numOperands ∧
  op.getNumResults! ctx = 1 ∧
  operands = op.getOperands! ctx ∧
  properties = op.getProperties! ctx opType := by
  simp only [matchOp]
  simp only [guard, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, ite_eq_left_iff,
    reduceCtorEq, imp_false, Decidable.not_not, Option.some.injEq, Prod.mk.injEq, exists_const,
    and_imp]
  intros
  grind

theorem matchOp_interpretOp
  {state : InterpreterState ctx}
  (hmatch : matchOp op ctx opType numOperands = some (operands, properties)) :
  interpretOp op state opInBounds = some (.ok (newState, cf)) →
  ∃ values newValue newMem newVarState,
    operands.mapM state.variables.getVar? = some values ∧
    interpretOp' opType properties (op.getResultTypes! ctx.raw) values (op.getSuccessors! ctx.raw) state.memory =
      some (.ok (#[newValue], newMem, cf)) ∧
    state.variables.setVar? (op.getResult 0) newValue (by grind [→ matchOp_implies]) = some newVarState ∧
    newState = ⟨newVarState, newMem⟩ := by
  intro hinterp
  have ⟨hOpType, hNumOperands, hNumResults, hOperands, hProperties⟩ := matchOp_implies hmatch
  subst opType properties
  simp only [interpretOp] at hinterp
  split at hinterp; rotate_left; grind; rename_i _ values hValues
  exists values
  simp only [bind] at hinterp
  split at hinterp; grind; grind; rename_i _ res hinterp'
  have ⟨resValues, resMem, cf⟩ := res
  have : resValues.size = 1 := by sorry -- Missing lemma about number of results and interpretation
  exists resValues[0]
  have : resValues = #[resValues[0]] := by grind
  simp only [liftM, monadLift, MonadLift.monadLift, pure, Interp] at hinterp
  split at hinterp; grind; grind; rename_i hinterpSetValues
  simp only [VariableState.setResultValues?, hNumResults, VariableState.setResultValues?_loop]
    at hinterpSetValues
  grind [cases InterpreterState, VariableState.getOperandValues]

def matchAddi (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.arith .addi)) := do
  let (op, properties) ← matchOp op ctx (.arith .addi) 2
  return (op[0]!, op[1]!, properties)

theorem matchAddi_implies :
  matchAddi op ctx = some (lhs, rhs, properties) →
  op.getOpType! ctx = .arith .addi ∧
  op.getNumResults! ctx = 1 ∧
  op.getOperands! ctx = #[lhs, rhs] ∧
  op.getOperand! ctx 0 = lhs ∧
  op.getOperand! ctx 1 = rhs ∧
  properties = op.getProperties! ctx (.arith .addi) := by
  intro hmatch
  simp only [matchAddi, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq, Prod.exists] at hmatch
  grind [matchOp_implies]

theorem matchAddi_interpretOp
  {state : InterpreterState ctx}
  (opInBounds : op.InBounds ctx.raw)
  (hmatch : matchAddi op ctx = some (lhs, rhs, properties)) :
  interpretOp op state opInBounds = some (newState, cf) →
  ∃ lhsVal rhsVal newValue mem' newVarState,
    state.variables.getVar? lhs = some lhsVal ∧
    state.variables.getVar? rhs = some rhsVal ∧
    interpretOp' (.arith .addi) properties (op.getResultTypes! ctx.raw) #[lhsVal, rhsVal] #[] state.memory = some (#[newValue], mem', cf) ∧
    state.variables.setVar? (op.getResult 0) newValue (by grind [→ matchAddi_implies]) = some newVarState ∧
    newState = ⟨newVarState, newState.memory⟩ := by
  sorry

theorem interpretOp'_arith_addi_eq_some_implies :
    interpretOp' (OpCode.arith Arith.addi) properties #[resType] #[lhsVal, rhsVal] #[] memory = some (#[res], memory', cf) →
    ∃ bw intLhs intRhs,
    lhsVal = .int bw intLhs ∧
    rhsVal = .int bw intRhs ∧
    res = .int bw (intLhs.add intRhs properties.nsw properties.nuw) ∧
    cf = none ∧
    memory = memory' := by
  intro h
  sorry

theorem matchAddi_interpretOp_unfold {state : InterpreterState ctx} (opInBounds : op.InBounds ctx.raw) :
    matchAddi op ctx = some (lhs, rhs, properties) →
    interpretOp op state opInBounds = some (newState, cf) →
    ∀ bw isType, lhs.getType! ctx.raw = ⟨Attribute.integerType (IntegerType.mk bw), isType⟩ →
    ∃ intLhs intRhs,
    state.variables.getVar? lhs = some (RuntimeValue.int bw intLhs) ∧
    state.variables.getVar? rhs = some (RuntimeValue.int bw intRhs) ∧
    newState.variables.getVar? (op.getResult 0) = some (RuntimeValue.int bw (intLhs.add intRhs properties.nsw properties.nuw)) ∧
    cf = none := by
  sorry

def matchConstantOp (op : OperationPtr) (ctx : IRContext OpCode) : Option IntegerAttr := do
  let .arith .constant := op.getOpType! ctx | none
  let properties := op.getProperties! ctx (.arith .constant)
  return properties.value

theorem matchConstantOp_implies :
    matchConstantOp op ctx = some properties →
    op.getOpType! ctx = .arith .constant ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[] ∧
    properties = (op.getProperties! ctx (.arith .constant)).value := by
  sorry

theorem matchConstantOp_interpretOp' {state : InterpreterState ctx}
    (opInBounds : op.InBounds ctx.raw) :
    matchConstantOp op ctx = some (properties) →
    interpretOp op state opInBounds = some (newState, cf) →
    ∃ newValue,
      newState.variables.getVar? (op.getResult 0) = some newValue ∧
      interpretOp' (.arith .constant) (ArithConstantProperties.mk properties) #[((op.getResult 0).get! ctx.raw).type] #[] #[] state.memory = some (#[newValue], newState.memory, cf) := by
  sorry

theorem interpretOp'_arith_constant_eq_some_implies :
    interpretOp' (OpCode.arith Arith.constant) properties #[resType] #[] #[] memory = some (#[res], newMemory, cf) →
    ∃ intType,
    resType = Attribute.integerType intType ∧
    res = RuntimeValue.int intType.bitwidth (Data.LLVM.Int.val (BitVec.ofInt intType.bitwidth properties.value.value)) ∧
    cf = none ∧
    memory = newMemory := by
  unfold interpretOp'
  simp only [bind, liftM, monadLift, MonadLift.monadLift]
  sorry
  -- grind

theorem matchConstantOp_interpretOp_unfold {state : InterpreterState ctx} (opInBounds : op.InBounds ctx.raw) :
    matchConstantOp op ctx = some properties →
    interpretOp op state opInBounds = some (newState, cf) →
    newState.variables.getVar? (op.getResult 0) = some (RuntimeValue.int properties.type.bitwidth (Data.LLVM.Int.val (BitVec.ofInt properties.type.bitwidth properties.value))) ∧
    cf = none := by
  sorry
  --grind [matchConstantOp_interpretOp', interpretOp'_arith_constant_eq_some_implies]

theorem matchConstantOp_interpretOp_unfold' {state : InterpreterState ctx} (opInBounds : op.InBounds ctx.raw) :
    matchConstantOp op ctx = some properties →
    interpretOp op state opInBounds = some (newState, cf) →
    ∀ bw, bw = properties.type.bitwidth →
    newState.variables.getVar? (op.getResult 0) = some (RuntimeValue.int bw (Data.LLVM.Int.val (BitVec.ofInt bw properties.value))) ∧
    cf = none := by
  grind [matchConstantOp_interpretOp_unfold]

def addIConstantFolding (ctx: WfIRContext OpCode) (op: OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  -- Match an `arith.addi`
  let (lhs, rhs, addProp) ← matchAddi op ctx
  if addProp.nsw || addProp.nuw then
    return (ctx, none)
  let lhsOp ← lhs.getDefiningOp! ctx.raw
  let rhsOp ← rhs.getDefiningOp! ctx.raw
  let lhsConst ← matchConstantOp lhsOp ctx
  let rhsConst ← matchConstantOp rhsOp ctx

  -- Sum both constant values
  let ⟨.integerType intType, _⟩ := lhs.getType! ctx.raw | none
  let newConst := ArithConstantProperties.mk (IntegerAttr.mk ((BitVec.ofInt intType.bitwidth lhsConst.value) + (BitVec.ofInt intType.bitwidth rhsConst.value)).toInt intType)
  let (ctx, newOp) ← WfRewriter.createOp ctx (.arith .constant) #[intType] #[] #[] #[] newConst none (by grind) (by grind) (by grind) (by grind)
  return (ctx, some (#[newOp], #[newOp.getResult 0]))

theorem ValuePtr.getDefiningOp!.numResults_zero {ctx : IRContext OpInfo} {op : OperationPtr} {value : ValuePtr} :
    value.getDefiningOp! ctx = op →
    op.getNumResults! ctx = 1 →
    value = op.getResult 0 := by
  sorry

grind_pattern ValuePtr.getDefiningOp!.numResults_zero =>
    value.getDefiningOp! ctx, op.getNumResults! ctx

theorem addIConstantFolding_preservesSemantics :
    LocalRewritePattern.PreservesSemantics addIConstantFolding h h₂ h₃ h₄ := by
  -- Unfold definition
  simp only [LocalRewritePattern.PreservesSemantics, addIConstantFolding]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern

  -- Peel matchAddi
  try simp only [Option.bind_eq_some_iff] at hpattern
  have ⟨⟨lhs, rhs, properties⟩, matchAdd, hpattern'⟩ := hpattern
  clear hpattern; have hpattern := hpattern'; clear hpattern'
  have ⟨_, _, _, _, _, _⟩ := matchAddi_implies matchAdd
  have : op.Verified ctx := by grind
  have ⟨_, _, _, _, intType, ⟨_, _, _⟩⟩ := OperationPtr.Verified.arith_addi this (by grind)
  have ⟨intLhs, intRhs, hIntLhs, hIntRhs, hAddRes, hCf⟩ := matchAddi_interpretOp_unfold (by grind) matchAdd hinterp intType.bitwidth (by grind) (by grind [cases IntegerType])
  subst hCf
  simp only at hpattern
  have : lhs.dominatesIp (InsertPoint.before op) ctx := by sorry
  have : rhs.dominatesIp (InsertPoint.before op) ctx := by sorry

  -- Peel properties condition
  split at hpattern; grind; rename_i hProperties

  -- Peel getDefiningOp
  simp only [Option.bind_eq_some_iff] at hpattern
  have ⟨lhsOp, hLhsOp, hpattern'⟩ := hpattern
  clear hpattern; have hpattern := hpattern'; clear hpattern'

  -- Peel getDefiningOp
  try simp only [Option.bind_eq_some_iff] at hpattern
  have ⟨rhsOp, hRhsOp, hpattern'⟩ := hpattern
  clear hpattern; have hpattern := hpattern'; clear hpattern'

  -- Peel matchConstantOp for lhs
  try simp only [Option.bind_eq_some_iff] at hpattern
  have ⟨constLhs, matchLhs, hpattern'⟩ := hpattern; clear hpattern; have hpattern := hpattern'; clear hpattern'
  have ⟨_, _, _, _⟩ := matchConstantOp_implies matchLhs
  have : lhsOp.Verified ctx := by grind
  have ⟨_, _, _, _, _⟩ := OperationPtr.Verified.arith_constant this (by grind)
  have : lhs = ValuePtr.opResult (lhsOp.getResult 0) := by grind
  subst this
  have ⟨_, interpLhs⟩ := stateWf lhsOp (by grind) (by sorry) (by grind)
  have ⟨hResLhs, hCfLhs⟩ := matchConstantOp_interpretOp_unfold' (by grind) matchLhs interpLhs intType.bitwidth (by grind)
  subst hCfLhs

  -- Peel matchConstantOp for rhs
  try simp only [Option.bind_eq_some_iff] at hpattern
  have ⟨constRhs, matchRhs, hpattern'⟩ := hpattern; clear hpattern; have hpattern := hpattern'; clear hpattern'
  have ⟨_, _, _, _⟩ := matchConstantOp_implies matchRhs
  have : rhsOp.Verified ctx := by grind
  have ⟨_, _, _, _, _⟩ := OperationPtr.Verified.arith_constant this (by grind)
  have : rhs = ValuePtr.opResult (rhsOp.getResult 0) := by grind
  subst this
  have ⟨_, interpRhs⟩ := stateWf rhsOp (by grind) (by sorry) (by grind)
  have ⟨hResRhs, hCfRhs⟩ := matchConstantOp_interpretOp_unfold' (by grind) matchRhs interpRhs intType.bitwidth (by grind)
  subst hCfRhs

  -- Peel splittable condition
  split at hpattern; rotate_left; grind; rename_i intType' _ _
  have : intType = intType' := by grind
  subst intType'

  -- Peel op creation
  try simp only [Option.bind_eq_some_iff] at hpattern
  have ⟨⟨newCtx, newOp⟩, hNewCtx, hpattern'⟩ := hpattern
  clear hpattern; have hpattern := hpattern'; clear hpattern'

  -- Cleanup rest of hpattern
  simp at hpattern; have ⟨ha, hb, hc⟩ := hpattern; clear hpattern
  subst ha hb hc

  -- Propagate information between hypotheses
  simp [hIntLhs] at hResLhs
  simp [hIntRhs] at hResRhs
  subst intLhs intRhs
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] by sorry] at hsourceValues
  simp at hsourceValues
  simp [hAddRes] at hsourceValues
  subst sourceValues

  -- simplify the interpretation of the new constant op
  simp [interpretOpList, interpretOp, VariableState.getOperandValues, OperationPtr.interpret]
  simp_getset; simp
  simp [bind, liftM, monadLift, MonadLift.monadLift, pure]
  rw [show newOp.getOpType! newCtx.raw = .arith .constant by grind]
  simp_getset; simp
  simp [interpretOp', Arith.interpretOp']
  simp [bind, pure]
  simp [VariableState.setResultValues?]
  simp_getset; simp
  simp [VariableState.setResultValues?_loop]
  rw [VariableState.setVar?_eq_some_setVar (by simp only [RuntimeValue.Conforms]; simp_getset; simp)]
  simp [Interp]
  constructor; sorry -- Missing info from somewhere, should be easy to grab
  simp [VariableState.getVar?_of_setVar]

  simp [show properties.nsw = false by grind, show properties.nuw = false by grind]
  simp [RuntimeValue.arrayIsRefinedBy, RuntimeValue.isRefinedBy, isRefinedBy]
  simp [Data.LLVM.Int.add, Id.run, ←BitVec.toInt_inj]


open Lean Meta Elab Tactic in
/-- Search the local context for a hypothesis `interpretOp ctx op state = some (newState, cf)`
    where `op` matches `opFVarId`. Returns the `FVarId` of the hypothesis so callers can use
    it programmatically inside other `elab` tactics.
    If no such hypothesis is found, falls back to finding a `state.EquationLemmaAt ctx ...`
    hypothesis, calling it with `op (by grind) (by sorry) (by grind)`, and returning the
    resulting `state.EquationHolds ctx op` hypothesis. -/
def findInterpHypFVar (opFVarId : FVarId) : TacticM FVarId := withMainContext do
  let lctx ← getLCtx
  for ldecl in lctx do
    let ty := ldecl.type
    if !ty.isAppOfArity `Eq 3 then continue
    let eqLhs := ty.appFn!.appArg!
    let fn := eqLhs.getAppFn
    unless fn.isConst && fn.constName! == `Veir.interpretOp do continue
    unless eqLhs.getAppArgs.any (fun a => a.isFVar && a.fvarId! == opFVarId) do continue
    return ldecl.fvarId
  -- Fallback: find a `state.EquationLemmaAt ctx ...` hypothesis and call it to derive EquationHolds
  let mut eqLemmaFvar? : Option FVarId := none
  for ldecl in lctx do
    let fn := ldecl.type.getAppFn
    unless fn.isConst && fn.constName! == `Veir.InterpreterState.EquationLemmaAt do continue
    eqLemmaFvar? := some ldecl.fvarId
    break
  let some eqLemmaFvar := eqLemmaFvar? |
    throwError "findInterpHyp: no hypothesis of the form 'interpretOp ctx op state = some ...' or 'state.EquationLemmaAt ctx ...'"
  let eqLemmaIdent := mkIdent (← eqLemmaFvar.getUserName)
  let opIdent := mkIdent (← opFVarId.getUserName)
  let freshHoldsName ← mkFreshUserName `hEquationHolds
  let holdsIdent := mkIdent freshHoldsName
  let freshInterpName ← mkFreshUserName `hInterpEq
  let interpIdent := mkIdent freshInterpName
  evalTactic (← `(tactic|
    ( have $holdsIdent := $eqLemmaIdent $opIdent (by grind) (by sorry) (by grind)
      obtain ⟨_, $interpIdent⟩ := $holdsIdent )
  ))
  withMainContext do
    let lctx ← getLCtx
    for ldecl in lctx do
      if ldecl.userName == freshInterpName then
        return ldecl.fvarId
    throwError "findInterpHyp: failed to introduce interpretOp equation from EquationLemmaAt"

open Lean Meta Elab Tactic in
/-- Convenience wrapper: elaborates `opSyntax` as a local variable and returns the `ident` of the
    matching `interpretOp` hypothesis. Usable directly inside `elab` tactic handlers. -/
def findInterpHypIdent (opSyntax : TSyntax `ident) : TacticM (TSyntax `ident) :=
  withMainContext do
    let opExpr ← Elab.Tactic.elabTerm opSyntax none
    unless opExpr.isFVar do
      throwErrorAt opSyntax "expected a local variable"
    let fvar ← findInterpHypFVar opExpr.fvarId!
    withMainContext do
      return mkIdent (← fvar.getUserName)

open Lean Meta Elab Tactic in
elab "substOpResult" opName:ident : tactic => withMainContext do
  -- Elaborate opName to get the fvar for e.g. lhsOp
  let opExpr ← Elab.Tactic.elabTerm opName none
  unless opExpr.isFVar do
    throwErrorAt opName "substOpResult: expected a local variable"
  let opFVarId := opExpr.fvarId!
  let lctx ← getLCtx
  -- Search for a hypothesis `lhs.getDefiningOp! ... = some lhsOp`
  let mut lhsName? : Option Name := none
  for ldecl in lctx do
    let ty := ldecl.type
    if !ty.isAppOfArity `Eq 3 then continue
    let eqLhs := ty.appFn!.appArg!
    let eqRhs := ty.appArg!
    if !eqRhs.isAppOfArity `Option.some 2 then continue
    if eqRhs.appArg!.fvarId? != some opFVarId then continue
    let fn := eqLhs.getAppFn
    if !fn.isConst then continue
    let isGetDefiningOp := match fn.constName! with | .str _ s => s.startsWith "getDefiningOp" | _ => false
    if !isGetDefiningOp then continue
    -- Find the ValuePtr fvar among the args of getDefiningOp
    let mut foundLhs? : Option Expr := none
    for arg in eqLhs.getAppArgs do
      if !arg.isFVar then continue
      let argTy ← inferType arg
      if let some (.str _ "ValuePtr") := argTy.getAppFn.constName? then
        foundLhs? := some arg
        break
    let some lhsArg := foundLhs? | continue
    let some lhsDecl := lctx.find? lhsArg.fvarId! | continue
    lhsName? := some lhsDecl.userName
    break
  let lhsName ← match lhsName? with
    | some n => pure n
    | none => throwError "substOpResult: no hypothesis of the form 'lhs.getDefiningOp! ... = some {opName.getId}'"
  let lhsIdent := mkIdent lhsName
  let opGetResult ← `($(opName).getResult 0)
  evalTactic (← `(tactic| (
    have : $lhsIdent = ValuePtr.opResult $opGetResult := by grind
    subst this
  )))

open Lean Meta Elab Tactic in
elab "peelMatchAddi" suffix:str op:ident hpattern:ident ctx:ident bwName:ident bwVal:("(" term ")")? : tactic => do
  let suffix := suffix.getString
  let mk (base : String) : TSyntax `ident := mkIdent (.mkSimple (base ++ suffix))
  let bwExpr : TSyntax `term ← match bwVal with
    | none => `($(mk "intType").bitwidth)
    | some val => pure (⟨val.raw[1]⟩ : TSyntax `term)
  let interpHypIdent ← findInterpHypIdent op
  evalTactic (← `(tactic|
    ( /- First, grab the new variables from the pattern -/
     try simp only [Option.bind_eq_some_iff] at $hpattern:ident
     have ⟨⟨$(mk "lhs"), $(mk "rhs"), $(mk "properties")⟩, $(mk "matchAdd"), pat'⟩ := $hpattern
     clear $hpattern; have $hpattern := pat'; clear pat'
     /- Get the information gathered from `matchAddi` and verification of the op -/
     have ⟨_, _, _, _, _, _⟩ := matchAddi_implies $(mk "matchAdd")
     have : ($op:ident).Verified $ctx:ident := by grind
     have ⟨_, _, _, _, $(mk "intType"), ⟨_, _, _⟩⟩ := OperationPtr.Verified.arith_addi this (by grind)
     try substOpResult $op:ident
     let $bwName:ident := $bwExpr
     have ⟨$(mk "intLhs"), $(mk "intRhs"), $(mk "hIntLhs"), $(mk "hIntRhs"), $(mk "hAddRes"), $(mk "hCf")⟩ :=
       matchAddi_interpretOp_unfold (by grind) $(mk "matchAdd") $interpHypIdent $bwName:ident (by grind) (by grind [cases IntegerType])
     subst $(mk "hCf")
     simp only at $hpattern:ident
     have : $(mk "lhs").dominatesIp (InsertPoint.before $op:ident) $ctx:ident := by sorry
     have : $(mk "rhs").dominatesIp (InsertPoint.before $op:ident) $ctx:ident := by sorry
     )))

open Lean Meta Elab Tactic in
elab "peelMatchConstantOp" suffix:str op:ident hpattern:ident ctx:ident bwVal:term : tactic => do
  let suffix := suffix.getString
  let mk (base : String) : TSyntax `ident := mkIdent (.mkSimple (base ++ suffix))
  let bwExpr : TSyntax `term := bwVal
  let interpHypIdent ← findInterpHypIdent op
  evalTactic (← `(tactic|
    ( try simp only [Option.bind_eq_some_iff] at $hpattern:ident
      have ⟨$(mk "const"), $(mk "match"), pat'⟩ := $hpattern; clear $hpattern; have $hpattern := pat'; clear pat'
      have ⟨_, _, _, _⟩ := matchConstantOp_implies $(mk "match")
      have : ($op:ident).Verified $ctx:ident := by grind
      have ⟨_, _, _, _, _⟩ := OperationPtr.Verified.arith_constant this (by grind)
      try substOpResult $op:ident
      have ⟨$(mk "hRes"), $(mk "hCf")⟩ := matchConstantOp_interpretOp_unfold' (by grind) $(mk "match") $interpHypIdent $bwExpr (by grind)
      subst $(mk "hCf")
    )))

open Lean in
macro "peelGetDefiningOp" opName:ident hOpName:ident hpattern:ident : tactic =>
  `(tactic| (
      try simp only [Option.bind_eq_some_iff] at $hpattern:ident
      have ⟨$opName, $hOpName, pat'⟩ := $hpattern:ident
      clear $hpattern:ident; have $hpattern:ident := pat'; clear pat'
     ))

open Lean in
macro "peelSplittableCondition" "[" hyps:binderIdent* "]" hpattern:ident : tactic =>
  `(tactic| (
      split at $hpattern:ident; grind; rename_i $[$hyps]*
      try simp at $hpattern:ident
     ))

open Lean in
macro "peelSplittableCondition'" "[" hyps:binderIdent* "]" hpattern:ident : tactic =>
  `(tactic| (
      split at $hpattern:ident; rotate_left; grind; rename_i $[$hyps]*
      try simp at $hpattern:ident
     ))

open Lean in
macro "cleanupHpattern" hpattern:ident : tactic =>
  `(tactic| (
      simp at $hpattern:ident; have ⟨ha, hb, hc⟩ := $hpattern:ident; clear $hpattern:ident
      subst ha hb hc
     ))

open Lean in
macro "peelOpCreation" hpattern:ident newCtx:ident newOp:ident hNewCtx:ident : tactic =>
  `(tactic| (
      try simp only [Option.bind_eq_some_iff] at $hpattern:ident
      have ⟨⟨$newCtx, $newOp⟩, $hNewCtx, pat'⟩ := $hpattern:ident
      clear $hpattern:ident; have $hpattern:ident := pat'; clear pat'
     ))

theorem addIConstantFolding_preservesSemantics_peel :
    LocalRewritePattern.PreservesSemantics addIConstantFolding h h₁ h₂ h₃ := by
  -- Unfold definition and cleanup hypotheses
  simp only [LocalRewritePattern.PreservesSemantics, addIConstantFolding]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern

  -- Process hpattern
  peelMatchAddi "" op hpattern ctx bw
  peelSplittableCondition [hproperties] hpattern
  peelGetDefiningOp lhsOp hLhsOp hpattern
  peelGetDefiningOp rhsOp hRhsOp hpattern
  peelMatchConstantOp "Lhs" lhsOp hpattern ctx bw
  peelMatchConstantOp "Rhs" rhsOp hpattern ctx bw
  peelSplittableCondition' [intType' _ _] hpattern
  peelOpCreation hpattern newCtx newOp hNewCtx
  cleanupHpattern hpattern

  -- Plug input/output information between match instructions
  simp [hIntLhs] at hResLhs
  simp [hIntRhs] at hResRhs
  subst intLhs intRhs
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] by sorry] at hsourceValues
  simp at hsourceValues
  simp [hAddRes] at hsourceValues
  subst sourceValues
  have : intType = intType' := by grind
  subst intType'
  subst bw

  -- simplify the interpretation of the new constant op
  simp [interpretOpList, interpretOp, VariableState.getOperandValues, OperationPtr.interpret]
  simp_getset; simp
  simp [bind, liftM, monadLift, MonadLift.monadLift, pure]
  rw [show newOp.getOpType! newCtx.raw = .arith .constant by grind]
  simp_getset; simp
  simp [interpretOp', Arith.interpretOp']
  simp [bind, pure]
  simp [VariableState.setResultValues?]
  simp_getset; simp
  simp [VariableState.setResultValues?_loop]
  rw [VariableState.setVar?_eq_some_setVar (by simp only [RuntimeValue.Conforms]; simp_getset; simp)]
  simp [Interp]
  constructor; sorry -- Missing info from somewhere, should be easy to grab
  simp [VariableState.getVar?_of_setVar]

  simp [show properties.nsw = false by grind, show properties.nuw = false by grind]
  simp [RuntimeValue.arrayIsRefinedBy, RuntimeValue.isRefinedBy, isRefinedBy]
  simp [Data.LLVM.Int.add, Id.run, ←BitVec.toInt_inj]

theorem RuntimeValue.isRefinedBy.int_of_refinement :
    RuntimeValue.int bw intLhs ⊒ intLhs' →
    ∃ intLhs'', intLhs' = RuntimeValue.int bw intLhs'' := by
  simp [RuntimeValue.isRefinedBy]
  grind

def addIComm (ctx: WfIRContext OpCode) (op: OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  -- Match an `arith.addi`
  let (lhs, rhs, addProp) ← matchAddi op ctx

  -- Commutes it
  let ⟨.integerType intType, _⟩ := (lhs.getType! ctx.raw) | none
  let (ctx, newOp) ← WfRewriter.createOp ctx (.arith .addi) #[intType] #[rhs, lhs] #[] #[] addProp none sorry (by grind) (by grind) (by grind)
  return (ctx, some (#[newOp], #[newOp.getResult 0]))

theorem addIComm_preservesSemantics :
    LocalRewritePattern.PreservesSemantics addIComm h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  have hpattern_fold := hpattern
  simp [addIComm, Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern

  peelMatchAddi "" op hpattern ctx bw
  peelSplittableCondition' [intType' _ _] hpattern
  peelOpCreation hpattern newCtx newOp hNewCtx
  cleanupHpattern hpattern

  -- Resolve the new state values
  simp [liftM, monadLift, MonadLift.monadLift, Interp]
  simp [interpretOpList, interpretOp, VariableState.getOperandValues, OperationPtr.interpret]
  simp_getset; simp

  subst bw
  have : intType' = intType := by grind
  subst intType'

  -- Use state refinement to get the new values
  have := valueRefinement lhs (by grind) _ hIntLhs
  simp only [LocalRewritePattern.mapping] at this
  have lhsNotOp : ¬ lhs ∈ op.getResults! ctx.raw := by sorry
  simp [lhsNotOp] at this
  have ⟨lhsVar', hLhsVar', hLhsVarRef⟩ := this; clear this

  have := valueRefinement rhs (by grind) _ hIntRhs
  simp only [LocalRewritePattern.mapping] at this
  have rhsNotOp : ¬ rhs ∈ op.getResults! ctx.raw := by sorry
  simp [rhsNotOp] at this
  have ⟨rhsVar', hRhsVar', hRhsVarRef⟩ := this; clear this

  have ⟨intLhs₂, hIntLhs₂⟩ := RuntimeValue.isRefinedBy.int_of_refinement hLhsVarRef
  subst lhsVar'
  have ⟨intRhs₂, hIntRhs₂⟩ := RuntimeValue.isRefinedBy.int_of_refinement hRhsVarRef
  subst rhsVar'
  simp only [hRhsVar', hLhsVar', Option.bind_some, Function.comp_apply, Option.map_some]

  rw [show newOp.getOpType! newCtx.raw = .arith .addi by grind]
  simp_getset; simp
  simp [interpretOp', Arith.interpretOp']
  simp [pure, liftM, monadLift, MonadLift.monadLift, Interp, bind]
  simp [VariableState.setResultValues?]
  simp_getset; simp
  simp [VariableState.setResultValues?_loop]
  rw [VariableState.setVar?_eq_some_setVar (by simp only [RuntimeValue.Conforms]; simp_getset; simp)]
  simp
  constructor; sorry -- Missing info from somewhere, should be
  simp [VariableState.getVar?_of_setVar]
  simp [show (op.getResults ctx.raw (by grind)) = #[ValuePtr.opResult (op.getResult 0)] by grind] at hsourceValues
  simp [hAddRes] at hsourceValues
  subst sourceValues
  simp [RuntimeValue.arrayIsRefinedBy, RuntimeValue.isRefinedBy, isRefinedBy]
  sorry -- lemma with refinement

def addIAssoc (ctx: WfIRContext OpCode) (op: OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  -- Match an (x + y) + z
  let (lhs, z, addProp) ← matchAddi op ctx
  if addProp.nsw || addProp.nuw then
    return (ctx, none)

  let lhsOp ← lhs.getDefiningOp! ctx.raw
  let (x, y, addProp') ← matchAddi lhsOp ctx
  if addProp'.nsw || addProp'.nuw then
    return (ctx, none)

  let ⟨.integerType intType, _⟩ := (lhs.getType! ctx.raw) | none
  -- Create (y + z)
  let (ctx, newOp) ← WfRewriter.createOp ctx (.arith .addi) #[intType] #[y, z] #[] #[] addProp none sorry sorry sorry sorry
  -- Create x + (y + z)
  let (ctx, newOp') ← WfRewriter.createOp ctx (.arith .addi) #[intType] #[x, newOp.getResult 0] #[] #[] addProp' none sorry sorry sorry sorry
  return (ctx, some (#[newOp, newOp'], #[newOp'.getResult 0]))

theorem addIAssoc_preservesSemantics :
    LocalRewritePattern.PreservesSemantics addIAssoc h h₂ h₃ h₄ := by
  -- Unfold definition and cleanup hypotheses
  simp only [LocalRewritePattern.PreservesSemantics, addIAssoc]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern

  peelMatchAddi "" op hpattern ctx bw
  peelSplittableCondition [hproperties] hpattern
  peelGetDefiningOp lhsOp hLhsOp hpattern
  peelMatchAddi "Lhs" lhsOp hpattern ctx bw'
  peelSplittableCondition [hproperties'] hpattern
  peelSplittableCondition' [intType' _ _] hpattern
  peelOpCreation hpattern newCtx newOp hNewCtx
  peelOpCreation hpattern newCtx' newOp' hNewCtx'
  cleanupHpattern hpattern

  have : bw = bw' := by grind
  subst bw
  subst bw'

  simp [*]
  have : intType = intTypeLhs := by grind
  subst intTypeLhs
  simp [hIntLhs] at hAddResLhs; subst hAddResLhs

  simp [interpretOpList, interpretOp, VariableState.getOperandValues, OperationPtr.interpret]
  simp_getset; simp
  have : newOp ≠ newOp' := by grind
  have : newOp' ≠ newOp := by grind
  simp [*]
  rw [show newOp.getOpType! newCtx'.raw = .arith .addi by grind]
  rw [show newOp'.getOpType! newCtx'.raw = .arith .addi by grind]
  simp [interpretOp']
  simp [Arith.interpretOp']

  -- Use state refinement to get the new values
  have := valueRefinement lhsLhs (by grind) _ hIntLhsLhs
  simp only [LocalRewritePattern.mapping] at this
  have lhsNotOp : ¬ lhsLhs ∈ op.getResults! ctx.raw := by sorry
  simp [lhsNotOp] at this
  have ⟨lhsLhsVar', hlhsLhsVar', hlhsLhsVarRef⟩ := this; clear this
  have ⟨intLhs₂, hIntLhs₂⟩ := RuntimeValue.isRefinedBy.int_of_refinement hlhsLhsVarRef
  subst lhsLhsVar'
  --simp only [hlhsLhsVar', Option.bind_some, Function.comp_apply, Option.map_bind]


  have := valueRefinement rhsLhs (by grind) _ hIntRhsLhs
  simp only [LocalRewritePattern.mapping] at this
  have lhsNotOp : ¬ rhsLhs ∈ op.getResults! ctx.raw := by sorry
  simp [lhsNotOp] at this
  have ⟨rhsLhsVar', hrhsLhsVar', hrhsLhsVarRef⟩ := this; clear this
  have ⟨intLhs₂, hIntLhs₂⟩ := RuntimeValue.isRefinedBy.int_of_refinement hrhsLhsVarRef
  subst rhsLhsVar'
  simp only [hrhsLhsVar', Option.bind_some, Function.comp_apply, Option.map_bind]

  have := valueRefinement rhs (by grind) _ hIntRhs
  simp only [LocalRewritePattern.mapping] at this
  have rhsNotOp : ¬ rhs ∈ op.getResults! ctx.raw := by sorry
  simp [rhsNotOp] at this
  have ⟨rhsVar', hRhsVar', hRhsVarRef⟩ := this; clear this
  have ⟨intRhs₂, hIntRhs₂⟩ := RuntimeValue.isRefinedBy.int_of_refinement hRhsVarRef
  subst rhsVar'
  simp only [hRhsVar', Option.bind_some, Function.comp_apply, Option.map_some, ↓reduceDIte,
    Data.LLVM.Int.cast_self]

  simp only [Interp, bind, pure, liftM, monadLift, MonadLift.monadLift]

  have : intType = intType' := by grind
  subst intType'

  simp [VariableState.setResultValues?]
  simp_getset; simp
  simp [VariableState.setResultValues?_loop]
  rw [VariableState.setVar?_eq_some_setVar (by simp only [RuntimeValue.Conforms]; simp_getset; simp)]
  simp only
  simp [VariableState.getVar?_of_setVar]
  have : (op.getResults ctx.raw (by grind)) = #[ValuePtr.opResult (op.getResult 0)] := by sorry
  simp [this] at hsourceValues
  simp [hAddRes] at hsourceValues
  subst sourceValues
  have : lhsLhs ≠ ValuePtr.opResult (newOp.getResult 0) := by sorry
  simp [this]
  simp [hlhsLhsVar']
  rw [VariableState.setVar?_eq_some_setVar (by simp only [RuntimeValue.Conforms]; simp_getset; simp)]
  simp
  constructor; sorry
  simp [VariableState.getVar?_of_setVar]
  simp [RuntimeValue.arrayIsRefinedBy]
  simp [show newOp ≠ newOp' by grind]
  simp [RuntimeValue.isRefinedBy]
  sorry
