module

public meta import Lean
meta import all Lean.Elab.Tactic.Grind.Sym
public import Veir.PatternRewriter.Puddle.CTreeValidity

namespace Veir.Puddle.CTree

public section

attribute [cbv_opaque] Veir.TypeAttr.of

/- Reduce beta redexes, projections, and matches introduced by symbolic rewrites.
Unfold function-valued assignment updates explicitly so lookups with extra
arguments reduce too. Preserve comparison heads for the equality rewrite rules. -/
open Lean Meta Elab Tactic Grind in
meta def reducePuddleHead : Sym.Simp.Simproc := fun e => do
  -- The explicit metadata heads below are ordinary definitions, not just instances.
  -- Default transparency lets their dependent matches reduce; the predicate still
  -- keeps operation interpreters opaque.
  let e' ← withTransparency .default <| whnfHeadPred e fun e => do
    let head := e.getAppFn
    if #[`Bind.bind, `Pure.pure, `Option.bind,
      `Veir.HasOpInfo.getEffects, `Veir.HasOpInfo.isTerminator,
      `Veir.Puddle.IsMetadataTuple.shape,
      `Veir.Puddle.SemanticAssignment.bind, `Veir.Puddle.SemanticAssignment.bindType,
      `Veir.Puddle.SemanticAssignment.bindValue, `Veir.Puddle.SemanticAssignment.bindProperty,
      `Veir.Puddle.SemanticAssignment.getType, `Veir.Puddle.SemanticAssignment.getValue,
      `Veir.Puddle.SemanticAssignment.getTypes, `Veir.Puddle.SemanticAssignment.getValues,
      `Veir.Puddle.SemanticAssignment.getProperty,
      `Veir.Puddle.MetadataTuple.resolveSemantic, `Veir.Puddle.MetadataTuple.bindSemantic,
      `Veir.Puddle.MetadataTuple.Shape.resolveSemantic,
      `Veir.Puddle.MetadataTuple.Shape.bindSemantic,
      `Veir.Puddle.MetadataTuple.Atom.resolveSemantic,
      `Veir.Puddle.MetadataTuple.Atom.bindSemantic].any head.isConstOf then
      return true
    let .const name _ := head | return false
    if name == `BEq.beq then return false
    return (← getReducibilityStatus name) == .reducible
  if e' == e then return .rfl
  let e' ← Sym.foldProjs e'
  let e' ← Sym.shareCommon e'
  if e' == e then return .rfl
  return .step e' (← mkEqRefl e')

syntax (name := reducePuddleHeadSyntax) "puddle_head" : sym_simproc

@[sym_simproc reducePuddleHeadSyntax]
meta def elabReducePuddleHead : Lean.Elab.Tactic.Grind.SymSimprocElab := fun _ =>
  pure reducePuddleHead

/- Unlike `control`, continue into branches when a native callback's result is unknown.
Its success and failure branches must both be free of assignment bookkeeping. -/
open Lean Meta Elab Tactic Grind in
meta def reducePuddleControl : Sym.Simp.Simproc := fun e => do
  match ← Sym.Simp.simpControl e with
  | .rfl _ cd => return .rfl false cd
  | .step e' proof _ cd => return .step e' proof false cd

syntax (name := reducePuddleControlSyntax) "puddle_control" : sym_simproc

@[sym_simproc reducePuddleControlSyntax]
meta def elabReducePuddleControl : Lean.Elab.Tactic.Grind.SymSimprocElab := fun _ =>
  pure reducePuddleControl

/- Normalize assignments while retaining operation choices.
Omit arrow_telescope: Lean 4.35.0-rc1 can produce an ill-typed proof for nested
outcome implications. Conditional rules use self as their discharger. -/
register_sym_simp puddleProgram where
  pre := puddle_control
  post := ground >> rewrite [
    List.partition_eq_filter_filter, List.range_succ, List.reverse_cons,
    Veir.Puddle.CTree.MatchProg.ModelsDecls, Veir.Puddle.CTree.MatchDecl.Models,
    Veir.Puddle.CTree.CreateProg.semantics,
    Veir.Puddle.CTree.CreateProg.semanticsDecls, Veir.Puddle.CTree.CreateDecl.semantics,
    Veir.Puddle.CTree.MatchProg.rootSemantics,
    Veir.Interp.ok.injEq, Veir.Interp.ub.injEq, Veir.Interp.fail.injEq,
    Veir.Puddle.SemanticAssignment.getValues, Veir.Puddle.SemanticAssignment.getTypes,
    Veir.Puddle.SemanticAssignment.getValue, Veir.Puddle.SemanticAssignment.getType,
    Veir.Puddle.SemanticAssignment.getProperty, Veir.Puddle.SemanticAssignment.bindProperty,
    Veir.Puddle.SemanticAssignment.bindType, Veir.Puddle.SemanticAssignment.bindValue,
    Veir.Puddle.SemanticAssignment.bind, Veir.Puddle.SemanticAssignment.ForallValues,
    Veir.Puddle.SemanticAssignment.bindValues, Veir.Puddle.MetadataTuple.resolveSemantic,
    Veir.Puddle.MetadataTuple.Shape.resolveSemantic,
    Veir.Puddle.MetadataTuple.Atom.resolveSemantic, Veir.Puddle.MetadataTuple.bindSemantic,
    Veir.Puddle.MetadataTuple.Shape.bindSemantic, Veir.Puddle.MetadataTuple.Atom.bindSemantic,
    Veir.Puddle.SemanticAssignment.bind_of_ne_eq,
    IsTypeAttr.cast?_eq_some_iff, Veir.Puddle.IsMetadataTuple.shape_unit,
    Veir.Puddle.IsMetadataTuple.shape_type, Veir.Puddle.IsMetadataTuple.shape_property,
    Veir.Puddle.IsMetadataTuple.shape_type_cons, Veir.Puddle.IsMetadataTuple.shape_property_cons,
    List.filter_cons_of_pos, List.filter_cons_of_neg, List.filter_nil, Function.comp_apply,
    List.reverse_nil, List.nil_append, List.cons_append, List.append_nil, Array.toList_map,
    Array.toList_range, List.range_zero, List.map_cons, List.map_nil, List.length_cons,
    List.length_nil, Array.size_map, Array.size_range, List.mapM_cons, List.mapM_nil,
    Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_fun_some, Nat.add_zero,
    Nat.zero_ne_one, Option.map_some, Option.map_eq_some_iff, Option.getD_eq_iff, Bool.not_true,
    Bool.not_false, Bool.not_eq_true, Bool.not_eq_true', Bool.false_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, and_false, or_false, not_false_eq_true, ne_eq, forall_const,
    true_implies,
    and_true, and_imp, not_imp, Classical.not_forall, not_exists, not_and, exists_and_left,
    exists_false, false_or, exists_eq_left, exists_eq_right, forall_exists_index,
    forall_apply_eq_imp_iff, forall_eq_apply_imp_iff, true_and,
    Veir.RuntimeValue.arrayIsRefinedBy_cons, Veir.RuntimeValue.arrayIsRefinedBy_refl,
    Veir.Puddle.Handle.mk.injEq] with self >> puddle_head
  maxSteps := 1000000

-- Restore `pure` notation after head reduction, which unfolds it to `CTree.ret`.
-- Keeping this separate avoids cycling between the two forms.
register_sym_simp puddleProgramResult where
  post := ground >> rewrite [Option.isSome_some, implies_true, forall_const,
    CTree.CTree.ret_pure, true_and] with self

/- Expose the outer validity predicates before entering symbolic normalization. -/
macro "unfoldPuddleSemanticsForSym" : tactic =>
  `(tactic| dsimp only [Pattern.PreservesSemantics, MatchProg.Models, MatchProg.bindingDecls])

open Lean Elab Tactic in
/-- Enforce the proof interface on expressions, including implicit type arguments.
Assignments are an elaboration detail and must not reach the user's proof body. -/
elab "puddleNoAssignments" : tactic => do
  for goal in ← getGoals do
    goal.withContext do
      let check (e : Expr) : MetaM Unit := do
        let e ← instantiateMVars e
        if (e.find? fun
          | .const name _ =>
            (``SemanticAssignment).isPrefixOf name || (``SemanticBinding).isPrefixOf name
          | _ => false).isSome then
          throwError "Puddle normalization left a semantic assignment in the proof state"
      check (← goal.getType)
      for decl in ← getLCtx do
        unless decl.isImplementationDetail do
          check decl.type
          if let some value := decl.value? then check value

open Lean Elab Tactic in
/-- Run symbolic program normalization without requiring the semantic proof to close. -/
elab "normalizePuddleProgram" : tactic => withMainContext do
  let params ← Meta.Grind.mkDefaultParams {}
  let (_, state) ← Grind.GrindTacticM.runAtGoal (← getMainGoal) params («sym» := true) do
    for variant in [`puddleProgram, `puddleProgramResult] do
      unless (← Grind.getGoals).isEmpty do
        let (methods, config) ← Grind.elabSimpVariant variant #[]
        let goal ← Grind.getMainGoal
        let result ← Grind.liftGrindM <|
          Meta.Sym.simpGoalIgnoringNoProgress goal.mvarId methods config
        match result with
        | .closed => Grind.replaceMainGoal []
        | .goal mvarId => Grind.replaceMainGoal [{ goal with mvarId }]
        | .noProgress => pure ()
  replaceMainGoal (state.goals.map (·.mvarId))

/-- Normalize handle bookkeeping while leaving operation CTrees opaque. -/
macro "simpPuddleProgramSym" "=>" body:tacticSeq : tactic =>
  `(tactic| (
    unfoldPuddleSemanticsForSym
    normalizePuddleProgram
    puddleNoAssignments
    ($body:tacticSeq)))

open Lean Elab Tactic in
/-- Normalize CTree validity, leaving only assignment-free semantic obligations. -/
elab "simpPuddleValid" : tactic => withMainContext do
  unless (← getMainTarget).isAppOf ``Pattern.Valid do
    throwError "expected a CTree pattern validity goal"
  evalTactic (← `(tactic| (
    unfoldPuddleBuilder
    constructor
    · simp [Pattern.Supported, get_effects, is_terminator]
    · cbv
    · open scoped Veir.Puddle.PuddleCbv in cbv
    unfoldPuddleSemanticsForSym
    normalizePuddleProgram
    puddleNoAssignments)))

/-- Discharge structural obligations and erase assignments before the proof body. -/
macro "simpPuddleValid" "program" "sym" "=>" body:tacticSeq : tactic =>
  `(tactic| (simpPuddleValid; ($body:tacticSeq)))

end

end Veir.Puddle.CTree
