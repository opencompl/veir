module

public meta import Lean
meta import all Lean.Elab.Tactic.Grind.Sym
public import Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.PatternRewriter.Puddle.CTreeProgramValidity

namespace Veir.Puddle.CTree

public section

/- Reduce beta redexes, projections, and matches introduced by symbolic rewrites.
Unfold function-valued assignment updates explicitly so lookups with extra
arguments reduce too. Preserve comparison heads for the equality rewrite rules. -/
open Lean Meta Elab Tactic Grind in
meta def reducePuddleHead : Sym.Simp.Simproc := fun e => do
  let e' ← withTransparency .instances <| whnfHeadPred e fun e => do
    let head := e.getAppFn
    if #[`Bind.bind, `Pure.pure, `Option.bind, `Veir.Puddle.IsMetadataTuple.shape,
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

/- Unfold support checks and opcode-interface projections at the head. This
reduces the actual effect/terminator implementations without enumerating dialects.
Keep list membership opaque so the symbolic list rules match syntactically. -/
open Lean Meta Elab Tactic Grind in
meta def reducePuddleSupportedHead : Sym.Simp.Simproc := fun e => do
  if !(#[`Veir.Puddle.MatchDecl.Supported, `Veir.Puddle.CreateDecl.Supported,
      `Veir.HasOpInfo.getEffects, `Veir.HasOpInfo.isTerminator,
      `Veir.MemoryEffects.none].any e.getAppFn.isConstOf) then
    return ← reducePuddleHead e
  let e' ← withTransparency .all <| whnf e
  let e' ← Sym.foldProjs e'
  let e' ← Sym.shareCommon e'
  if e' == e then return .rfl
  return .step e' (← mkEqRefl e')

syntax (name := reducePuddleSupportedHeadSyntax) "puddle_supported_head" : sym_simproc

@[sym_simproc reducePuddleSupportedHeadSyntax]
meta def elabReducePuddleSupportedHead : Lean.Elab.Tactic.Grind.SymSimprocElab := fun _ =>
  pure reducePuddleSupportedHead

register_sym_simp puddleSupported where
  pre := control
  post := ground >> rewrite [
    Veir.Puddle.Pattern.Supported, Veir.Puddle.CreateProg.Supported,
    Veir.Puddle.MatchProg.Supported, Veir.Puddle.MatchDecl.Supported,
    Veir.Puddle.CreateDecl.Supported, Veir.Puddle.SupportedOpCode,
    List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    true_and, and_true] with self >> puddle_supported_head

/-- Prove opcode support with symbolic simplification. -/
macro "provePuddleSupported" "sym" : tactic => do
  let variant := Lean.mkIdent `puddleSupported
  `(tactic| sym => simp $variant:ident)

/- Builder projections and metadata allocation need delta reduction even when callbacks
contain free variables. Keep this stronger reduction local to builder normalization. -/
open Lean Meta Elab Tactic Grind in
meta def reducePuddleBuilderHead : Sym.Simp.Simproc := fun e => do
  if !(#[`Veir.Puddle.Pattern.Builder, `Veir.Puddle.MatchProg.build,
      `Veir.Puddle.CreateProg.build, `Veir.Puddle.Pattern.matcher,
      `Veir.Puddle.Pattern.creation, `Veir.Puddle.Pattern.replacement,
      `Veir.Puddle.MatchProg.numHandles, `Veir.Puddle.MatchProg.exports,
      `Veir.Puddle.CreateProg.numHandles, `Veir.Puddle.CreateProg.exports,
      `Veir.Puddle.MatchProg.Builder.run, `Veir.Puddle.CreateProg.Builder.run,
      `Veir.Puddle.MatchProg.BuilderState.nextId, `Veir.Puddle.MatchProg.BuilderState.decls,
      `Veir.Puddle.MatchProg.BuilderState.guardDecls, `Veir.Puddle.MatchProg.BuilderState.root?,
      `Veir.Puddle.MatchProg.BuilderState.numRoots,
      `Veir.Puddle.CreateProg.BuilderState.nextId, `Veir.Puddle.CreateProg.BuilderState.decls,
      `Veir.Puddle.MetadataTuple.fresh, `Veir.Puddle.MetadataTuple.Shape.fresh,
      `Veir.Puddle.MetadataTuple.Atom.fresh].any e.getAppFn.isConstOf) then
    return ← reducePuddleHead e
  let e' ← withTransparency .default <| whnf e
  let e' ← Sym.foldProjs e'
  let e' ← Sym.shareCommon e'
  if e' == e then return .rfl
  return .step e' (← mkEqRefl e')

syntax (name := reducePuddleBuilderHeadSyntax) "puddle_builder_head" : sym_simproc

@[sym_simproc reducePuddleBuilderHeadSyntax]
meta def elabReducePuddleBuilderHead : Lean.Elab.Tactic.Grind.SymSimprocElab := fun _ =>
  pure reducePuddleBuilderHead

/- Normalize builder state symbolically, sharing repeated matcher and creation exports. -/
register_sym_simp puddleBuilder where
  pre := control >> puddle_builder_head
  post := ground >> rewrite [
    Veir.Puddle.Pattern.Builder, Veir.Puddle.MatchProg.build, Veir.Puddle.CreateProg.build,
    Veir.Puddle.MatchProg.value, Veir.Puddle.MatchProg.type, Veir.Puddle.MatchProg.root,
    Veir.Puddle.MatchProg.operation, Veir.Puddle.MatchProg.matchNative,
    Veir.Puddle.MatchProg.inspectOperation,
    Veir.Puddle.CreateProg.type, Veir.Puddle.CreateProg.operation,
    Veir.Puddle.CreateProg.property, Veir.Puddle.CreateProg.applyNative,
    Veir.Puddle.MetadataTuple.fresh,
    Veir.Puddle.IsMetadataTuple.shape_unit, Veir.Puddle.IsMetadataTuple.shape_type,
    Veir.Puddle.IsMetadataTuple.shape_property, Veir.Puddle.IsMetadataTuple.shape_type_cons,
    Veir.Puddle.IsMetadataTuple.shape_property_cons,
    Veir.Puddle.MetadataTuple.Shape.fresh, Veir.Puddle.MetadataTuple.Atom.fresh,
    Nat.zero_add, List.size_toArray, List.length_cons, List.length_nil,
    Array.size_map, Array.size_range, Nat.lt_add_one, getElem!_pos,
    Array.getElem_map, Array.getElem_range, Nat.add_zero, List.cons_append,
    List.nil_append, List.reverse_cons, List.reverse_nil] with self >> puddle_builder_head
  maxSteps := 1000000

open Lean Elab Tactic in
/-- Expand builders with symbolic simplification for the symbolic program validity mode. -/
elab "unfoldPuddleBuilderForSym" : tactic => withMainContext do
  let params ← Meta.Grind.mkDefaultParams {}
  let (_, state) ← Grind.GrindTacticM.runAtGoal (← getMainGoal) params («sym» := true) do
    unless (← Grind.getGoals).isEmpty do
      let (methods, config) ← Grind.elabSimpVariant `puddleBuilder #[]
      let goal ← Grind.getMainGoal
      let result ← Grind.liftGrindM <|
        Meta.Sym.simpGoalIgnoringNoProgress goal.mvarId methods config
      match result with
      | .closed => Grind.replaceMainGoal []
      | .goal mvarId => Grind.replaceMainGoal [{ goal with mvarId }]
      | .noProgress => pure ()
  replaceMainGoal (state.goals.map (·.mvarId))
  -- Numeric offsets can occur in dependent constructor fields skipped by symbolic congruence.
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic| try simp only [Nat.reduceAdd]))

/- Normalize assignments while retaining operation choices and safety checks.
Omit arrow_telescope: Lean 4.35.0-rc1 can produce an ill-typed proof for nested
outcome implications. Conditional rules use self as their discharger. -/
register_sym_simp puddleProgram where
  pre := control
  post := ground >> rewrite [
    List.partition_eq_filter_filter, List.range_succ, List.reverse_cons,
    Veir.Puddle.CTree.MatchProg.modelsDecls, Veir.Puddle.CTree.MatchDecl.Models,
    Veir.Puddle.CTree.CreateProg.interpretReplacement, Veir.Puddle.CTree.CreateProg.interpret,
    Veir.Puddle.CTree.CreateProg.interpretDecls, Veir.Puddle.CTree.CreationM.bind_assoc,
    Veir.Puddle.CTree.CreationM.pure_bind, Veir.Puddle.CTree.CreationM.bind_pure,
    Veir.Puddle.CTree.CreationM.invalid_bind, Veir.Puddle.CTree.CreateDecl.interpret,
    Veir.Interp.ok.injEq, Veir.Interp.ub.injEq, Veir.Interp.fail.injEq,
    Veir.Puddle.SemanticAssignment.getValues, Veir.Puddle.SemanticAssignment.getTypes,
    Veir.Puddle.SemanticAssignment.getValue, Veir.Puddle.SemanticAssignment.getType,
    Veir.Puddle.SemanticAssignment.getProperty, Veir.Puddle.SemanticAssignment.bindProperty,
    Veir.Puddle.SemanticAssignment.bindType, Veir.Puddle.SemanticAssignment.bindValue,
    Veir.Puddle.SemanticAssignment.bind, Veir.Puddle.SemanticAssignment.ForallValues,
    Veir.Puddle.CTree.SemanticAssignment.bindValues.go, Veir.Puddle.MetadataTuple.resolveSemantic,
    Veir.Puddle.MetadataTuple.Shape.resolveSemantic,
    Veir.Puddle.MetadataTuple.Atom.resolveSemantic, Veir.Puddle.MetadataTuple.bindSemantic,
    Veir.Puddle.MetadataTuple.Shape.bindSemantic, Veir.Puddle.MetadataTuple.Atom.bindSemantic,
    Veir.Puddle.CTree.MatchProg.RootCanInterpretTo, Veir.Puddle.SemanticAssignment.bind_of_ne_eq,
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
    Veir.Puddle.Handle.mk.injEq, Veir.Puddle.CTree.CreationM.checked_bind_check,
    Veir.TypeAttr.mk_registerType, Veir.TypeAttr.mk_integerType,
    Veir.TypeAttr.mk_byteType] with self >> puddle_head
  maxSteps := 1000000

/- Simplify a peeled outcome without expanding the remaining operation choices. -/
register_sym_simp puddleStep where
  pre := control
  post := ground >> rewrite [
    Veir.TypeAttr.mk_registerType, Veir.TypeAttr.mk_integerType, Veir.TypeAttr.mk_byteType,
    forall_exists_index, and_imp, forall_eq_apply_imp_iff, forall_eq,
    Veir.Puddle.CTree.CreationM.forall_result_eq,
    Veir.Interp.foldProp_ok, Veir.Interp.foldProp_ub, Veir.Interp.foldProp_fail,
    Veir.Puddle.CTree.CreationM.models_check_bind,
    Veir.Puddle.CTree.CreationM.models_check, Veir.Puddle.CTree.CreationM.models_pure,
    List.size_toArray, List.length_cons, List.length_nil,
    Array.size_map, Nat.lt_add_one, getElem!_pos,
    List.getElem_toArray, List.getElem_cons_zero,
    true_and, and_true] with self >> puddle_head
  maxSteps := 1000000

/- Native metadata callbacks carry dependent tuple types and comparison instances.
Unfold their deterministic plumbing before symbolic rule matching, which uses
syntactic matching rather than the ordinary simplifier's definitional equality.
The creation outcome relations remain opaque for the symbolic models_* rules. -/
open Lean Elab Tactic in
elab "unfoldPuddleSemanticsForSym" : tactic => withMainContext do
  let target ← getMainTarget
  if (target.find? fun e => e.isAppOf `Veir.Puddle.MatchDecl.applyNative ||
      e.isAppOf `Veir.Puddle.CreateDecl.applyNative ||
      e.isAppOf `Veir.Puddle.MatchDecl.inspectOperation).isSome then
    evalTactic (← `(tactic| simpPuddleCore []))
  else
    evalTactic (← `(tactic| unfold Pattern.PreservesSemantics MatchProg.Models MatchProg.bindingDecls))

/-- Normalize the creation program symbolically, preserving binds for explicit peeling. -/
macro "simpPuddleProgramSym" "=>" body:tacticSeq : tactic => do
  let variant := Lean.mkIdent `puddleProgram
  `(tactic| (
    unfoldPuddleSemanticsForSym
    sym =>
      -- Native metadata callbacks can leave the plumbing normalized already.
      try simp $variant:ident
      tactic => $body))

namespace StructureCbv

/- Lean 4.35.0-rc4's cbv simproc for `if True` omits the Decidable argument in
its proof. Evaluate Option guards through Bool.cond instead. These rules are
scoped so the workaround only applies to Puddle structural checking. -/
@[scoped cbv_eval]
theorem guard_eq_cond {condition : Prop} [Decidable condition] :
    (guard condition : Option Unit) = cond (decide condition) (some ()) none := by
  cases ‹Decidable condition› <;> rfl

/- Evaluate arrays through their list representation even when Array.Basic's
implementation is hidden by module imports. -/
attribute [scoped cbv_eval ←] List.toArray_range
attribute [scoped cbv_eval] Array.mapM_eq_mapM_toList

end StructureCbv

/-- Prove structural obligations symbolically, then peel the folded creation program. -/
macro "provePuddleValid" "program" "sym" "=>" body:tacticSeq : tactic =>
  `(tactic| (
    unfoldPuddleBuilderForSym
    constructor
    · provePuddleSupported sym
    · cbv
    · open scoped StructureCbv in cbv
    simpPuddleProgramSym => $body))

open Lean Elab Tactic in
/-- Consume one operation choice, keeping later choices folded.
Unlike `sym =>`, this returns the simplified goal to the surrounding tactic script.
Universally quantified choices from earlier operations are preserved, so subsequent
steps can run without introducing those choices into the local context. -/
elab "puddleStep" "sym" "[" rules:ident,* "]" : tactic => withMainContext do
  let mut goal ← getMainGoal
  let mut choices := #[]
  while (← goal.getType).isForall do
    let (choice, next) ← goal.intro1P
    choices := choices.push choice
    goal := next
  replaceMainGoal [goal]
  evalTactic (← `(tactic| try simp only [CreationM.models_check_bind,
    CreationM.models_check, CreationM.models_pure, true_and, and_true]))
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| rw [CreationM.models_bind, CreationM.models_choose]))
  if (← getGoals).isEmpty then return
  let params ← Meta.Grind.mkDefaultParams {}
  let (_, state) ← Grind.GrindTacticM.runAtGoal (← getMainGoal) params («sym» := true) do
    unless (← Grind.getGoals).isEmpty do
      let (_, thms) ← Grind.resolveExtraTheorems (some rules.getElems)
      let (methods, config) ← Grind.elabSimpVariant `puddleStep thms
      let goal ← Grind.getMainGoal
      let result ← Grind.liftGrindM <|
        Meta.Sym.simpGoalIgnoringNoProgress goal.mvarId methods config
      match result with
      | .closed => Grind.replaceMainGoal []
      | .goal mvarId => Grind.replaceMainGoal [{ goal with mvarId }]
      | .noProgress => pure ()
  let goals ← state.goals.mapM fun goal => do
    let (_, goal) ← goal.mvarId.revert choices (preserveOrder := true)
    return goal
  replaceMainGoal goals

open Lean Elab Tactic in
/-- Peel the supported operation choices one at a time, preserving universal choices
and keeping the remaining creation program folded between steps. -/
elab "puddleSteps" "sym" "[" rules:ident,* "]" : tactic => do
  -- Report misspelled or unavailable rules instead of swallowing them in `repeat`.
  for rule in rules.getElems do
    discard <| resolveGlobalConstNoOverload rule
  evalTactic (← `(tactic| repeat (puddleStep sym [$rules,*])))
  for goal in ← getGoals do
    goal.withContext do
      if ((← goal.getType).find? (·.isAppOf ``CreationM.Models)).isSome then
        throwError "puddleSteps left a folded creation program; supply its interpretation rule or split the remaining cases first"

end

end Veir.Puddle.CTree
