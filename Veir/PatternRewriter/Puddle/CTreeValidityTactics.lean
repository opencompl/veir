module

public meta import Lean
public import Veir.PatternRewriter.Puddle.CTreeValidity

namespace Veir.Puddle.CTree

public section

open Lean Elab Tactic in
/--
Enforce no `SemanticAssignment` or `SemanticBinding` terms are in the proof state.
This is a debugging tactic to ensure that the Puddle normalization tactic is simplifying
what it should.
-/
elab "checkPuddleSimpTactic" : tactic => do
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
/-- Discharge the structural CTree validity obligations, leaving semantic preservation. -/
elab "simpPuddleValid" : tactic => withMainContext do
  unless (← getMainTarget).isAppOf ``Pattern.Valid do
    throwError "expected a CTree pattern validity goal"
  evalTactic (← `(tactic| (
    unfoldPuddleBuilder
    constructor
    · conv => arg 1; cbv
      /- Eliminate empty-list quantifiers before unfolding opcode metadata. -/
      simp only [Pattern.Supported, List.forall_mem_cons, List.not_mem_nil,
        false_implies, implies_true]
      simp [get_effects, is_terminator]
    · cbv
    · open scoped Veir.Puddle.PuddleCbv in cbv
    /- Normalize semantic plumbing while keeping operation denotations opaque. -/
    simp only [Pattern.PreservesSemantics, MatchProg.Models,
      Veir.Puddle.MatchProg.bindingDecls, List.partition_eq_filter_filter,
      MatchProg.ModelsDecls, MatchDecl.Models, MatchProg.rootSemantics,
      CreateProg.semantics, CreateProg.semanticsDecls, CreateDecl.semantics,
      SemanticAssignment.getValues, SemanticAssignment.getTypes,
      SemanticAssignment.getValueTypes, SemanticAssignment.getValueType,
      SemanticAssignment.getValue, SemanticAssignment.getType, SemanticAssignment.getProperty,
      SemanticAssignment.bindValues, SemanticAssignment.bindValue, SemanticAssignment.bindType,
      SemanticAssignment.bindProperty, SemanticAssignment.bind, SemanticAssignment.empty,
      SemanticAssignment.ForallValues, SemanticAssignment.ExistsValues,
      MetadataTuple.resolveSemantic, MetadataTuple.Shape.resolveSemantic,
      MetadataTuple.Atom.resolveSemantic, MetadataTuple.bindSemantic,
      MetadataTuple.Shape.bindSemantic, MetadataTuple.Atom.bindSemantic,
      IsMetadataTuple.shape_unit, IsMetadataTuple.shape_type, IsMetadataTuple.shape_property,
      IsMetadataTuple.shape_type_cons, IsMetadataTuple.shape_property_cons,
      List.filter_cons_of_pos, List.filter_cons_of_neg, List.filter_nil, Function.comp_apply,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.append_nil,
      Array.toList_map, Array.toList_range, List.range_succ, List.range_zero,
      List.map_cons, List.map_nil,
      /- Evaluate concrete builder loops before resolving their allocated handles. -/
      Array.mapM, ↓Array.mapM.map, bind, pure,
      List.size_toArray, List.length_cons, List.length_nil,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      Array.toList_push, Array.emptyWithCapacity, Array.size_map, Array.size_range,
      getElem!_pos, Array.getElem_map, Array.getElem_range,
      List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      Option.bind_fun_some, Nat.add_zero, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT,
      IsTypeAttr.cast?_eq_some_iff, Option.map_eq_some_iff, Option.getD_eq_iff,
      Bool.not_true, Bool.not_false, Bool.not_eq_true, Bool.not_eq_true', Bool.false_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_false, or_false,
      not_false_eq_true, not_true_eq_false, ne_eq, Handle.mk.injEq, reduceCtorEq,
      ↓reduceIte, ↓reduceDIte, forall_const,
      and_true, and_imp, not_imp, Classical.not_forall, not_exists, not_and, exists_and_left,
      forall_exists_index, forall_apply_eq_imp_iff]
    checkPuddleSimpTactic)))

end

end Veir.Puddle.CTree
