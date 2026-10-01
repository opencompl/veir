module

public meta import Lean
public import Veir.PatternRewriter.Puddle.CTreeValidity

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

/- Omit arrow_telescope: in Lean 4.35.0-rc1 it can produce an ill-typed proof
for the nested outcome implications. Conditional rules use self as discharger. -/
register_sym_simp puddleSemantics where
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
    Veir.Puddle.Handle.mk.injEq, Veir.Puddle.CTree.CreationM.models_bind,
    Veir.Puddle.CTree.CreationM.models_pure, Veir.Puddle.CTree.CreationM.models_checked,
    Veir.Puddle.CTree.CreationM.models_choose, Veir.Puddle.CTree.CreationM.models_invalid,
    Veir.Interp.foldProp_ok, Veir.Interp.foldProp_ub, Veir.Interp.foldProp_fail,
    Veir.Interp.foldProp_onError] with self >> puddle_head
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

/-- Expose CTree semantics using symbolic simp after unfolding the matcher wrapper.
Unfold bindingDecls outside sym to avoid its recursive-reducible-rule preprocessing crash.
The continuation runs ordinary tactics on the normalized proposition. -/
macro "simpPuddleSemanticsSym" "=>" body:tacticSeq : tactic => do
  let variant := Lean.mkIdent `puddleSemantics
  `(tactic| (
    unfoldPuddleSemanticsForSym
    sym =>
      simp $variant:ident
      tactic => $body))

/-- Opt in to symbolic assignment normalization for a validity proof. -/
macro "provePuddleValid" "sym" "=>" body:tacticSeq : tactic =>
  `(tactic| (
    try unfoldPuddleBuilder
    constructor
    · provePuddleSupported sym
    · cbv
    · native_decide
    simpPuddleSemanticsSym => $body))

end

end Veir.Puddle.CTree
