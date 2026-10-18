module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.ProofTactics

open Veir Veir.Puddle

/-- Construct a scalar integer constant property at the matched type. -/
public def integerConstantProperty (value : Int) (type : TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt value intType))

@[cbv_eval] public theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

/-- Discharges the support and handle-well-formedness obligations shared by
    straight-line scalar integer Puddle patterns. -/
@[expose] macro "proveScalarPuddleStructure" : tactic =>
  `(tactic| (
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;>
        simp [properties_of, guard_eq_cond_punit, MatchProg.collectBindings,
          MatchProg.collectDeclBindings, MatchProg.rootResults?, HandleContext.forbid,
          HandleContext.forbidMany, HandleContext.lookup, HandleContext.lookupBindings,
          HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
          HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
          MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
          CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]))

/-- Exposes the semantic values of arbitrary scalar integer inputs after the
    generic Puddle model simplifier has reduced a straight-line pattern. -/
@[expose] macro "simpScalarPuddleSemantics" : tactic =>
  `(tactic| (
    simpPuddleSemantics
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index,
      forall_eq_apply_imp_iff]))

/-- Semantic normalization for scalar patterns that export opcode-indexed
    property handles from the matcher to an `applyNative` creator. -/
@[expose] macro "simpScalarPropertyPuddleSemantics" : tactic =>
  `(tactic| (
    simp only [properties_of, Pattern.PreservesSemantics, MatchProg.Models,
      MatchProg.bindingDecls, List.partition_eq_filter_filter, List.range_succ,
      List.reverse_cons, MatchProg.modelsDecls, MatchDecl.Models,
      CreateProg.Models, CreateProg.modelsDecls, CreateDecl.Models,
      SemanticAssignment.getValues, SemanticAssignment.getTypes,
      SemanticAssignment.getValue, SemanticAssignment.getType,
      SemanticAssignment.getProperty, SemanticAssignment.bindProperty,
      SemanticAssignment.bindType, SemanticAssignment.bindValue, SemanticAssignment.bind,
      SemanticAssignment.ForallValues, SemanticAssignment.ExistsValues,
      MetadataTuple.resolveSemantic, MetadataTuple.Shape.resolveSemantic,
      MetadataTuple.Atom.resolveSemantic, MetadataTuple.bindSemantic,
      MetadataTuple.Shape.bindSemantic, MetadataTuple.Atom.bindSemantic,
      Replacement.RefinesRoot, MatchProg.rootResults?, SemanticAssignment.bind_of_ne_eq,
      IsTypeAttr.cast?_eq_some_iff,
      IsMetadataTuple.shape_unit, IsMetadataTuple.shape_type, IsMetadataTuple.shape_property,
      IsMetadataTuple.shape_type_cons, IsMetadataTuple.shape_property_cons,
      List.filter_cons_of_pos, List.filter_cons_of_neg, List.filter_nil, Function.comp_apply,
      List.reverse_nil, List.nil_append, List.cons_append, List.append_nil,
      Array.toList_map, Array.toList_range, List.range_zero, List.map_cons, List.map_nil,
      List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      Option.bind_fun_some, Nat.add_zero, Nat.reduceAdd, Nat.zero_ne_one, Nat.reduceEqDiff,
      Option.map_eq_some_iff, Option.getD_eq_iff,
      Bool.not_true, Bool.not_false, Bool.not_eq_true, Bool.not_eq_true', Bool.false_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_false, or_false,
      not_false_eq_true, ne_eq, reduceCtorEq, ↓reduceIte, ↓reduceDIte, forall_const,
      and_true, and_imp, not_imp, Classical.not_forall, not_exists, not_and,
      exists_and_left, forall_exists_index, forall_apply_eq_imp_iff,
      RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.arrayIsRefinedBy_refl]
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index,
      forall_eq_apply_imp_iff]))

end Veir.Passes.InstCombineLLVM.ProofTactics
