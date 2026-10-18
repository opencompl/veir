module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.MulNegConstant

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def isIntegralConstant
    (props : propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  match (asLLVMConstantProperties props).value with
  | .integer _ => true
  | _ => false

private def negateMulConstantProperty
    (input : TypeAttr × propertiesOf (OpCode.llvm .mlir__constant)) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let (type, props) := input
  let some intType := type.cast? IntegerType | none
  let .integer attr := (asLLVMConstantProperties props).value | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt (-attr.value) intType))

macro "simpMulNegConstantSemantics" : tactic =>
  `(tactic| simp only [properties_of, Pattern.PreservesSemantics, MatchProg.Models,
    MatchProg.bindingDecls, List.partition_eq_filter_filter, List.range_succ, List.reverse_cons,
    MatchProg.modelsDecls, MatchDecl.Models,
    CreateProg.Models, CreateProg.modelsDecls, CreateDecl.Models,
    SemanticAssignment.getValues, SemanticAssignment.getTypes,
    SemanticAssignment.getValue, SemanticAssignment.getType,
    SemanticAssignment.getProperty,
    SemanticAssignment.bindProperty, SemanticAssignment.bindType,
    SemanticAssignment.bindValue, SemanticAssignment.bind,
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
    and_true, and_imp, not_imp, Classical.not_forall, not_exists, not_and, exists_and_left,
    forall_exists_index, forall_apply_eq_imp_iff,
    RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.arrayIsRefinedBy_refl])

/- Scalar specialization of InstCombineMulDivRem.cpp:420-424. -/
public def mulNegConstant : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let zero ← matchIntConstant ty 0
      let negX ← MatchProg.operation (.llvm .sub) #[zero, x] #[ty] (fun _ => true)
      let constant ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
        isIntegralConstant
      let _ ← MatchProg.root (.llvm .mul) #[negX.res[0]!, constant.res[0]!]
        #[ty] (fun _ => true)
      return (ty, x, constant.properties))
    (fun (ty, x, constantProps) => do
      let negatedProps ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
        (ty, constantProps) negateMulConstantProperty
      let negated ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] negatedProps
      let mp ← CreateProg.property (.llvm .mul) default
      CreateProg.operation (.llvm .mul) #[x, negated.res[0]!] #[ty] mp)
    (fun result => result.res[0]!)

set_option linter.tacticCheckInstances false in
public theorem mulNegConstant_valid : Pattern.Valid mulNegConstant := by
  simp only [mulNegConstant, matchIntConstant]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
      HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
      HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
      Replacement.checkBindings]
  simpMulNegConstantSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index,
    forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩ x
  rintro ⟨zeroValue⟩ zero hZero hInterpZero
  cases zeroValue with
  | float _ | dense _ | string _ => simp at hZero
  | integer zeroAttr =>
    have hZeroValue : zeroAttr.value = 0 := of_decide_eq_true hZero
    obtain rfl := (constant_iff _ zeroAttr _).mp hInterpZero
    rintro negProps negX hNegX
    obtain rfl := (sub_iff _ _ _ _ _).mp hNegX
    rintro constantProps constant hConstant hInterpConstant
    generalize hTyped : asLLVMConstantProperties constantProps = typedProps
    cases typedProps with
    | mk constantValue =>
      cases constantValue with
      | float _ | dense _ | string _ =>
        simp [isIntegralConstant, hTyped] at hConstant
      | integer constantAttr =>
        have hInterpTyped :
            InterpretsTo (.llvm .mlir__constant) (asLLVMConstantProperties constantProps)
              #[IntegerType.mk w signedness] #[] #[constant] := hInterpConstant
        rw [hTyped] at hInterpTyped
        obtain rfl := (constant_iff _ constantAttr _).mp hInterpTyped
        rintro mulProps source hSource
        obtain rfl := (mul_iff _ _ _ _ _).mp hSource
        rw [hZeroValue]
        simp [negateMulConstantProperty, hTyped, IsTypeAttr.cast?_of]
        refine ⟨.int w (.val (BitVec.ofInt w (-constantAttr.value))), ?_, ?_⟩
        · apply (constant_iff _ _ _).mpr
          simpa [IntegerAttr.ofInt] using congrArg
            (fun z => RuntimeValue.int w (.val z))
            (ofInt_normalizeValue { bitwidth := w, signedness := signedness }
              (-constantAttr.value)).symm
        refine ⟨.int w (LLVM.Int.mul x (.val (BitVec.ofInt w (-constantAttr.value)))),
          (mul_iff _ _ _ _ _).mpr rfl, ?_⟩
        refine ⟨rfl, ?_⟩
        simpa only [LLVM.Int.cast_self, BitVec.ofInt_neg,
            show BitVec.ofInt w 0 = 0#w by rfl] using
          (mul_neg_constant_flags_refine w x (BitVec.ofInt w constantAttr.value)
            negProps.nsw negProps.nuw mulProps.nsw mulProps.nuw)

end Veir.Passes.InstCombineLLVM.MulNegConstant
