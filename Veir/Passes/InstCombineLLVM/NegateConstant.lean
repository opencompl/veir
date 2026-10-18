module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.NegateConstant

open Veir
open Veir.Data
open Veir.Puddle
open Veir.Passes.InstCombineLLVM

@[local cbv_eval]
theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t

private def isIntegralConstant
    (props : propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  match (asLLVMConstantProperties props).value with
  | .integer _ => true
  | _ => false

private def isZeroConstant
    (props : propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  match (asLLVMConstantProperties props).value with
  | .integer attr => attr.value = 0
  | _ => false

private def matchZeroConstant (ty : Handle OpCode .type) :
    MatchProg.Builder (Handle OpCode .value) := do
  let constant ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty] isZeroConstant
  return constant.res[0]!

private def negateConstantProperty
    (input : TypeAttr × propertiesOf (OpCode.llvm .mlir__constant)) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let (type, props) := input
  let some intType := type.cast? IntegerType | none
  let .integer attr := (asLLVMConstantProperties props).value | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt (-attr.value) intType))

/- `properties_of` must participate in the same simplification pass as the semantic plumbing:
   this pattern exports an opcode-indexed property handle to its creator. -/
macro "simpNegateConstantSemantics" : tactic =>
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

/-- Scalar specialization of InstCombineNegator.cpp:126-129:
    `-(C) -> -C` for an integral constant `C`. -/
public def negateConstant : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let constant ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
        isIntegralConstant
      let zero ← matchZeroConstant ty
      let _ ← MatchProg.root (.llvm .sub) #[zero, constant.res[0]!] #[ty]
        (fun _ => true)
      return (ty, constant.properties))
    (fun (ty, constantProps) => do
      let negatedProps ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
        (ty, constantProps) negateConstantProperty
      CreateProg.operation (.llvm .mlir__constant) #[] #[ty] negatedProps)
    (fun result => result.res[0]!)

set_option linter.tacticCheckInstances false in
public theorem negateConstant_valid : Pattern.Valid negateConstant := by
  simp only [negateConstant, matchZeroConstant]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.insertFreshBindings,
        CreateDecl.checkBindings, Replacement.checkBindings]
  simpNegateConstantSemantics
  rintro ⟨w, signedness⟩ constantProps constant hConstant hinterpConstant
  generalize hTyped : asLLVMConstantProperties constantProps = typedProps
  cases typedProps with
  | mk constantValue =>
    cases constantValue with
    | float _ | dense _ | string _ =>
      simp [isIntegralConstant, hTyped] at hConstant
    | integer constantAttr =>
      have hinterpTyped :
          InterpretsTo (.llvm .mlir__constant) (asLLVMConstantProperties constantProps)
            #[IntegerType.mk w signedness] #[] #[constant] := by
        exact hinterpConstant
      rw [hTyped] at hinterpTyped
      obtain rfl := (constant_iff _ constantAttr _).mp hinterpTyped
      rintro zeroProps zero hZero hinterpZero
      change LLVMConstantProperties at zeroProps
      cases zeroProps with
      | mk zeroValue =>
        cases zeroValue with
        | float _ | dense _ | string _ =>
          simp [isZeroConstant, asLLVMConstantProperties] at hZero
        | integer zeroAttr =>
          simp only [isZeroConstant, asLLVMConstantProperties] at hZero
          have hZeroValue : zeroAttr.value = 0 := of_decide_eq_true hZero
          obtain rfl := (constant_iff _ zeroAttr _).mp hinterpZero
          rintro negProps source hinterpSource
          obtain rfl := (sub_iff _ _ _ _ _).mp hinterpSource
          rw [hZeroValue]
          simp [negateConstantProperty, hTyped, IsTypeAttr.cast?_of]
          refine ⟨.int w (.val (BitVec.ofInt w (-constantAttr.value))), ?_, ?_⟩
          · apply (constant_iff _ _ _).mpr
            simpa [IntegerAttr.ofInt] using congrArg
              (fun z => RuntimeValue.int w (.val z))
              (ofInt_normalizeValue { bitwidth := w, signedness := signedness }
                (-constantAttr.value)).symm
          change ∃ h : w = w,
            (LLVM.Int.sub (.val (BitVec.ofInt w 0))
              (.val (BitVec.ofInt w constantAttr.value)) negProps.nsw negProps.nuw).cast h ⊒
              .val (BitVec.ofInt w (-constantAttr.value))
          refine ⟨rfl, ?_⟩
          simpa only [LLVM.Int.cast_self] using
            (isRefinedBy_trans (sub_flags_refine w (.val (BitVec.ofInt w 0))
              (.val (BitVec.ofInt w constantAttr.value)) negProps.nsw negProps.nuw)
              (by rw [neg_constant]; exact isRefinedBy_refl _))

end Veir.Passes.InstCombineLLVM.NegateConstant
