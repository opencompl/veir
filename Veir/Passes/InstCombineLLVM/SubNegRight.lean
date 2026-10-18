module
public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
namespace Veir.Passes.InstCombineLLVM.SubNegRight
open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by cases ‹Decidable p› <;> rfl

private def isIntegralConstant
    (props : propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  match (asLLVMConstantProperties props).value with
  | .integer _ => true
  | _ => false

private def isNonMinConstant
    (input : TypeAttr × propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  let (type, props) := input
  match type.cast? IntegerType, (asLLVMConstantProperties props).value with
  | some intType, .integer attr =>
      decide (BitVec.ofInt intType.bitwidth attr.value ≠ BitVec.intMin intType.bitwidth)
  | _, _ => false

private def negateSubConstantProperty
    (input : TypeAttr × propertiesOf (OpCode.llvm .mlir__constant)) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let (type, props) := input
  let some intType := type.cast? IntegerType | none
  let .integer attr := (asLLVMConstantProperties props).value | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt (-attr.value) intType))

macro "simpSubNegConstantSemantics" : tactic =>
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

/-- Scalar specialization of InstCombineAddSub.cpp:2443-2459: `X-(-A) -> X+A`.
    This conservative form clears result flags. -/
public def subNegRight : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let a ← MatchProg.value ty
    let zero ← matchIntConstant ty 0
    let negA ← MatchProg.operation (.llvm .sub) #[zero, a] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .sub) #[x, negA.res[0]!] #[ty] (fun _ => true)
    return (ty, x, a))
  (fun (ty, x, a) => do
    let props ← CreateProg.property (.llvm .add) default
    CreateProg.operation (.llvm .add) #[x, a] #[ty] props)
  (fun result => result.res[0]!)

public theorem subNegRight_valid : Pattern.Valid subNegRight := by
  simp only [subNegRight, matchIntConstant]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
      HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
      HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, s⟩ x a
  rintro ⟨cv⟩ zero hz hiz
  cases cv with
  | float _ | dense _ | string _ => simp at hz
  | integer za =>
    have hzv : za.value = 0 := of_decide_eq_true hz
    obtain rfl := (constant_iff _ za _).mp hiz
    rintro negProps negA hNegA
    obtain rfl := (sub_iff _ _ _ _ _).mp hNegA
    rintro subProps source hSource
    obtain rfl := (sub_iff _ _ _ _ _).mp hSource
    rw [hzv]
    refine ⟨.int w (LLVM.Int.add x a), (add_iff _ _ _ _ _).mpr rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    simpa only [LLVM.Int.cast_self] using
      (sub_neg_right_refines w x a negProps.nsw negProps.nuw subProps.nsw subProps.nuw)

/-- NSW-preserving explicit-negation form emitted when both source subtractions are NSW. -/
public def subNegRightNSW : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let a ← MatchProg.value ty
    let zero ← matchIntConstant ty 0
    let negA ← MatchProg.operation (.llvm .sub) #[zero, a] #[ty] (fun p => p.nsw)
    let _ ← MatchProg.root (.llvm .sub) #[x, negA.res[0]!] #[ty] (fun p => p.nsw)
    return (ty, x, a))
  (fun (ty, x, a) => do
    let props ← CreateProg.property (.llvm .add) { nsw := true, nuw := false }
    CreateProg.operation (.llvm .add) #[x, a] #[ty] props)
  (fun result => result.res[0]!)

public theorem subNegRightNSW_valid : Pattern.Valid subNegRightNSW := by
  simp only [subNegRightNSW, matchIntConstant]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
      HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
      HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩ x a
  rintro ⟨constantValue⟩ zero hZero hInterpZero
  cases constantValue with
  | float _ | dense _ | string _ => simp at hZero
  | integer zeroAttr =>
    have hZeroValue : zeroAttr.value = 0 := of_decide_eq_true hZero
    obtain rfl := (constant_iff _ zeroAttr _).mp hInterpZero
    rintro negProps negA hNegNSW hNegA
    obtain rfl := (sub_iff _ _ _ _ _).mp hNegA
    rintro subProps source hSubNSW hSource
    obtain rfl := (sub_iff _ _ _ _ _).mp hSource
    rw [hZeroValue, hNegNSW, hSubNSW]
    refine ⟨.int w (LLVM.Int.add x a true false), (add_iff _ _ _ _ _).mpr rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    simpa only [LLVM.Int.cast_self] using
      (sub_neg_right_nsw_refines w x a negProps.nuw subProps.nuw)

/-- Scalar constant arm of `dyn_castNegVal`: `x - C -> x + (-C)`, clearing flags. -/
public def subNegConstant : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let constant ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty] isIntegralConstant
    let _ ← MatchProg.root (.llvm .sub) #[x, constant.res[0]!] #[ty] (fun _ => true)
    return (ty, x, constant.properties))
  (fun (ty, x, constantProps) => do
    let negatedProps ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      (ty, constantProps) negateSubConstantProperty
    let negated ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] negatedProps
    let props ← CreateProg.property (.llvm .add) default
    CreateProg.operation (.llvm .add) #[x, negated.res[0]!] #[ty] props)
  (fun result => result.res[0]!)

set_option linter.tacticCheckInstances false in
public theorem subNegConstant_valid : Pattern.Valid subNegConstant := by
  simp only [subNegConstant]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
      HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
      HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
      Replacement.checkBindings]
  simpSubNegConstantSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index,
    forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩ x
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
      rintro subProps source hSource
      obtain rfl := (sub_iff _ _ _ _ _).mp hSource
      simp [negateSubConstantProperty, hTyped, IsTypeAttr.cast?_of]
      refine ⟨.int w (.val (BitVec.ofInt w (-constantAttr.value))), ?_, ?_⟩
      · apply (constant_iff _ _ _).mpr
        simpa [IntegerAttr.ofInt] using congrArg
          (fun z => RuntimeValue.int w (.val z))
          (ofInt_normalizeValue { bitwidth := w, signedness := signedness }
            (-constantAttr.value)).symm
      refine ⟨.int w (LLVM.Int.add x (.val (BitVec.ofInt w (-constantAttr.value)))),
        (add_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, BitVec.ofInt_neg] using
        (sub_neg_constant_refines w x (BitVec.ofInt w constantAttr.value)
          subProps.nsw subProps.nuw)

/-- NSW-preserving constant arm, valid when `C` is not the signed minimum. -/
public def subNegConstantNSW : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let constant ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty] isIntegralConstant
    MatchProg.matchNative (ty, constant.properties) isNonMinConstant
    let _ ← MatchProg.root (.llvm .sub) #[x, constant.res[0]!] #[ty] (fun p => p.nsw)
    return (ty, x, constant.properties))
  (fun (ty, x, constantProps) => do
    let negatedProps ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      (ty, constantProps) negateSubConstantProperty
    let negated ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] negatedProps
    let props ← CreateProg.property (.llvm .add) { nsw := true, nuw := false }
    CreateProg.operation (.llvm .add) #[x, negated.res[0]!] #[ty] props)
  (fun result => result.res[0]!)

set_option linter.tacticCheckInstances false in
public theorem subNegConstantNSW_valid : Pattern.Valid subNegConstantNSW := by
  simp only [subNegConstantNSW]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, MatchProg.collectBindings,
      MatchProg.collectDeclBindings, MatchProg.rootResults?, HandleContext.forbid,
      HandleContext.forbidMany, HandleContext.lookup, HandleContext.lookupBindings,
      HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
      HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
      MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
      CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpSubNegConstantSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index,
    forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩ x
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
      rintro subProps source hSubNSW hSource hNonMin
      obtain rfl := (sub_iff _ _ _ _ _).mp hSource
      have hConstantValue :
          constantProps.value = LLVMConstantValue.integer constantAttr := by
        simpa [asLLVMConstantProperties] using
          congrArg (fun p : LLVMConstantProperties => p.value) hTyped
      have hNotMin : BitVec.ofInt w constantAttr.value ≠ BitVec.intMin w := by
        simpa [isNonMinConstant, hConstantValue, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hNonMin
      rw [hSubNSW]
      simp [negateSubConstantProperty, hTyped, IsTypeAttr.cast?_of]
      refine ⟨.int w (.val (BitVec.ofInt w (-constantAttr.value))), ?_, ?_⟩
      · apply (constant_iff _ _ _).mpr
        simpa [IntegerAttr.ofInt] using congrArg
          (fun z => RuntimeValue.int w (.val z))
          (ofInt_normalizeValue { bitwidth := w, signedness := signedness }
            (-constantAttr.value)).symm
      refine ⟨.int w (LLVM.Int.add x (.val (BitVec.ofInt w (-constantAttr.value))) true false),
        (add_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, BitVec.ofInt_neg] using
        (sub_neg_constant_nsw_refines w x (BitVec.ofInt w constantAttr.value)
          hNotMin subProps.nuw)
end Veir.Passes.InstCombineLLVM.SubNegRight
