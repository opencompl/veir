module

public import Veir.Passes.InstCombineLLVM.CoreInversionSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
import all Veir.Data.LLVM.Int.Basic

namespace Veir.Passes.InstCombineLLVM.FreeInvertConstant

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def isIntegralConstant
    (props : propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  match (asLLVMConstantProperties props).value with
  | .integer _ => true
  | _ => false

private def complementConstantProperty
    (input : TypeAttr × propertiesOf (OpCode.llvm .mlir__constant)) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let (type, props) := input
  let some intType := type.cast? IntegerType | none
  let .integer attr := (asLLVMConstantProperties props).value | none
  return LLVMConstantProperties.mk
    (.integer (IntegerAttr.ofInt (-attr.value - 1) intType))

macro "simpConstantInversionSemantics" : tactic =>
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

private def invertIntegerConstantPattern (outerNotLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let constant ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
        isIntegralConstant
      let minusOne ← matchIntConstantNormalized ty (-1)
      let _ ← if outerNotLeft then
        MatchProg.root (.llvm .xor) #[minusOne, constant.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[constant.res[0]!, minusOne] #[ty] (fun _ => true)
      return (ty, constant.properties))
    (fun (ty, constantProps) => do
      let complementedProps ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
        (ty, constantProps) complementConstantProperty
      CreateProg.operation (.llvm .mlir__constant) #[] #[ty] complementedProps)
    (fun result => result.res[0]!)

set_option maxHeartbeats 1000000 in
private theorem invertIntegerConstantPattern_valid (outerNotLeft : Bool) :
    Pattern.Valid (invertIntegerConstantPattern outerNotLeft) := by
  cases outerNotLeft <;> simp only [invertIntegerConstantPattern,
    matchIntConstantNormalized, Bool.false_eq_true, ite_false, ite_true] <;>
    unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [properties_of, guard_eq_cond_punit,
        MatchProg.collectBindings, MatchProg.collectDeclBindings,
        MatchProg.rootResults?, HandleContext.forbid, HandleContext.forbidMany,
        HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
        HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
        MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
        CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings,
        complementConstantProperty]
    simpConstantInversionSemantics
    rintro ⟨w, signedness⟩ constantProps constant hConstant hInterpConstant
    generalize hTyped : asLLVMConstantProperties constantProps = typedProps
    cases typedProps with
    | mk constantValue => cases constantValue with
      | float _ | dense _ | string _ => simp [isIntegralConstant, hTyped] at hConstant
      | integer constantAttr =>
        have hInterpTyped : InterpretsTo (.llvm .mlir__constant)
            (asLLVMConstantProperties constantProps) #[IntegerType.mk w signedness]
            #[] #[constant] := hInterpConstant
        rw [hTyped] at hInterpTyped
        obtain rfl := (constant_iff _ constantAttr _).mp hInterpTyped
        rintro minusOneProps minusOne hInterpMinusOne
        generalize hMinusTyped : asLLVMConstantProperties minusOneProps = minusTyped
        cases minusTyped with
        | mk minusValue => cases minusValue with
          | float _ | dense _ | string _ =>
            rintro _ _ _ hMinusOne
            have hMinusValue := congrArg
              (fun p : LLVMConstantProperties => p.value) hMinusTyped
            change minusOneProps.value = _ at hMinusValue
            simp [isNormalizedIntConstant, hMinusValue,
              asLLVMConstantProperties, IsTypeAttr.cast?_of] at hMinusOne
          | integer minusOneAttr =>
            have hInterpMinusTyped : InterpretsTo (.llvm .mlir__constant)
                (asLLVMConstantProperties minusOneProps) #[IntegerType.mk w signedness]
                #[] #[minusOne] := hInterpMinusOne
            rw [hMinusTyped] at hInterpMinusTyped
            obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusTyped
            rintro ⟨⟩ source hSource hMinusOne
            obtain rfl := (xor_iff _ _ _ _).mp hSource
            have hMinusValue : minusOneProps.value =
                LLVMConstantValue.integer minusOneAttr := by
              simpa [asLLVMConstantProperties] using
                congrArg (fun p : LLVMConstantProperties => p.value) hMinusTyped
            have hBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
              simpa [isNormalizedIntConstant, hMinusValue,
                asLLVMConstantProperties, IsTypeAttr.cast?_of] using hMinusOne
            rw [hBits]
            simp [complementConstantProperty, hTyped, IsTypeAttr.cast?_of]
            refine ⟨.int w (.val (BitVec.ofInt w (-constantAttr.value - 1))), ?_, ?_⟩
            · apply (constant_iff _ _ _).mpr
              simpa [IntegerAttr.ofInt] using congrArg
                (fun z => RuntimeValue.int w (.val z))
                (ofInt_normalizeValue { bitwidth := w, signedness := signedness }
                  (-constantAttr.value - 1)).symm
            refine ⟨rfl, ?_⟩
            rw [bitvec_ofInt_complement]
            rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
              rw [BitVec.ofInt_neg]
              exact BitVec.neg_one_eq_allOnes]
            simp [LLVM.Int.xor, Id.run, BitVec.xor_allOnes, BitVec.xor_comm]

private theorem poison_iff {signedness : IntegerType.Signedness} (w : Nat)
    (v : RuntimeValue) :
    InterpretsTo (.llvm .mlir__poison) () #[IntegerType.mk w signedness]
      #[] #[v] ↔ v = .int w .poison := by
  have hResultType :
      (#[TypeAttr.of IntegerType (IntegerType.mk w signedness)][0]? : Option TypeAttr) =
        some (TypeAttr.of IntegerType (IntegerType.mk w signedness)) := by rfl
  simp only [InterpretsTo]
  constructor
  · rintro ⟨_, hi⟩
    have hv := hi .empty
    simp only [interpretOp', Llvm.interpretOp', hResultType, integerType_of_val,
      Interp.pure_eq, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
      List.cons.injEq, and_true] at hv
    simpa only [mlir_poison_eq] using hv.symm
  · rintro rfl
    constructor
    · simp
    · intro memory
      simp only [interpretOp', Llvm.interpretOp', hResultType, integerType_of_val,
        mlir_poison_eq, Interp.pure_eq]

private def invertPoisonPattern (outerNotLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let minusOne ← matchIntConstantNormalized ty (-1)
      let _ ← if outerNotLeft then
        MatchProg.root (.llvm .xor) #[minusOne, poison.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[poison.res[0]!, minusOne] #[ty] (fun _ => true)
      return poison.res[0]!)
    pure (fun poison => poison)

set_option maxHeartbeats 500000 in
private theorem invertPoisonPattern_valid (outerNotLeft : Bool) :
    Pattern.Valid (invertPoisonPattern outerNotLeft) := by
  cases outerNotLeft <;> simp only [invertPoisonPattern,
    matchIntConstantNormalized, Bool.false_eq_true, ite_false, ite_true] <;>
    unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [properties_of, guard_eq_cond_punit,
        MatchProg.collectBindings, MatchProg.collectDeclBindings,
        MatchProg.rootResults?, HandleContext.forbid, HandleContext.forbidMany,
        HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
        HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
        MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
        CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
    simpPuddleSemantics
    rintro ⟨w, signedness⟩
    rintro ⟨⟩ poison hPoison
    obtain rfl := (poison_iff (signedness := signedness) w _).mp hPoison
    rintro ⟨constantValue⟩ minusOne hInterpMinusOne
    cases constantValue with
    | float _ | dense _ | string _ =>
      rintro _ _ _ hMinusOne
      simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
    | integer minusOneAttr =>
      obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
      rintro ⟨⟩ source hSource hMinusOne
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      simp [LLVM.Int.xor, Id.run]

public def invertIntegerConstant : Pattern OpCode := invertIntegerConstantPattern false
public theorem invertIntegerConstant_valid : Pattern.Valid invertIntegerConstant :=
  invertIntegerConstantPattern_valid false
public def invertIntegerConstantNotLeft : Pattern OpCode := invertIntegerConstantPattern true
public theorem invertIntegerConstantNotLeft_valid : Pattern.Valid invertIntegerConstantNotLeft :=
  invertIntegerConstantPattern_valid true
public def invertPoison : Pattern OpCode := invertPoisonPattern false
public theorem invertPoison_valid : Pattern.Valid invertPoison := invertPoisonPattern_valid false
public def invertPoisonNotLeft : Pattern OpCode := invertPoisonPattern true
public theorem invertPoisonNotLeft_valid : Pattern.Valid invertPoisonNotLeft :=
  invertPoisonPattern_valid true

end Veir.Passes.InstCombineLLVM.FreeInvertConstant
