module

public import Veir.Passes.InstCombineLLVM.GEPSemantics
public import Veir.Passes.InstCombineLLVM.SelectSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.GEPSelectConstantIndex

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.GEPSemantics
open Veir.Passes.InstCombineLLVM.ProofTactics

private def isIntegerConstant
    (props : propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  match (asLLVMConstantProperties props).value with
  | .integer _ => true
  | _ => false

private def addConstantProperties
    (input : TypeAttr × propertiesOf (OpCode.llvm .mlir__constant) ×
      propertiesOf (OpCode.llvm .mlir__constant)) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let (type, firstProps, secondProps) := input
  let some intType := type.cast? IntegerType | none
  let .integer first := (asLLVMConstantProperties firstProps).value | none
  let .integer second := (asLLVMConstantProperties secondProps).value | none
  return LLVMConstantProperties.mk
    (.integer (IntegerAttr.ofInt (first.value + second.value) intType))

private theorem gepResult_add_constants (stride : Nat) (base : LLVM.Ptr)
    (first second : Int) :
    gepResult stride
        (gepResult stride base (.val (BitVec.ofInt 64 first)))
        (.val (BitVec.ofInt 64 second)) =
      gepResult stride base (.val (BitVec.ofInt 64 (first + second))) := by
  rw [← gepResult_add_i64]
  simp [LLVM.Int.add, Id.run, BitVec.ofInt_add]

/-- InstructionCombining.cpp:2927-2967, RV64 scalar constant/select arm:
    `gep (gep base, C), (select c, T, F)` becomes
    `gep base, (select c, C+T, C+F)`. -/
public def gepSelectConstantIndex : Pattern OpCode := Pattern.Builder
  (do
    let ptrTy ← MatchProg.type (Attr := LLVM.PointerType)
    let condTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let idxTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 64)
    let base ← MatchProg.value ptrTy
    let cond ← MatchProg.value condTy
    let offset ← MatchProg.operation (.llvm .mlir__constant) #[] #[idxTy]
      isIntegerConstant
    let trueIndex ← MatchProg.operation (.llvm .mlir__constant) #[] #[idxTy]
      isIntegerConstant
    let falseIndex ← MatchProg.operation (.llvm .mlir__constant) #[] #[idxTy]
      isIntegerConstant
    let selected ← MatchProg.operation (.llvm .select)
      #[cond, trueIndex.res[0]!, falseIndex.res[0]!] #[idxTy] (fun _ => true)
    let inner ← MatchProg.operation (.llvm .getelementptr) #[base, offset.res[0]!]
      #[ptrTy] (fun props => props == dynamicGepI32Properties)
    let _ ← MatchProg.root (.llvm .getelementptr) #[inner.res[0]!, selected.res[0]!]
      #[ptrTy] (fun props => props == dynamicGepI32Properties)
    return (ptrTy, idxTy, base, cond, offset.properties,
      trueIndex.properties, falseIndex.properties))
  (fun (ptrTy, idxTy, base, cond, offsetProps, trueProps, falseProps) => do
    let foldedTrueProps ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      (idxTy, offsetProps, trueProps) addConstantProperties
    let foldedTrue ← CreateProg.operation (.llvm .mlir__constant) #[] #[idxTy]
      foldedTrueProps
    let foldedFalseProps ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      (idxTy, offsetProps, falseProps) addConstantProperties
    let foldedFalse ← CreateProg.operation (.llvm .mlir__constant) #[] #[idxTy]
      foldedFalseProps
    let selectProps ← CreateProg.property (.llvm .select) ()
    let selected ← CreateProg.operation (.llvm .select)
      #[cond, foldedTrue.res[0]!, foldedFalse.res[0]!] #[idxTy] selectProps
    let gepProps ← CreateProg.property (.llvm .getelementptr) dynamicGepI32Properties
    CreateProg.operation (.llvm .getelementptr) #[base, selected.res[0]!]
      #[ptrTy] gepProps)
  (fun result => result.res[0]!)

public theorem gepSelectConstantIndex_valid : Pattern.Valid gepSelectConstantIndex := by
  simp only [gepSelectConstantIndex]
  unfoldPuddleBuilder
  proveScalarPuddleStructure
  simpPuddleSemantics
  rintro ptrTy condType ⟨condW, condSignedness⟩ hCondType hCondWidth
  subst condType
  change condW = 1 at hCondWidth
  subst condW
  rintro idxType ⟨idxW, idxSignedness⟩ hIdxType hIdxWidth
  subst idxType
  change idxW = 64 at hIdxWidth
  subst idxW
  rintro base hBase cond hCond
  obtain ⟨base, rfl⟩ := RuntimeValue.Conforms.llvmPointerType.mp hBase
  obtain ⟨cond, rfl⟩ := RuntimeValue.Conforms.integerType.mp hCond
  rintro offsetProps offset hOffsetInteger hOffset
  generalize hOffsetTyped : asLLVMConstantProperties offsetProps = offsetTyped
  cases offsetTyped with
  | mk offsetValue =>
    cases offsetValue with
    | float _ | dense _ | string _ =>
      simp [isIntegerConstant, hOffsetTyped] at hOffsetInteger
    | integer offsetAttr =>
      have hOffsetTypedInterp :
          InterpretsTo (.llvm .mlir__constant)
            (asLLVMConstantProperties offsetProps)
            #[IntegerType.mk 64 idxSignedness] #[] #[offset] := hOffset
      rw [hOffsetTyped] at hOffsetTypedInterp
      obtain rfl := (constant_iff _ offsetAttr _).mp hOffsetTypedInterp
      rintro trueProps trueIndex hTrueInteger hTrue
      generalize hTrueTyped : asLLVMConstantProperties trueProps = trueTyped
      cases trueTyped with
      | mk trueValue =>
        cases trueValue with
        | float _ | dense _ | string _ =>
          simp [isIntegerConstant, hTrueTyped] at hTrueInteger
        | integer trueAttr =>
          have hTrueTypedInterp :
              InterpretsTo (.llvm .mlir__constant)
                (asLLVMConstantProperties trueProps)
                #[IntegerType.mk 64 idxSignedness] #[] #[trueIndex] := hTrue
          rw [hTrueTyped] at hTrueTypedInterp
          obtain rfl := (constant_iff _ trueAttr _).mp hTrueTypedInterp
          rintro falseProps falseIndex hFalseInteger hFalse
          generalize hFalseTyped : asLLVMConstantProperties falseProps = falseTyped
          cases falseTyped with
          | mk falseValue =>
            cases falseValue with
            | float _ | dense _ | string _ =>
              simp [isIntegerConstant, hFalseTyped] at hFalseInteger
            | integer falseAttr =>
              have hFalseTypedInterp :
                  InterpretsTo (.llvm .mlir__constant)
                    (asLLVMConstantProperties falseProps)
                    #[IntegerType.mk 64 idxSignedness] #[] #[falseIndex] := hFalse
              rw [hFalseTyped] at hFalseTypedInterp
              obtain rfl := (constant_iff _ falseAttr _).mp hFalseTypedInterp
              rintro ⟨⟩ selected hSelected
              obtain rfl := (select_iff 64 cond
                (.val (BitVec.ofInt 64 trueAttr.value))
                (.val (BitVec.ofInt 64 falseAttr.value)) selected).mp hSelected
              rintro innerProps inner hInnerProps hInner
              have hInnerPropsEq : innerProps = dynamicGepI32Properties :=
                beq_iff_eq.mp hInnerProps
              subst innerProps
              obtain rfl := (gep_i32_iff ptrTy base
                (.val (BitVec.ofInt 64 offsetAttr.value)) inner).mp hInner
              rintro outerProps source hOuterProps hSource
              have hOuterPropsEq : outerProps = dynamicGepI32Properties :=
                beq_iff_eq.mp hOuterProps
              subst outerProps
              obtain rfl := (gep_i32_iff ptrTy
                (gepResult 4 base (.val (BitVec.ofInt 64 offsetAttr.value)))
                (LLVM.Int.select cond
                  (.val (BitVec.ofInt 64 trueAttr.value))
                  (.val (BitVec.ofInt 64 falseAttr.value))) source).mp hSource
              simp [addConstantProperties, hOffsetTyped, hTrueTyped, hFalseTyped,
                IsTypeAttr.cast?_of]
              refine ⟨.int 64 (.val (BitVec.ofInt 64
                  (offsetAttr.value + trueAttr.value))), ?_, ?_⟩
              · apply (constant_iff _ _ _).mpr
                simpa [IntegerAttr.ofInt] using congrArg
                  (fun z => RuntimeValue.int 64 (.val z))
                  (ofInt_normalizeValue
                    { bitwidth := 64, signedness := idxSignedness }
                    (offsetAttr.value + trueAttr.value)).symm
              refine ⟨.int 64 (.val (BitVec.ofInt 64
                  (offsetAttr.value + falseAttr.value))), ?_, ?_⟩
              · apply (constant_iff _ _ _).mpr
                simpa [IntegerAttr.ofInt] using congrArg
                  (fun z => RuntimeValue.int 64 (.val z))
                  (ofInt_normalizeValue
                    { bitwidth := 64, signedness := idxSignedness }
                    (offsetAttr.value + falseAttr.value)).symm
              refine ⟨.int 64 (LLVM.Int.select cond
                  (.val (BitVec.ofInt 64 (offsetAttr.value + trueAttr.value)))
                  (.val (BitVec.ofInt 64 (offsetAttr.value + falseAttr.value)))),
                (select_iff 64 cond _ _ _).mpr rfl, ?_⟩
              refine ⟨.addr (gepResult 4 base (LLVM.Int.select cond
                  (.val (BitVec.ofInt 64 (offsetAttr.value + trueAttr.value)))
                  (.val (BitVec.ofInt 64 (offsetAttr.value + falseAttr.value))))),
                (gep_i32_iff ptrTy base _ _).mpr rfl, ?_⟩
              cases base with
              | poison =>
                simp [gepResult, LLVM.Int.select, Id.run,
                  RuntimeValue.isRefinedBy, LLVM.Ptr.isRefinedBy]
              | val baseValue =>
                cases cond with
                | poison =>
                  simp [gepResult, LLVM.Int.select, Id.run,
                    RuntimeValue.isRefinedBy, LLVM.Ptr.isRefinedBy]
                | val condBits =>
                  by_cases hCondTrue : condBits = BitVec.ofNat 1 1
                  · simp [LLVM.Int.select, Id.run, hCondTrue,
                      gepResult_add_constants, RuntimeValue.isRefinedBy,
                      LLVM.Ptr.isRefinedBy]
                    generalize gepResult 4 (.val baseValue)
                      (.val (BitVec.ofInt 64
                        (offsetAttr.value + trueAttr.value))) = result
                    cases result <;> simp
                  · simp [LLVM.Int.select, Id.run, hCondTrue,
                      gepResult_add_constants, RuntimeValue.isRefinedBy,
                      LLVM.Ptr.isRefinedBy]
                    generalize gepResult 4 (.val baseValue)
                      (.val (BitVec.ofInt 64
                        (offsetAttr.value + falseAttr.value))) = result
                    cases result <;> simp

end Veir.Passes.InstCombineLLVM.GEPSelectConstantIndex

#print axioms Veir.Passes.InstCombineLLVM.GEPSelectConstantIndex.gepSelectConstantIndex_valid
