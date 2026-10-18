module

public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.AddSubConstants

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

private def isIntegralConstant
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

/-- Scalar specialization of InstCombineAddSub.cpp:876-880:
    `add (sub C1, X), C2 -> sub (C1 + C2), X`. -/
public def addSubConstants : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let first ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty] isIntegralConstant
    let difference ← MatchProg.operation (.llvm .sub) #[first.res[0]!, x] #[ty]
      (fun _ => true)
    let second ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty] isIntegralConstant
    let _ ← MatchProg.root (.llvm .add) #[difference.res[0]!, second.res[0]!] #[ty]
      (fun _ => true)
    return (ty, x, first.properties, second.properties))
  (fun (ty, x, firstProps, secondProps) => do
    let foldedProps ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      (ty, firstProps, secondProps) addConstantProperties
    let folded ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] foldedProps
    let sp ← CreateProg.property (.llvm .sub) default
    CreateProg.operation (.llvm .sub) #[folded.res[0]!, x] #[ty] sp)
  (fun result => result.res[0]!)

set_option linter.tacticCheckInstances false in
public theorem addSubConstants_valid : Pattern.Valid addSubConstants := by
  simp only [addSubConstants]
  unfoldPuddleBuilder
  proveScalarPuddleStructure
  simpScalarPropertyPuddleSemantics
  rintro ⟨w, signedness⟩ x
  rintro firstProps first hFirst hInterpFirst
  generalize hTypedFirst : asLLVMConstantProperties firstProps = typedFirst
  cases typedFirst with
  | mk firstValue =>
    cases firstValue with
    | float _ | dense _ | string _ => simp [isIntegralConstant, hTypedFirst] at hFirst
    | integer firstAttr =>
      have hInterpFirstTyped :
          InterpretsTo (.llvm .mlir__constant) (asLLVMConstantProperties firstProps)
            #[IntegerType.mk w signedness] #[] #[first] := hInterpFirst
      rw [hTypedFirst] at hInterpFirstTyped
      obtain rfl := (constant_iff _ firstAttr _).mp hInterpFirstTyped
      rintro subProps difference hDifference
      obtain rfl := (sub_iff _ _ _ _ _).mp hDifference
      rintro secondProps second hSecond hInterpSecond
      generalize hTypedSecond : asLLVMConstantProperties secondProps = typedSecond
      cases typedSecond with
      | mk secondValue =>
        cases secondValue with
        | float _ | dense _ | string _ =>
          simp [isIntegralConstant, hTypedSecond] at hSecond
        | integer secondAttr =>
          have hInterpSecondTyped :
              InterpretsTo (.llvm .mlir__constant) (asLLVMConstantProperties secondProps)
                #[IntegerType.mk w signedness] #[] #[second] := hInterpSecond
          rw [hTypedSecond] at hInterpSecondTyped
          obtain rfl := (constant_iff _ secondAttr _).mp hInterpSecondTyped
          rintro addProps source hSource
          obtain rfl := (add_iff _ _ _ _ _).mp hSource
          simp [addConstantProperties, hTypedFirst, hTypedSecond, IsTypeAttr.cast?_of]
          refine ⟨.int w (.val (BitVec.ofInt w
              (firstAttr.value + secondAttr.value))), ?_, ?_⟩
          · apply (constant_iff _ _ _).mpr
            simpa [IntegerAttr.ofInt] using congrArg
              (fun z => RuntimeValue.int w (.val z))
              (ofInt_normalizeValue { bitwidth := w, signedness := signedness }
                (firstAttr.value + secondAttr.value)).symm
          refine ⟨.int w (LLVM.Int.sub
              (.val (BitVec.ofInt w (firstAttr.value + secondAttr.value))) x),
            (sub_iff _ _ _ _ _).mpr rfl, ?_⟩
          refine ⟨rfl, ?_⟩
          simpa only [LLVM.Int.cast_self, BitVec.ofInt_add] using
            (add_sub_constants_refine w x (BitVec.ofInt w firstAttr.value)
              (BitVec.ofInt w secondAttr.value) subProps.nsw subProps.nuw
              addProps.nsw addProps.nuw)

end Veir.Passes.InstCombineLLVM.AddSubConstants
