module

public import Veir.Passes.InstCombineLLVM.ProofTactics
public import Veir.Passes.InstCombineLLVM.ArithmeticBitwiseSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.SubSubConstants

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

private def isIntegralConstant
    (props : propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  match (asLLVMConstantProperties props).value with
  | .integer _ => true
  | _ => false

private def subtractConstantProperties
    (input : TypeAttr × propertiesOf (OpCode.llvm .mlir__constant) ×
      propertiesOf (OpCode.llvm .mlir__constant)) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let (type, firstProps, secondProps) := input
  let some intType := type.cast? IntegerType | none
  let .integer first := (asLLVMConstantProperties firstProps).value | none
  let .integer second := (asLLVMConstantProperties secondProps).value | none
  return LLVMConstantProperties.mk
    (.integer (IntegerAttr.ofInt (first.value - second.value) intType))

/-- Scalar specialization of InstCombineAddSub.cpp:2678-2680:
    `C - (C2 - X) -> X + (C - C2)`. -/
public def subSubConstants : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let first ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty] isIntegralConstant
    let second ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty] isIntegralConstant
    let difference ← MatchProg.operation (.llvm .sub) #[second.res[0]!, x] #[ty]
      (fun _ => true)
    let _ ← MatchProg.root (.llvm .sub) #[first.res[0]!, difference.res[0]!] #[ty]
      (fun _ => true)
    return (ty, x, first.properties, second.properties))
  (fun (ty, x, firstProps, secondProps) => do
    let foldedProps ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      (ty, firstProps, secondProps) subtractConstantProperties
    let folded ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] foldedProps
    let ap ← CreateProg.property (.llvm .add) default
    CreateProg.operation (.llvm .add) #[x, folded.res[0]!] #[ty] ap)
  (fun result => result.res[0]!)

set_option linter.tacticCheckInstances false in
public theorem subSubConstants_valid : Pattern.Valid subSubConstants := by
  simp only [subSubConstants]
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
          rintro innerProps difference hDifference
          obtain rfl := (sub_iff _ _ _ _ _).mp hDifference
          rintro outerProps source hSource
          obtain rfl := (sub_iff _ _ _ _ _).mp hSource
          simp [subtractConstantProperties, hTypedFirst, hTypedSecond,
            IsTypeAttr.cast?_of]
          refine ⟨.int w (.val (BitVec.ofInt w
              (firstAttr.value - secondAttr.value))), ?_, ?_⟩
          · apply (constant_iff _ _ _).mpr
            simpa [IntegerAttr.ofInt] using congrArg
              (fun z => RuntimeValue.int w (.val z))
              (ofInt_normalizeValue { bitwidth := w, signedness := signedness }
                (firstAttr.value - secondAttr.value)).symm
          refine ⟨.int w (LLVM.Int.add x
              (.val (BitVec.ofInt w (firstAttr.value - secondAttr.value)))),
            (add_iff _ _ _ _ _).mpr rfl, ?_⟩
          refine ⟨rfl, ?_⟩
          simpa only [LLVM.Int.cast_self, Int.sub_eq_add_neg, BitVec.ofInt_add,
              BitVec.ofInt_neg, BitVec.sub_eq_add_neg] using
            (sub_sub_constants_refine w x (BitVec.ofInt w firstAttr.value)
              (BitVec.ofInt w secondAttr.value) innerProps.nsw innerProps.nuw
              outerProps.nsw outerProps.nuw)

end Veir.Passes.InstCombineLLVM.SubSubConstants
