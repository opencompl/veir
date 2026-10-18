module

public import Veir.Passes.InstCombineLLVM.ProofTactics
public import Veir.Passes.InstCombineLLVM.ArithmeticBitwiseSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.NotAddConstant

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

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

/-- Scalar specialization of InstCombineAndOrXor.cpp:5340-5341:
    `~(X + C) -> ~C - X`, with the complement folded at the matched width. -/
private def notAddConstantPattern (notConstantLeft : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let constant ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      isIntegralConstant
    let minusOne ← matchIntConstantNormalized ty (-1)
    let sum ← MatchProg.operation (.llvm .add) #[x, constant.res[0]!] #[ty]
      (fun _ => true)
    let _ ← if notConstantLeft then
      MatchProg.root (.llvm .xor) #[minusOne, sum.res[0]!] #[ty] (fun _ => true)
    else
      MatchProg.root (.llvm .xor) #[sum.res[0]!, minusOne] #[ty] (fun _ => true)
    return (ty, x, constant.properties))
  (fun (ty, x, constantProps) => do
    let foldedProps ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      (ty, constantProps) complementConstantProperty
    let folded ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] foldedProps
    let sp ← CreateProg.property (.llvm .sub) default
    CreateProg.operation (.llvm .sub) #[folded.res[0]!, x] #[ty] sp)
  (fun result => result.res[0]!)

set_option linter.tacticCheckInstances false in
private theorem notAddConstantPattern_valid (notConstantLeft : Bool) :
    Pattern.Valid (notAddConstantPattern notConstantLeft) := by
  cases notConstantLeft <;> simp only [notAddConstantPattern, matchIntConstantNormalized,
    Bool.false_eq_true, ite_false, ite_true] <;>
  unfoldPuddleBuilder
  all_goals proveScalarPuddleStructure
  all_goals simpScalarPropertyPuddleSemantics
  all_goals
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
        rintro ⟨minusOneValue⟩ minusOne hInterpMinusOne
        cases minusOneValue with
        | float _ | dense _ | string _ =>
          rintro _ _ _ _ _ _ hMinusOne
          simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
        | integer minusOneAttr =>
          obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
          rintro addProps sum hSum
          obtain rfl := (add_iff _ _ _ _ _).mp hSum
          rintro ⟨⟩ source hSource
          obtain rfl := (xor_iff _ _ _ _).mp hSource
          rintro hMinusOne
          have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
            simpa [isNormalizedIntConstant, asLLVMConstantProperties,
              IsTypeAttr.cast?_of] using hMinusOne
          rw [hMinusOneBits]
          simp [complementConstantProperty, hTyped, IsTypeAttr.cast?_of]
          refine ⟨.int w (.val (BitVec.ofInt w (-constantAttr.value - 1))), ?_, ?_⟩
          · apply (constant_iff _ _ _).mpr
            simpa [IntegerAttr.ofInt] using congrArg
              (fun z => RuntimeValue.int w (.val z))
              (ofInt_normalizeValue { bitwidth := w, signedness := signedness }
                (-constantAttr.value - 1)).symm
          refine ⟨.int w (LLVM.Int.sub
              (.val (BitVec.ofInt w (-constantAttr.value - 1))) x),
            (sub_iff _ _ _ _ _).mpr rfl, ?_⟩
          refine ⟨rfl, ?_⟩
          simpa only [LLVM.Int.cast_self, llvm_xor_comm] using
            (not_add_refines_folded_constant_sub w x constantAttr.value
              addProps.nsw addProps.nuw)


public def notAddConstant : Pattern OpCode := notAddConstantPattern false
public theorem notAddConstant_valid : Pattern.Valid notAddConstant :=
  notAddConstantPattern_valid false

public def notAddConstantConstantLeft : Pattern OpCode := notAddConstantPattern true
public theorem notAddConstantConstantLeft_valid : Pattern.Valid notAddConstantConstantLeft :=
  notAddConstantPattern_valid true

end Veir.Passes.InstCombineLLVM.NotAddConstant
