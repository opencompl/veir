module

public import Veir.Passes.InstCombineLLVM.GEPSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.GEPConstantOffsetToPtrAdd

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.GEPSemantics
open Veir.Passes.InstCombineLLVM.ProofTactics

private def isIntegerConstant
    (props : propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  match (asLLVMConstantProperties props).value with
  | .integer _ => true
  | _ => false

private def scaleConstantProperty
    (input : TypeAttr × propertiesOf (OpCode.llvm .mlir__constant)) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let (type, sourceProps) := input
  let some intType := type.cast? IntegerType | none
  let .integer sourceAttr := (asLLVMConstantProperties sourceProps).value | none
  return LLVMConstantProperties.mk
    (.integer (IntegerAttr.ofInt (sourceAttr.value * 4) intType))

/-- RV64 scalar specialization of InstructionCombining.cpp:3423-3437:
    an unflagged one-index `i32` GEP by any i64 constant is the same address as
    an `i8` GEP by four times that constant. -/
public def gepConstantOffsetToPtrAdd : Pattern OpCode := Pattern.Builder
  (do
    let ptrTy ← MatchProg.type (Attr := LLVM.PointerType)
    let idxTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 64)
    let ptr ← MatchProg.value ptrTy
    let idx ← MatchProg.operation (.llvm .mlir__constant) #[] #[idxTy]
      isIntegerConstant
    let _ ← MatchProg.root (.llvm .getelementptr) #[ptr, idx.res[0]!] #[ptrTy]
      (fun props => props == dynamicGepI32Properties)
    return (ptrTy, idxTy, ptr, idx.properties))
  (fun (ptrTy, idxTy, ptr, sourceProps) => do
    let constantProps ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      (idxTy, sourceProps) scaleConstantProperty
    let byteOffset ← CreateProg.operation (.llvm .mlir__constant) #[] #[idxTy]
      constantProps
    let gepProps ← CreateProg.property (.llvm .getelementptr) dynamicGepI8Properties
    CreateProg.operation (.llvm .getelementptr) #[ptr, byteOffset.res[0]!]
      #[ptrTy] gepProps)
  (fun result => result.res[0]!)

public theorem gepConstantOffsetToPtrAdd_valid :
    Pattern.Valid gepConstantOffsetToPtrAdd := by
  simp only [gepConstantOffsetToPtrAdd]
  unfoldPuddleBuilder
  proveScalarPuddleStructure
  simpPuddleSemantics
  rintro ptrTy _ ⟨idxW, idxSignedness⟩ rfl hWidth ptr hPtr
  change idxW = 64 at hWidth
  subst idxW
  obtain ⟨ptr, rfl⟩ := RuntimeValue.Conforms.llvmPointerType.mp hPtr
  rintro sourceProps idx hInteger hIdx
  generalize hTyped : asLLVMConstantProperties sourceProps = typed
  cases typed with
  | mk sourceValue =>
    cases sourceValue with
    | float _ | dense _ | string _ => simp [isIntegerConstant, hTyped] at hInteger
    | integer idxAttr =>
      have hIdxTyped :
          InterpretsTo (.llvm .mlir__constant) (asLLVMConstantProperties sourceProps)
            #[IntegerType.mk 64 idxSignedness] #[] #[idx] := hIdx
      rw [hTyped] at hIdxTyped
      obtain rfl := (constant_iff _ idxAttr _).mp hIdxTyped
      rintro gepProps source hProps hSource
      have hPropsEq : gepProps = dynamicGepI32Properties := beq_iff_eq.mp hProps
      subst gepProps
      obtain rfl := (gep_i32_iff ptrTy ptr
        (.val (BitVec.ofInt 64 idxAttr.value)) source).mp hSource
      simp [scaleConstantProperty, hTyped, IsTypeAttr.cast?_of]
      refine ⟨.int 64 (.val (BitVec.ofInt 64 (idxAttr.value * 4))), ?_, ?_⟩
      · apply (constant_iff _ _ _).mpr
        simpa [IntegerAttr.ofInt] using congrArg
          (fun z => RuntimeValue.int 64 (.val z))
          (ofInt_normalizeValue
            { bitwidth := 64, signedness := idxSignedness }
            (idxAttr.value * 4)).symm
      refine ⟨.addr (gepResult 1 ptr
          (.val (BitVec.ofInt 64 (idxAttr.value * 4)))),
        (gep_i8_iff ptrTy ptr
          (.val (BitVec.ofInt 64 (idxAttr.value * 4))) _).mpr rfl, ?_⟩
      cases ptr <;>
        simp [gepResult, RuntimeValue.isRefinedBy, LLVM.Ptr.isRefinedBy,
          BitVec.ofInt_mul]
      rw [UInt64.ofNat_mod_size', UInt64.ofNat_mul]
      rfl

end Veir.Passes.InstCombineLLVM.GEPConstantOffsetToPtrAdd

#print axioms Veir.Passes.InstCombineLLVM.GEPConstantOffsetToPtrAdd.gepConstantOffsetToPtrAdd_valid
