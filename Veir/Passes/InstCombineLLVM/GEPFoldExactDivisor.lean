module

public import Veir.Passes.InstCombineLLVM.GEPSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.GEPFoldExactDivisor

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.GEPSemantics
open Veir.Passes.InstCombineLLVM.ProofTactics

private def constantProperty (value : Int) (type : TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt value intType))

private theorem exactShift3To1 (bits : BitVec 64)
    (h : bits >>> 3 <<< 3 = bits) :
    bits >>> 1 <<< 1 = bits := by
  apply BitVec.eq_of_toNat_eq
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] at hn ⊢
  simp only [Nat.reducePow] at hn ⊢
  have hle8 := Nat.div_mul_le_self bits.toNat 8
  have hlt8 : bits.toNat / 8 * 8 < 18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hlt8] at hn
  have hle2 := Nat.div_mul_le_self bits.toNat 2
  have hlt2 : bits.toNat / 2 * 2 < 18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hlt2]
  omega

private theorem exactShift3Scaling (bits : BitVec 64)
    (h : bits >>> 3 <<< 3 = bits) :
    (bits >>> 3).toNat * 4 = (bits >>> 1).toNat := by
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] at hn ⊢
  simp only [Nat.reducePow] at hn ⊢
  have hle := Nat.div_mul_le_self bits.toNat 8
  have hlt : bits.toNat / 8 * 8 < 18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hlt] at hn
  omega

/-- InstructionCombining.cpp:3581-3614, RV64 `i32`/logical-shift arm:
    `gep i32, base, (lshr exact bytes, 3)` becomes
    `gep i8, base, (lshr exact bytes, 1)`. -/
public def gepFoldExactDivisor : Pattern OpCode := Pattern.Builder
  (do
    let ptrTy ← MatchProg.type (Attr := LLVM.PointerType)
    let idxTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 64)
    let base ← MatchProg.value ptrTy
    let bytes ← MatchProg.value idxTy
    let three ← matchIntConstant idxTy 3
    let divided ← MatchProg.operation (.llvm .lshr) #[bytes, three] #[idxTy]
      (fun props => props.exact)
    let _ ← MatchProg.root (.llvm .getelementptr) #[base, divided.res[0]!]
      #[ptrTy] (fun props => props == dynamicGepI32Properties)
    return (ptrTy, idxTy, base, bytes))
  (fun (ptrTy, idxTy, base, bytes) => do
    let oneProps ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant))) idxTy
      (constantProperty 1)
    let one ← CreateProg.operation (.llvm .mlir__constant) #[] #[idxTy] oneProps
    let shiftProps ← CreateProg.property (.llvm .lshr) { exact := true }
    let shifted ← CreateProg.operation (.llvm .lshr) #[bytes, one.res[0]!]
      #[idxTy] shiftProps
    let gepProps ← CreateProg.property (.llvm .getelementptr) dynamicGepI8Properties
    CreateProg.operation (.llvm .getelementptr) #[base, shifted.res[0]!]
      #[ptrTy] gepProps)
  (fun result => result.res[0]!)

public theorem gepFoldExactDivisor_valid : Pattern.Valid gepFoldExactDivisor := by
  simp only [gepFoldExactDivisor, matchIntConstant]
  unfoldPuddleBuilder
  proveScalarPuddleStructure
  simpPuddleSemantics
  rintro ptrTy _ ⟨idxW, idxSignedness⟩ rfl hWidth base hBase bytes hBytes
  change idxW = 64 at hWidth
  subst idxW
  obtain ⟨base, rfl⟩ := RuntimeValue.Conforms.llvmPointerType.mp hBase
  obtain ⟨bytes, rfl⟩ := RuntimeValue.Conforms.integerType.mp hBytes
  rintro ⟨amountValue⟩ amount hAmount hInterpAmount
  cases amountValue with
  | float _ | dense _ | string _ => simp at hAmount
  | integer amountAttr =>
    have hAmountValue : amountAttr.value = 3 := of_decide_eq_true hAmount
    obtain rfl := (constant_iff _ amountAttr _).mp hInterpAmount
    rintro shiftProps divided hExact hDivided
    have hExactTrue : shiftProps.exact = true := of_decide_eq_true hExact
    obtain rfl := (lshr_iff 64 shiftProps bytes
      (.val (BitVec.ofInt 64 amountAttr.value)) divided).mp hDivided
    rintro gepProps source hGepProps hSource
    have hGepPropsEq : gepProps = dynamicGepI32Properties := beq_iff_eq.mp hGepProps
    subst gepProps
    obtain rfl := (gep_i32_iff ptrTy base
      (LLVM.Int.lshr bytes (.val (BitVec.ofInt 64 amountAttr.value))
        shiftProps.exact) source).mp hSource
    simp [constantProperty, IsTypeAttr.cast?_of]
    refine ⟨.int 64 (.val (BitVec.ofInt 64 1)), ?_, ?_⟩
    · apply (constant_iff _ _ _).mpr
      simpa [IntegerAttr.ofInt] using congrArg
        (fun z => RuntimeValue.int 64 (.val z))
        (ofInt_normalizeValue
          { bitwidth := 64, signedness := idxSignedness } 1).symm
    refine ⟨.int 64 (LLVM.Int.lshr bytes (.val (BitVec.ofInt 64 1)) true),
      (lshr_iff 64 { exact := true } bytes _ _).mpr rfl, ?_⟩
    refine ⟨.addr (gepResult 1 base
        (LLVM.Int.lshr bytes (.val (BitVec.ofInt 64 1)) true)),
      (gep_i8_iff ptrTy base _ _).mpr rfl, ?_⟩
    rw [hAmountValue, hExactTrue]
    cases base with
    | poison =>
      simp [gepResult, LLVM.Int.lshr, Id.run,
        RuntimeValue.isRefinedBy, LLVM.Ptr.isRefinedBy]
    | val baseValue =>
      cases bytes with
      | poison =>
        simp [gepResult, LLVM.Int.lshr, Id.run,
          RuntimeValue.isRefinedBy, LLVM.Ptr.isRefinedBy]
      | val bits =>
        simp only [LLVM.Int.lshr, Id.run]
        split
        · simp [gepResult, RuntimeValue.isRefinedBy, LLVM.Ptr.isRefinedBy]
        · rename_i hAmountInRange
          split
          · simp [gepResult, RuntimeValue.isRefinedBy, LLVM.Ptr.isRefinedBy]
          · rename_i hExactShift
            simp at hExactShift
            have hTargetExact := exactShift3To1 bits hExactShift
            have hScaling := exactShift3Scaling bits hExactShift
            simp [gepResult, LLVM.Int.lshr, Id.run, hTargetExact,
              RuntimeValue.isRefinedBy, LLVM.Ptr.isRefinedBy]
            rw [← BitVec.toNat_ushiftRight]
            change UInt64.ofNat (bits >>> 3).toNat * UInt64.ofNat 4 = _
            rw [← UInt64.ofNat_mul, hScaling]
            simp

end Veir.Passes.InstCombineLLVM.GEPFoldExactDivisor

#print axioms Veir.Passes.InstCombineLLVM.GEPFoldExactDivisor.gepFoldExactDivisor_valid
