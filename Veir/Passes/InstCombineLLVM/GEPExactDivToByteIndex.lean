module

public import Veir.Passes.InstCombineLLVM.GEPSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.GEPExactDivToByteIndex

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.GEPSemantics
open Veir.Passes.InstCombineLLVM.ProofTactics

private theorem exactShiftScaling (bits : BitVec 64)
    (h : bits >>> 2 <<< 2 = bits) :
    (bits >>> 2).toNat * 4 = bits.toNat := by
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] at hn ⊢
  simp only [Nat.reducePow] at hn ⊢
  have hle := Nat.div_mul_le_self bits.toNat 4
  have hlt : bits.toNat / 4 * 4 < 18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hlt] at hn
  exact hn

/-- InstructionCombining.cpp:3565-3580, RV64 `i32`/logical-shift arm:
    `gep i32, base, (lshr exact bytes, 2)` becomes `gep i8, base, bytes`. -/
public def gepExactDivToByteIndex : Pattern OpCode := Pattern.Builder
  (do
    let ptrTy ← MatchProg.type (Attr := LLVM.PointerType)
    let idxTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 64)
    let base ← MatchProg.value ptrTy
    let bytes ← MatchProg.value idxTy
    let two ← matchIntConstant idxTy 2
    let divided ← MatchProg.operation (.llvm .lshr) #[bytes, two] #[idxTy]
      (fun props => props.exact)
    let _ ← MatchProg.root (.llvm .getelementptr) #[base, divided.res[0]!]
      #[ptrTy] (fun props => props == dynamicGepI32Properties)
    return (ptrTy, base, bytes))
  (fun (ptrTy, base, bytes) => do
    let gepProps ← CreateProg.property (.llvm .getelementptr) dynamicGepI8Properties
    CreateProg.operation (.llvm .getelementptr) #[base, bytes] #[ptrTy] gepProps)
  (fun result => result.res[0]!)

public theorem gepExactDivToByteIndex_valid : Pattern.Valid gepExactDivToByteIndex := by
  simp only [gepExactDivToByteIndex, matchIntConstant]
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
    have hAmountValue : amountAttr.value = 2 := of_decide_eq_true hAmount
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
    refine ⟨.addr (gepResult 1 base bytes),
      (gep_i8_iff ptrTy base bytes _).mpr rfl, ?_⟩
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
            have hScaling := exactShiftScaling bits hExactShift
            simp [gepResult, RuntimeValue.isRefinedBy, LLVM.Ptr.isRefinedBy,
              hScaling]
            rw [← BitVec.toNat_ushiftRight]
            change UInt64.ofNat (bits >>> 2).toNat * UInt64.ofNat 4 = _
            rw [← UInt64.ofNat_mul, hScaling]
            simp

end Veir.Passes.InstCombineLLVM.GEPExactDivToByteIndex

#print axioms Veir.Passes.InstCombineLLVM.GEPExactDivToByteIndex.gepExactDivToByteIndex_valid
