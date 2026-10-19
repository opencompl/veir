import Veir.Passes.ArithCanonicalize.CastSupport

/-! Casts whose intermediate width remains wider than the original operand. -/
namespace Veir.ArithCanonicalize.CastIntermediateSupport

open Veir Veir.Data Veir.Puddle

theorem truncate_signExtend (v : BitVec a) (_hab : a < b) (hbc : b < c) :
    (v.signExtend c).truncate b = v.signExtend b := by
  ext i hi
  simp only [BitVec.truncate_eq_setWidth, BitVec.getElem_setWidth]
  rw [← BitVec.getLsbD_eq_getElem (x := v.signExtend b) hi]
  rw [BitVec.getLsbD_signExtend, BitVec.getLsbD_signExtend]
  simp [hi, show i < c by omega]

theorem truncate_zeroExtend (v : BitVec a) (_hab : a < b) (hbc : b < c) :
    (v.zeroExtend c).truncate b = v.zeroExtend b := by
  simp only [BitVec.truncate_eq_setWidth]
  rw [BitVec.setWidth_setWidth_of_le]
  omega

theorem trunci_extsi_middle (x : LLVM.Int a) (hab : a < b) (hbc : b < c)
    (nsw nuw : Bool) :
    RuntimeValue.int b (LLVM.Int.trunc (LLVM.Int.sext x c (by omega)) b
      nsw nuw (by omega)) ⊒ .int b (LLVM.Int.sext x b hab) := by
  cases x with
  | poison => simp [LLVM.Int.sext, LLVM.Int.trunc, RuntimeValue.isRefinedBy,
      isRefinedBy, Id.run]
  | val v =>
    have hLow := truncate_signExtend v hab hbc
    have hs : (v.signExtend b).signExtend c = v.signExtend c := by
      apply BitVec.eq_of_toInt_eq
      simp only [BitVec.toInt_signExtend_of_le (Nat.le_of_lt hab),
        BitVec.toInt_signExtend_of_le (Nat.le_of_lt hbc),
        BitVec.toInt_signExtend_of_le (by omega : a ≤ c)]
    by_cases hu : (v.signExtend b).setWidth c = v.signExtend c <;>
      cases nsw <;> cases nuw <;>
      simp [LLVM.Int.sext, LLVM.Int.trunc, hLow, hs, hu,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

theorem trunci_extui_middle (x : LLVM.Int a) (hab : a < b) (hbc : b < c)
    (nneg nsw nuw : Bool) :
    RuntimeValue.int b (LLVM.Int.trunc (LLVM.Int.zext x c nneg (by omega)) b
      nsw nuw (by omega)) ⊒ .int b (LLVM.Int.zext x b nneg hab) := by
  cases x with
  | poison => simp [LLVM.Int.zext, LLVM.Int.trunc, RuntimeValue.isRefinedBy,
      isRefinedBy, Id.run]
  | val v =>
    have hLow := truncate_zeroExtend v hab hbc
    by_cases hv : v.msb = true <;>
      by_cases hs : (v.zeroExtend b).signExtend c = v.zeroExtend c <;>
      by_cases hu : (v.zeroExtend b).zeroExtend c = v.zeroExtend c <;>
      cases nneg <;> cases nsw <;> cases nuw <;>
      simp [LLVM.Int.zext, LLVM.Int.trunc, hLow, hv, hs, hu,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

end Veir.ArithCanonicalize.CastIntermediateSupport
