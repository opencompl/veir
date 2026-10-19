import Veir.Passes.ArithCanonicalize.ExtendedSupport

namespace Veir.ArithCanonicalize.ExtendedMoreSupport
open Veir Veir.Data Veir.Puddle

theorem smul_zero (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.mul x (.val 0)) ⊒ .int w (.val 0) ∧
    RuntimeValue.int w (LLVM.Int.smulHigh x (.val 0)) ⊒ .int w (.val 0) := by
  have hz : (0#w).signExtend (w + w) = 0 := by
    rw [BitVec.signExtend_eq_setWidth_of_msb_false (by simp)]
    simp
  cases x <;>
    simp [LLVM.Int.mul, LLVM.Int.smulHigh, hz,
      RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem umul_zero (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.mul x (.val 0)) ⊒ .int w (.val 0) ∧
    RuntimeValue.int w (LLVM.Int.umulHigh x (.val 0)) ⊒ .int w (.val 0) := by
  cases x <;>
    simp [LLVM.Int.mul, LLVM.Int.umulHigh, RuntimeValue.isRefinedBy,
      isRefinedBy, Id.run]

theorem high_zeroExtend (v : BitVec w) :
    (v.zeroExtend (w + w)).extractLsb' w w = 0 := by
  ext i hi
  simp only [BitVec.getElem_extractLsb', BitVec.getElem_zero]
  rw [BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth]
  simp [show ¬w + i < w by omega]

theorem umul_one (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.mul x (.val (BitVec.ofInt w 1))) ⊒ .int w x ∧
    RuntimeValue.int w (LLVM.Int.umulHigh x (.val (BitVec.ofInt w 1))) ⊒
      .int w (.val 0) := by
  cases w with
  | zero =>
    cases x <;> simp [BitVec.of_length_zero, LLVM.Int.mul, LLVM.Int.umulHigh,
      RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | succ n =>
    have hone : (BitVec.ofInt (n + 1) 1).zeroExtend ((n + 1) + (n + 1)) = 1 := by
      simpa [BitVec.zeroExtend_eq_setWidth] using
        (BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt
          (show 0 < n + 1 by omega) (w := (n + 1) + (n + 1)))
    cases x <;>
      simp [LLVM.Int.mul, LLVM.Int.umulHigh, hone,
        high_zeroExtend, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

end Veir.ArithCanonicalize.ExtendedMoreSupport
