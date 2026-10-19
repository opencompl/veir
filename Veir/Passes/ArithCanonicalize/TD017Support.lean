import Veir.Passes.ArithCanonicalize.ExtendedSupport
import Veir.Passes.ArithCanonicalize.SelectSupport

namespace Veir.ArithCanonicalize.TD017Support
open Veir Veir.Data

theorem one_sext (w : Nat) (hw : 1 < w) :
    (BitVec.ofInt w 1).signExtend (w + w) = 1#(w+w) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by omega)]
  simp [BitVec.toInt_one_of_lt hw, BitVec.toInt_one_of_lt (by omega : 1 < w + w)]

theorem high_sign (v : BitVec w) :
    (v.signExtend (w+w)).extractLsb' w w =
      (if v.msb then BitVec.allOnes w else 0#w) := by
  rw [BitVec.signExtend_eq_append_of_le (by omega : w ≤ w+w)]
  rw [BitVec.extractLsb'_cast]
  have hw : w + w - w = w := by omega
  rw [hw]
  exact BitVec.extractLsb'_append_eq_left

theorem sign_bool (w : Nat) (hw : 0 < w) (b : Bool) :
    (BitVec.ofBool b).signExtend w = if b then BitVec.allOnes w else 0#w := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by omega : 1 ≤ w)]
  cases b <;> simp [BitVec.toInt_allOnes, hw]

theorem smul_one_refines (x : LLVM.Int w) (hw : 1 < w) :
    RuntimeValue.int w (LLVM.Int.mul x (.val (1#w))) ⊒ .int w x ∧
    RuntimeValue.int w (LLVM.Int.smulHigh x (.val (1#w))) ⊒
      .int w (LLVM.Int.sext (LLVM.Int.icmp x (.val (0#w)) .slt) w (by omega)) := by
  cases x with
  | poison =>
    simp [LLVM.Int.mul, LLVM.Int.smulHigh, LLVM.Int.icmp, LLVM.Int.sext,
      RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val v =>
    have hOne := one_sext w hw
    have hHigh := high_sign v
    have hBool := sign_bool w (by omega) v.msb
    simp [LLVM.Int.mul, LLVM.Int.smulHigh, LLVM.Int.icmp, LLVM.Int.sext,
      LLVM.IntPred.eval, BitVec.slt_zero_eq_msb, hBool,
      RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    have hOne' : (1#w).signExtend (w+w) = 1#(w+w) := by simpa using hOne
    rw [hOne', BitVec.mul_one, hHigh]

end Veir.ArithCanonicalize.TD017Support
