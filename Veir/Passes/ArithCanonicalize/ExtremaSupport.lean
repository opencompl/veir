import Veir.Passes.ArithCanonicalize.CommutativeSupport

/-! All-width signed and unsigned extremum identities, with poison refinement. -/
namespace Veir.ArithCanonicalize.ExtremaSupport

open Veir Veir.Data Veir.ArithCanonicalize.CommutativeSupport

private theorem intMax_upper (bits : BitVec w) : bits.sle (BitVec.intMax w) = true := by
  simp [BitVec.sle, BitVec.toInt_intMax]
  exact BitVec.toInt_le

private theorem intMin_lower (bits : BitVec w) : (BitVec.intMin w).sle bits = true := by
  exact BitVec.intMin_sle bits

private theorem allOnes_upper (bits : BitVec w) : bits.ule (BitVec.allOnes w) = true := by
  simp [BitVec.ule, BitVec.toNat_allOnes]
  have h := bits.isLt
  omega

private theorem zero_lower (bits : BitVec w) : (0#w).ule bits = true := by
  simp [BitVec.ule]

theorem maxsi_top (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.smax x (.val (BitVec.intMax w))) ⊒
      .int w (.val (BitVec.intMax w)) := by
  cases x with
  | poison => simp [LLVM.Int.smax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val bits =>
    simp [LLVM.Int.smax, intMax_upper, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem maxsi_bottom (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.smax x (.val (BitVec.intMin w))) ⊒ .int w x := by
  rw [smax_comm]
  cases x with
  | poison => simp [LLVM.Int.smax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val bits =>
    simp [LLVM.Int.smax, intMin_lower, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem minsi_bottom (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.smin x (.val (BitVec.intMin w))) ⊒
      .int w (.val (BitVec.intMin w)) := by
  rw [smin_comm]
  cases x with
  | poison => simp [LLVM.Int.smin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val bits =>
    simp [LLVM.Int.smin, intMin_lower, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem minsi_top (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.smin x (.val (BitVec.intMax w))) ⊒ .int w x := by
  cases x with
  | poison => simp [LLVM.Int.smin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val bits =>
    simp [LLVM.Int.smin, intMax_upper, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem maxui_top (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.umax x (.val (BitVec.allOnes w))) ⊒
      .int w (.val (BitVec.allOnes w)) := by
  cases x with
  | poison => simp [LLVM.Int.umax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val bits =>
    simp [LLVM.Int.umax, allOnes_upper, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem maxui_bottom (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.umax x (.val (0#w))) ⊒ .int w x := by
  rw [umax_comm]
  cases x with
  | poison => simp [LLVM.Int.umax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val bits =>
    simp [LLVM.Int.umax, zero_lower, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem minui_bottom (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.umin x (.val (0#w))) ⊒ .int w (.val (0#w)) := by
  rw [umin_comm]
  cases x with
  | poison => simp [LLVM.Int.umin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val bits =>
    simp [LLVM.Int.umin, zero_lower, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem minui_top (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.umin x (.val (BitVec.allOnes w))) ⊒ .int w x := by
  cases x with
  | poison => simp [LLVM.Int.umin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val bits =>
    simp [LLVM.Int.umin, allOnes_upper, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

end Veir.ArithCanonicalize.ExtremaSupport
