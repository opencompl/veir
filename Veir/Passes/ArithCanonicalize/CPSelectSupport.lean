import Veir.Passes.ArithCanonicalize.CastSupport

namespace Veir.ArithCanonicalize.CPSelectSupport
open Veir Veir.Data Veir.Puddle

theorem select_one_zero_extui (c : LLVM.Int 1) (h : 1 < w) :
    RuntimeValue.int w
      (LLVM.Int.select c (.val (BitVec.ofInt w 1)) (.val (BitVec.ofInt w 0))) ⊒
      .int w (LLVM.Int.zext c w false h) := by
  cases c with
  | poison => simp [LLVM.Int.select, LLVM.Int.zext, RuntimeValue.isRefinedBy,
      isRefinedBy, Id.run]
  | val v =>
    have hv : v = 0#1 ∨ v = 1#1 := by bv_decide
    rcases hv with hv | hv <;> subst v <;>
      simp [LLVM.Int.select, LLVM.Int.zext,
        BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem select_zero_one_extui_not (c : LLVM.Int 1) (h : 1 < w) :
    RuntimeValue.int w
      (LLVM.Int.select c (.val (BitVec.ofInt w 0)) (.val (BitVec.ofInt w 1))) ⊒
      .int w (LLVM.Int.zext (LLVM.Int.xor c (.val (1#1))) w false h) := by
  cases c with
  | poison => simp [LLVM.Int.select, LLVM.Int.xor, LLVM.Int.zext,
      RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val v =>
    have hv : v = 0#1 ∨ v = 1#1 := by bv_decide
    rcases hv with hv | hv <;> subst v <;>
      simp [LLVM.Int.select, LLVM.Int.xor, LLVM.Int.zext,
        BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

end Veir.ArithCanonicalize.CPSelectSupport
