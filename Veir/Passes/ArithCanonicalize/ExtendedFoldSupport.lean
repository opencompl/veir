import Veir.Passes.ArithCanonicalize.ExtendedSupport

namespace Veir.ArithCanonicalize

open Veir Veir.Data

theorem uadd_zero_extended_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.add x (.val 0)) ⊒ .int w x ∧
    RuntimeValue.int 1 (LLVM.Int.uaddOverflowFlag x (.val 0)) ⊒ .int 1 (.val 0) := by
  cases x with
  | poison => simp [RuntimeValue.isRefinedBy, LLVM.Int.add,
      LLVM.Int.uaddOverflowFlag, isRefinedBy, Id.run]
  | val a =>
    have h : ¬2 ^ w ≤ a.toNat := Nat.not_le.mpr a.isLt
    simp [RuntimeValue.isRefinedBy, LLVM.Int.add,
      LLVM.Int.uaddOverflowFlag, BitVec.uaddOverflow, isRefinedBy, Id.run, h]

theorem usub_zero_extended_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.sub x (.val 0)) ⊒ .int w x ∧
    RuntimeValue.int 1 (LLVM.Int.usubOverflowFlag x (.val 0)) ⊒ .int 1 (.val 0) := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.sub,
    LLVM.Int.usubOverflowFlag, BitVec.usubOverflow, isRefinedBy, Id.run]

theorem usub_self_extended_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.sub x x) ⊒ .int w (.val 0) ∧
    RuntimeValue.int 1 (LLVM.Int.usubOverflowFlag x x) ⊒ .int 1 (.val 0) := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.sub,
    LLVM.Int.usubOverflowFlag, BitVec.usubOverflow, isRefinedBy, Id.run]

end Veir.ArithCanonicalize
