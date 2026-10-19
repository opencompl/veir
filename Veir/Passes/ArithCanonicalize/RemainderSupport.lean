import Veir.Passes.ArithCanonicalize.ConstSupport

/-! Scalar integer remainder identities used by the Arith fold proofs. -/

namespace Veir.ArithCanonicalize

open Veir
open Veir.Data

private theorem refines_zero_of_poison_or_zero (w : Nat) (x : LLVM.Int w)
    (h : x = .poison ∨ x = .val 0) :
    RuntimeValue.int w x ⊒ .int w (.val 0) := by
  rcases h with h | h <;> simp [h, RuntimeValue.isRefinedBy, isRefinedBy]

theorem urem_one_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.urem x (.val (BitVec.ofInt w 1))) ⊒
      .int w (.val 0) := by
  apply refines_zero_of_poison_or_zero
  cases x <;> simp [LLVM.Int.urem, Id.run, BitVec.umod_one]
  all_goals split <;> simp_all [pure]

theorem srem_one_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.srem x (.val (BitVec.ofInt w 1))) ⊒
      .int w (.val 0) := by
  apply refines_zero_of_poison_or_zero
  cases x <;> simp [LLVM.Int.srem, Id.run, BitVec.srem_one]
  all_goals split <;> simp_all [pure]

theorem urem_zero_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.urem (.val 0) x) ⊒ .int w (.val 0) := by
  apply refines_zero_of_poison_or_zero
  cases x <;> simp [LLVM.Int.urem, Id.run]
  all_goals split <;> simp_all [pure]

theorem srem_zero_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.srem (.val 0) x) ⊒ .int w (.val 0) := by
  apply refines_zero_of_poison_or_zero
  cases x <;> simp [LLVM.Int.srem, Id.run]
  all_goals split <;> simp_all [pure]

theorem urem_self_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.urem x x) ⊒ .int w (.val 0) := by
  apply refines_zero_of_poison_or_zero
  cases x <;> simp [LLVM.Int.urem, Id.run, BitVec.umod_self]
  all_goals split <;> simp_all [pure]

theorem srem_self_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.srem x x) ⊒ .int w (.val 0) := by
  apply refines_zero_of_poison_or_zero
  cases x <;> simp [LLVM.Int.srem, Id.run, BitVec.srem_self]
  all_goals split <;> simp_all [pure]

end Veir.ArithCanonicalize
