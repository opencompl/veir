import Veir.Dialects.Arith.Puddle

namespace Veir.ArithCanonicalize.F027Support
open Veir Veir.Data

theorem cancel_unsigned (a b : BitVec w) (h : ¬ BitVec.umulOverflow a b)
    (hb : b ≠ 0) : (a*b)/b = a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, BitVec.toNat_mul_of_not_umulOverflow h]
  have hp : 0 < b.toNat := by
    have : b.toNat ≠ 0 := by
      intro h0
      apply hb
      apply BitVec.eq_of_toNat_eq
      simpa using h0
    omega
  simpa [Nat.mul_comm] using Nat.mul_div_cancel_left a.toNat hp

theorem rem_unsigned (a b : BitVec w) (h : ¬ BitVec.umulOverflow a b) :
    (a*b) % b = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_mul_of_not_umulOverflow h]
  simp

theorem mul_comm (x y : LLVM.Int w) (nsw nuw : Bool) :
    LLVM.Int.mul x y nsw nuw = LLVM.Int.mul y x nsw nuw := by
  cases x <;> cases y <;>
    simp [LLVM.Int.mul, BitVec.smulOverflow, BitVec.umulOverflow,
      Int.mul_comm, Nat.mul_comm, BitVec.mul_comm, Id.run]

theorem div_mul_nuw (x y : LLVM.Int w) (nsw exact : Bool) :
    RuntimeValue.int w (LLVM.Int.udiv (LLVM.Int.mul x y nsw true) y exact) ⊒
      .int w x := by
  cases x with
  | poison =>
    cases y <;> simp [LLVM.Int.mul, LLVM.Int.udiv, RuntimeValue.isRefinedBy,
      isRefinedBy, Id.run]
  | val a =>
    cases y with
    | poison =>
      simp [LLVM.Int.mul, LLVM.Int.udiv, RuntimeValue.isRefinedBy,
        isRefinedBy, Id.run]
    | val b =>
      by_cases hU : BitVec.umulOverflow a b <;>
        by_cases hS : BitVec.smulOverflow a b <;>
        by_cases hb : b = 0 <;>
        cases nsw <;> cases exact
      all_goals
        try have hQ := cancel_unsigned a b hU hb
        try have hR := rem_unsigned a b hU
        simp_all [LLVM.Int.mul, LLVM.Int.udiv, RuntimeValue.isRefinedBy,
          isRefinedBy, Id.run, pure]


end Veir.ArithCanonicalize.F027Support
