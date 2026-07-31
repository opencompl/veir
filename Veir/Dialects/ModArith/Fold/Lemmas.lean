module

public import Veir.Dialects.ModArith.Fold.Basic
public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Refinement

import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement

public section

namespace Veir.Fold.Proofs.ModArith

open Veir.Data

theorem mul_zero_residue_rhs (modulus : Nat)
    (x : LLVM.Int 8) (c : BitVec 8) (h : c.toNat % modulus = 0) :
    (match x.toNat?, (LLVM.Int.val c).toNat? with
     | some x, some y => LLVM.Int.constant 8 ((x * y) % modulus)
     | _, _ => LLVM.Int.poison) ⊒ LLVM.Int.constant 8 0 := by
  cases x with
  | poison => simp [LLVM.Int.toNat?, isRefinedBy]
  | val x =>
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
    simp [LLVM.Int.toNat?, LLVM.Int.constant, isRefinedBy, hk]
    rw [Int.mul_emod]
    simp

theorem mul_zero_residue_lhs (modulus : Nat)
    (c : BitVec 8) (x : LLVM.Int 8) (h : c.toNat % modulus = 0) :
    (match (LLVM.Int.val c).toNat?, x.toNat? with
     | some x, some y => LLVM.Int.constant 8 ((x * y) % modulus)
     | _, _ => LLVM.Int.poison) ⊒ LLVM.Int.constant 8 0 := by
  cases x with
  | poison => simp [LLVM.Int.toNat?, isRefinedBy]
  | val x =>
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
    simp [LLVM.Int.toNat?, LLVM.Int.constant, isRefinedBy, hk]
    rw [Int.mul_emod]
    simp

end Veir.Fold.Proofs.ModArith
