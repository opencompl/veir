import Veir.Passes.ArithCanonicalize.FoldBitwiseSupport
import Veir.Passes.ArithCanonicalize.CommutativeSupport

namespace Veir.ArithCanonicalize.NestedBitwiseSupport
open Veir Veir.Data
open Veir.ArithCanonicalize.CommutativeSupport

theorem xor_cancel_left (w : Nat) (x a : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.xor (LLVM.Int.xor x a) a) ⊒ .int w x := by
  cases x <;> cases a <;>
    simp [LLVM.Int.xor, RuntimeValue.isRefinedBy, isRefinedBy,
      BitVec.xor_assoc, Id.run]

theorem xor_cancel_right (w : Nat) (x a : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.xor a (LLVM.Int.xor x a)) ⊒ .int w x := by
  have h (u v : BitVec w) : v ^^^ (u ^^^ v) = u := by
    calc
      v ^^^ (u ^^^ v) = (v ^^^ u) ^^^ v := by rw [← BitVec.xor_assoc]
      _ = (u ^^^ v) ^^^ v := by rw [BitVec.xor_comm v u]
      _ = u := by rw [BitVec.xor_assoc]; simp
  cases x <;> cases a <;>
    simp [LLVM.Int.xor, RuntimeValue.isRefinedBy, isRefinedBy,
      h, Id.run]

theorem xor_cancel_left_swapped (w : Nat) (x a : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.xor (LLVM.Int.xor a x) a) ⊒ .int w x := by
  rw [xor_comm a x]
  exact xor_cancel_left w x a

theorem xor_cancel_right_swapped (w : Nat) (x a : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.xor a (LLVM.Int.xor a x)) ⊒ .int w x := by
  rw [xor_comm a x]
  exact xor_cancel_right w x a

theorem and_absorb (w : Nat) (x y : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.and x (LLVM.Int.and x y)) ⊒
      .int w (LLVM.Int.and x y) := by
  have h (a b : BitVec w) : a &&& (a &&& b) = a &&& b := by
    rw [← BitVec.and_assoc]
    simp
  cases x <;> cases y <;>
    simp [LLVM.Int.and, RuntimeValue.isRefinedBy, isRefinedBy,
      h, Id.run]

theorem and_absorb_outer_swap (w : Nat) (x y : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.and (LLVM.Int.and x y) x) ⊒
      .int w (LLVM.Int.and x y) := by
  rw [and_comm (LLVM.Int.and x y) x]
  exact and_absorb w x y

theorem and_absorb_inner_swap (w : Nat) (x y : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.and x (LLVM.Int.and y x)) ⊒
      .int w (LLVM.Int.and y x) := by
  rw [and_comm y x]
  exact and_absorb w x y

theorem and_absorb_both_swap (w : Nat) (x y : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.and (LLVM.Int.and y x) x) ⊒
      .int w (LLVM.Int.and y x) := by
  rw [and_comm y x]
  exact and_absorb_outer_swap w x y

theorem or_absorb (w : Nat) (x y : LLVM.Int w) (di dout : Bool) :
    RuntimeValue.int w (LLVM.Int.or x (LLVM.Int.or x y di) dout) ⊒
      .int w (LLVM.Int.or x y di) := by
  have h (a b : BitVec w) : a ||| (a ||| b) = a ||| b := by
    rw [← BitVec.or_assoc]
    simp
  cases x with
  | poison => cases y <;> cases di <;> cases dout <;>
      simp [LLVM.Int.or, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val a =>
    cases y with
    | poison => cases di <;> cases dout <;>
        simp [LLVM.Int.or, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val b =>
      cases di <;> cases dout <;>
        simp [LLVM.Int.or, RuntimeValue.isRefinedBy, isRefinedBy, h, Id.run] <;>
        (by_cases h0 : a &&& b = 0#w <;>
          by_cases h1 : a &&& (a ||| b) = 0#w <;>
          simp_all [pure])

theorem or_absorb_outer_swap (w : Nat) (x y : LLVM.Int w) (di dout : Bool) :
    RuntimeValue.int w (LLVM.Int.or (LLVM.Int.or x y di) x dout) ⊒
      .int w (LLVM.Int.or x y di) := by
  rw [or_comm_flags (LLVM.Int.or x y di) x dout]
  exact or_absorb w x y di dout

theorem or_absorb_inner_swap (w : Nat) (x y : LLVM.Int w) (di dout : Bool) :
    RuntimeValue.int w (LLVM.Int.or x (LLVM.Int.or y x di) dout) ⊒
      .int w (LLVM.Int.or y x di) := by
  rw [or_comm_flags y x di]
  exact or_absorb w x y di dout

theorem or_absorb_both_swap (w : Nat) (x y : LLVM.Int w) (di dout : Bool) :
    RuntimeValue.int w (LLVM.Int.or (LLVM.Int.or y x di) x dout) ⊒
      .int w (LLVM.Int.or y x di) := by
  rw [or_comm_flags y x di]
  exact or_absorb_outer_swap w x y di dout

end Veir.ArithCanonicalize.NestedBitwiseSupport
