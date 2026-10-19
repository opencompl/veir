import Veir.Dialects.Arith.Puddle

namespace Veir.ArithCanonicalize

open Veir Veir.Data

theorem and_zero_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.and x (.val 0)) ⊒ .int w (.val 0) := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.and,
    isRefinedBy, Id.run, pure]

theorem and_ones_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.and x (.val (BitVec.ofInt w (-1)))) ⊒ .int w x := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.and,
    isRefinedBy, Id.run, BitVec.ofInt_neg, BitVec.neg_one_eq_allOnes]

theorem or_zero_refines (w : Nat) (x : LLVM.Int w) (disjoint : Bool) :
    RuntimeValue.int w (LLVM.Int.or x (.val 0) disjoint) ⊒ .int w x := by
  cases x <;> cases disjoint <;>
    simp [RuntimeValue.isRefinedBy, LLVM.Int.or, isRefinedBy, Id.run, pure]

theorem or_ones_refines (w : Nat) (x : LLVM.Int w) (disjoint : Bool) :
    RuntimeValue.int w (LLVM.Int.or x (.val (BitVec.ofInt w (-1))) disjoint) ⊒
      .int w (.val (BitVec.ofInt w (-1))) := by
  cases x with
  | poison =>
    simp [RuntimeValue.isRefinedBy, LLVM.Int.or, isRefinedBy, Id.run]
  | val a =>
    cases disjoint
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.or, isRefinedBy,
        Id.run, BitVec.ofInt_neg, BitVec.neg_one_eq_allOnes]
    · by_cases h : a = 0#w
      · simp [RuntimeValue.isRefinedBy, LLVM.Int.or, isRefinedBy,
          Id.run, pure, h, BitVec.ofInt_neg, BitVec.neg_one_eq_allOnes]
      · simp [RuntimeValue.isRefinedBy, LLVM.Int.or, isRefinedBy,
          Id.run, pure, h, BitVec.ofInt_neg, BitVec.neg_one_eq_allOnes]

theorem xor_zero_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.xor x (.val 0)) ⊒ .int w x := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.xor,
    isRefinedBy, Id.run, pure]

theorem xor_self_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.xor x x) ⊒ .int w (.val 0) := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.xor,
    isRefinedBy, Id.run, pure]

theorem and_self_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.and x x) ⊒ .int w x := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.and,
    isRefinedBy, Id.run]

theorem or_self_refines (w : Nat) (x : LLVM.Int w) (d : Bool) :
    RuntimeValue.int w (LLVM.Int.or x x d) ⊒ .int w x := by
  cases x with
  | poison => simp [RuntimeValue.isRefinedBy, LLVM.Int.or, isRefinedBy, Id.run]
  | val a =>
    cases d
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.or, isRefinedBy, Id.run]
    · by_cases h : a = 0#w
      · simp [RuntimeValue.isRefinedBy, LLVM.Int.or, isRefinedBy, Id.run, h]
      · simp [RuntimeValue.isRefinedBy, LLVM.Int.or, isRefinedBy,
          Id.run, pure, h]

theorem or_const_refines (w : Nat) (a b : BitVec w) (d : Bool) :
    RuntimeValue.int w (LLVM.Int.or (.val a) (.val b) d) ⊒
      .int w (.val (a ||| b)) := by
  cases d
  · simp [RuntimeValue.isRefinedBy, LLVM.Int.or, isRefinedBy, Id.run]
  · by_cases h : a &&& b = 0#w
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.or, isRefinedBy, Id.run, h]
    · simp [RuntimeValue.isRefinedBy, LLVM.Int.or, isRefinedBy,
        Id.run, pure, h]

theorem and_complement_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.and x
      (LLVM.Int.xor x (.val (BitVec.ofInt w (-1))))) ⊒ .int w (.val 0) := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.and, LLVM.Int.xor,
    isRefinedBy, Id.run, BitVec.ofInt_neg, BitVec.neg_one_eq_allOnes]

theorem and_complement_comm_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.and
      (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) x) ⊒ .int w (.val 0) := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.and, LLVM.Int.xor,
    isRefinedBy, Id.run, BitVec.ofInt_neg, BitVec.neg_one_eq_allOnes]

theorem or_complement_refines (w : Nat) (x : LLVM.Int w) (d : Bool) :
    RuntimeValue.int w (LLVM.Int.or x
      (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) d) ⊒
      .int w (.val (BitVec.ofInt w (-1))) := by
  cases x <;> cases d <;>
    simp [RuntimeValue.isRefinedBy, LLVM.Int.or, LLVM.Int.xor,
      isRefinedBy, Id.run, BitVec.ofInt_neg, BitVec.neg_one_eq_allOnes]

theorem or_complement_comm_refines (w : Nat) (x : LLVM.Int w) (d : Bool) :
    RuntimeValue.int w (LLVM.Int.or
      (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) x d) ⊒
      .int w (.val (BitVec.ofInt w (-1))) := by
  cases x <;> cases d <;>
    simp [RuntimeValue.isRefinedBy, LLVM.Int.or, LLVM.Int.xor,
      isRefinedBy, Id.run, BitVec.ofInt_neg, BitVec.neg_one_eq_allOnes]

end Veir.ArithCanonicalize
