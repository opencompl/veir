module

public import Veir.Passes.InstCombineLLVM.ArithmeticBitwiseSemantics
import all Veir.Data.LLVM.Int.Basic

namespace Veir.Passes.InstCombineLLVM

open Veir Veir.Data

public theorem bitvec_ofInt_complement (w : Nat) (value : Int) :
    BitVec.ofInt w (-value - 1) = ~~~(BitVec.ofInt w value) := by
  rw [show -value - 1 = -value + (-1) by omega]
  rw [BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.ofInt_neg]
  change -BitVec.ofInt w value + -(1#w) = ~~~(BitVec.ofInt w value)
  rw [BitVec.not_eq_neg_add, BitVec.sub_eq_add_neg]

public theorem double_not_refines (w : Nat) (x : LLVM.Int w) :
    LLVM.Int.xor (LLVM.Int.xor x (.val (BitVec.ofInt w (-1))))
        (.val (BitVec.ofInt w (-1))) ⊒ x := by
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  cases x <;> simp [LLVM.Int.xor, Id.run, isRefinedBy_eq, BitVec.xor_allOnes]

public theorem not_add_not_right_refines_sub (w : Nat) (a x : LLVM.Int w)
    (nsw nuw : Bool) :
    LLVM.Int.xor
        (LLVM.Int.add a (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) nsw nuw)
        (.val (BitVec.ofInt w (-1))) ⊒ LLVM.Int.sub x a := by
  apply isRefinedBy_trans (xor_refine_mono w
    (add_flags_refine w a (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) nsw nuw)
    (isRefinedBy_refl _))
  cases a <;> cases x <;> simp [LLVM.Int.xor, LLVM.Int.add, LLVM.Int.sub, Id.run]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  simp only [BitVec.xor_allOnes]
  rw [bitvec_not_add, BitVec.not_not]
  exact isRefinedBy_refl _

public theorem not_add_not_left_refines_sub (w : Nat) (x b : LLVM.Int w)
    (nsw nuw : Bool) :
    LLVM.Int.xor
        (LLVM.Int.add (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) b nsw nuw)
        (.val (BitVec.ofInt w (-1))) ⊒ LLVM.Int.sub x b := by
  rw [llvm_add_comm_flags]
  exact not_add_not_right_refines_sub w b x nsw nuw

public theorem not_xor_not_right_refines_xor (w : Nat) (a x : LLVM.Int w) :
    LLVM.Int.xor
        (LLVM.Int.xor a (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))))
        (.val (BitVec.ofInt w (-1))) ⊒ LLVM.Int.xor a x := by
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  cases a <;> cases x <;>
    simp [LLVM.Int.xor, Id.run, isRefinedBy_eq, BitVec.xor_allOnes,
      BitVec.not_xor_right]

public theorem not_xor_not_left_refines_xor (w : Nat) (x b : LLVM.Int w) :
    LLVM.Int.xor
        (LLVM.Int.xor (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) b)
        (.val (BitVec.ofInt w (-1))) ⊒ LLVM.Int.xor x b := by
  rw [llvm_xor_comm (LLVM.Int.xor x _) b]
  rw [llvm_xor_comm x b]
  exact not_xor_not_right_refines_xor w b x

public theorem not_sub_not_left_refines_add (w : Nat) (x b : LLVM.Int w)
    (nsw nuw : Bool) :
    LLVM.Int.xor
        (LLVM.Int.sub (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) b nsw nuw)
        (.val (BitVec.ofInt w (-1))) ⊒ LLVM.Int.add x b := by
  apply isRefinedBy_trans
    (not_sub_refines_not_add w
      (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) b nsw nuw)
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  cases x <;> cases b <;>
    simp [LLVM.Int.xor, LLVM.Int.add, Id.run, isRefinedBy_eq, BitVec.xor_allOnes]

public theorem not_ashr_not_refines_ashr (w : Nat) (x amount : LLVM.Int w)
    (exactFlag : Bool) :
    LLVM.Int.xor
        (LLVM.Int.ashr (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) amount exactFlag)
        (.val (BitVec.ofInt w (-1))) ⊒ LLVM.Int.ashr x amount false := by
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  cases x with
  | poison => simp [LLVM.Int.xor, LLVM.Int.ashr, Id.run]
  | val x =>
    cases amount with
    | poison => simp [LLVM.Int.xor, LLVM.Int.ashr, Id.run]
    | val amount =>
      have hmod : w % 2 ^ w = w := Nat.mod_eq_of_lt Nat.lt_two_pow_self
      by_cases hlarge : w ≤ amount.toNat
      · simp [LLVM.Int.xor, LLVM.Int.ashr, Id.run, BitVec.le_def, hmod, hlarge]
      · by_cases hexact : exactFlag = true ∧
            ((~~~x) >>> amount.toNat) <<< amount.toNat ≠ ~~~x
        · simp [LLVM.Int.xor, LLVM.Int.ashr, Id.run, BitVec.le_def,
            BitVec.xor_allOnes, BitVec.ushiftRight_eq', BitVec.sshiftRight_eq',
            hmod, hlarge, hexact, isRefinedBy_eq]
        · simp [LLVM.Int.xor, LLVM.Int.ashr, Id.run, BitVec.le_def,
            BitVec.xor_allOnes, BitVec.ushiftRight_eq', BitVec.sshiftRight_eq',
            hmod, hlarge, hexact, BitVec.not_sshiftRight_not, isRefinedBy_eq]

public theorem not_or_not_not_refines_and (w : Nat) (x y : LLVM.Int w)
    (disjoint : Bool) :
    LLVM.Int.xor
        (LLVM.Int.or
          (LLVM.Int.xor x (.val (BitVec.ofInt w (-1))))
          (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))) disjoint)
        (.val (BitVec.ofInt w (-1))) ⊒ LLVM.Int.and x y := by
  apply isRefinedBy_trans (xor_refine_mono w
    (or_flags_refine w _ _ disjoint) (isRefinedBy_refl _))
  cases x <;> cases y <;> simp [LLVM.Int.xor, LLVM.Int.or, LLVM.Int.and, Id.run]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  simp only [BitVec.xor_allOnes, BitVec.not_or, BitVec.not_not]
  exact isRefinedBy_refl _

public theorem not_and_not_not_refines_or (w : Nat) (x y : LLVM.Int w) :
    LLVM.Int.xor
        (LLVM.Int.and
          (LLVM.Int.xor x (.val (BitVec.ofInt w (-1))))
          (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))))
        (.val (BitVec.ofInt w (-1))) ⊒ LLVM.Int.or x y false := by
  cases x <;> cases y <;> simp [LLVM.Int.xor, LLVM.Int.or, LLVM.Int.and, Id.run]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  simp only [BitVec.xor_allOnes, BitVec.not_and, BitVec.not_not]
  exact isRefinedBy_refl _

end Veir.Passes.InstCombineLLVM
