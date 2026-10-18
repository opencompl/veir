module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Data.LLVM.Int.Basic

namespace Veir.Passes.InstCombineLLVM

open Veir Veir.Data

public theorem or_refine_mono (w : Nat) {a a' b b' : LLVM.Int w} (disjoint : Bool)
    (ha : a ⊒ a') (hb : b ⊒ b') :
    LLVM.Int.or a b disjoint ⊒ LLVM.Int.or a' b' disjoint := by
  cases a with
  | poison => exact poison_isRefinedBy _
  | val a =>
    cases a' with
    | poison => exact ((isRefinedBy_eq _ _).mp ha).elim
    | val a' =>
      have haa : a = a' := (isRefinedBy_eq _ _).mp ha
      subst a'
      cases b with
      | poison => exact poison_isRefinedBy _
      | val b =>
        cases b' with
        | poison => exact ((isRefinedBy_eq _ _).mp hb).elim
        | val b' =>
          have hbb : b = b' := (isRefinedBy_eq _ _).mp hb
          subst b'
          exact isRefinedBy_refl _

public theorem and_refine_mono (w : Nat) {a a' b b' : LLVM.Int w}
    (ha : a ⊒ a') (hb : b ⊒ b') : LLVM.Int.and a b ⊒ LLVM.Int.and a' b' := by
  cases a with
  | poison => exact poison_isRefinedBy _
  | val a =>
    cases a' with
    | poison => exact ((isRefinedBy_eq _ _).mp ha).elim
    | val a' =>
      have haa : a = a' := (isRefinedBy_eq _ _).mp ha
      subst a'
      cases b with
      | poison => exact poison_isRefinedBy _
      | val b =>
        cases b' with
        | poison => exact ((isRefinedBy_eq _ _).mp hb).elim
        | val b' =>
          have hbb : b = b' := (isRefinedBy_eq _ _).mp hb
          subst b'
          exact isRefinedBy_refl _

public theorem bitvec_self_xor_or_eq_and_not {w : Nat} (x y : BitVec w) :
    y ^^^ (x ||| y) = x &&& ~~~y := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
  cases x[i] <;> cases y[i] <;> decide

public theorem xor_self_or_refines_and_not (w : Nat) (x y : LLVM.Int w)
    (disjoint : Bool) :
    LLVM.Int.xor y (LLVM.Int.or x y disjoint) ⊒
      LLVM.Int.and x (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))) := by
  apply isRefinedBy_trans
    (xor_refine_mono w (isRefinedBy_refl _) (or_flags_refine w x y disjoint))
  cases x <;> cases y <;> simp [LLVM.Int.xor, LLVM.Int.or, LLVM.Int.and, Id.run]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes, BitVec.xor_allOnes]
  rw [bitvec_self_xor_or_eq_and_not]
  exact isRefinedBy_refl _

public theorem bitvec_self_xor_and_eq_not_and {w : Nat} (x y : BitVec w) :
    y ^^^ (x &&& y) = ~~~x &&& y := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
  cases x[i] <;> cases y[i] <;> decide

public theorem xor_self_and_eq_not_and (w : Nat) (x y : LLVM.Int w) :
    LLVM.Int.xor y (LLVM.Int.and x y) =
      LLVM.Int.and (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) y := by
  cases x <;> cases y <;> simp [LLVM.Int.xor, LLVM.Int.and, Id.run]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes, BitVec.xor_allOnes]
  exact bitvec_self_xor_and_eq_not_and _ _

public theorem xor_self_and_refines_not_and (w : Nat) (x y : LLVM.Int w) :
    LLVM.Int.xor y (LLVM.Int.and x y) ⊒
      LLVM.Int.and (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) y := by
  rw [xor_self_and_eq_not_and]
  exact isRefinedBy_refl _

public theorem bitvec_and_not_xor_not_eq_not_and {w : Nat} (x y : BitVec w) :
    (x &&& ~~~y) ^^^ ~~~x = ~~~(x &&& y) := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
  cases x[i] <;> cases y[i] <;> decide

public theorem and_not_xor_not_refines_not_and (w : Nat) (x y : LLVM.Int w) :
    LLVM.Int.xor (LLVM.Int.and x (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))))
        (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) ⊒
      LLVM.Int.xor (LLVM.Int.and x y) (.val (BitVec.ofInt w (-1))) := by
  cases x <;> cases y <;> simp [LLVM.Int.xor, LLVM.Int.and, Id.run]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  simp only [BitVec.xor_allOnes]
  rw [bitvec_and_not_xor_not_eq_not_and]
  exact isRefinedBy_refl _

public theorem bitvec_not_and_xor_self_eq_or {w : Nat} (x y : BitVec w) :
    (~~~x &&& y) ^^^ x = x ||| y := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not,
    BitVec.getElem_or]
  cases x[i] <;> cases y[i] <;> decide

public theorem not_and_xor_self_refines_or (w : Nat) (x y : LLVM.Int w) :
    LLVM.Int.xor
        (LLVM.Int.and (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) y) x ⊒
      LLVM.Int.or x y false := by
  cases x <;> cases y <;> simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes, BitVec.xor_allOnes]
  rw [bitvec_not_and_xor_self_eq_or]
  exact isRefinedBy_refl _

public theorem bitvec_xor_xor_or_shared_eq {w : Nat} (a b c : BitVec w) :
    (a ^^^ b) ^^^ (a ||| c) = (~~~a &&& c) ^^^ b := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not,
    BitVec.getElem_or]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> decide

public theorem xor_xor_or_shared_refines (w : Nat) (a b c : LLVM.Int w)
    (disjoint : Bool) :
    LLVM.Int.xor (LLVM.Int.xor a b) (LLVM.Int.or a c disjoint) ⊒
      LLVM.Int.xor
        (LLVM.Int.and (LLVM.Int.xor a (.val (BitVec.ofInt w (-1)))) c) b := by
  apply isRefinedBy_trans
    (xor_refine_mono w (isRefinedBy_refl _) (or_flags_refine w a c disjoint))
  cases a <;> cases b <;> cases c <;>
    simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes, BitVec.xor_allOnes]
  rw [bitvec_xor_xor_or_shared_eq]
  exact isRefinedBy_refl _

public theorem bitvec_or_and_not_and_eq_xor {w : Nat} (a b : BitVec w) :
    (a ||| b) &&& ~~~(a &&& b) = a ^^^ b := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not,
    BitVec.getElem_or]
  cases a[i] <;> cases b[i] <;> decide

public theorem or_and_not_and_refines_xor (w : Nat) (a b : LLVM.Int w)
    (disjoint : Bool) :
    LLVM.Int.and (LLVM.Int.or a b disjoint)
        (LLVM.Int.xor (LLVM.Int.and a b) (.val (BitVec.ofInt w (-1)))) ⊒
      LLVM.Int.xor a b := by
  cases disjoint
  · cases a with
    | poison => simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run]
    | val av => cases b with
      | poison => simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run]
      | val bv =>
        simp only [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run, Bool.false_eq_true,
          false_and, ↓reduceIte]
        rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
          rw [BitVec.ofInt_neg]
          exact BitVec.neg_one_eq_allOnes, BitVec.xor_allOnes,
          bitvec_or_and_not_and_eq_xor]
        exact isRefinedBy_refl _
  · cases a with
    | poison => simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run]
    | val av => cases b with
      | poison => simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run]
      | val bv =>
        by_cases h : av &&& bv = 0
        · rw [show LLVM.Int.or (.val av) (.val bv) true = .val (av ||| bv) by
            simp [LLVM.Int.or, Id.run, h]]
          simp only [LLVM.Int.xor, LLVM.Int.and, Id.run]
          rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
            rw [BitVec.ofInt_neg]
            exact BitVec.neg_one_eq_allOnes, BitVec.xor_allOnes,
            bitvec_or_and_not_and_eq_xor]
          exact isRefinedBy_refl _
        · rw [show LLVM.Int.or (.val av) (.val bv) true = .poison by
            simp only [LLVM.Int.or, Id.run, Bool.true_eq, true_and]
            rw [if_pos h]
            rfl]
          simp [LLVM.Int.xor, LLVM.Int.and, Id.run]

public theorem bitvec_complementary_masks_eq_xor {w : Nat} (a b : BitVec w) :
    (a &&& ~~~b) ||| (~~~a &&& b) = a ^^^ b := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not,
    BitVec.getElem_or]
  cases a[i] <;> cases b[i] <;> decide

public theorem bitvec_complementary_masks_disjoint {w : Nat} (a b : BitVec w) :
    (a &&& ~~~b) &&& (~~~a &&& b) = BitVec.ofNat w 0 := by
  ext i
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero_ofNat_zero]
  cases a[i] <;> cases b[i] <;> decide

public theorem complementary_masks_or_refines_xor (w : Nat) (a b : LLVM.Int w)
    (disjoint : Bool) :
    LLVM.Int.or
        (LLVM.Int.and a (LLVM.Int.xor b (.val (BitVec.ofInt w (-1)))))
        (LLVM.Int.and (LLVM.Int.xor a (.val (BitVec.ofInt w (-1)))) b) disjoint ⊒
      LLVM.Int.xor a b := by
  cases disjoint <;> cases a <;> cases b <;>
    simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run]
  all_goals
    rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
      rw [BitVec.ofInt_neg]
      exact BitVec.neg_one_eq_allOnes]
    simp only [BitVec.xor_allOnes]
  · rw [bitvec_complementary_masks_eq_xor]
    exact isRefinedBy_refl _
  · rw [bitvec_complementary_masks_disjoint]
    rw [bitvec_complementary_masks_eq_xor]
    exact isRefinedBy_refl _

public theorem bitvec_complementary_masks_xor_eq_xor {w : Nat} (a b : BitVec w) :
    (a &&& ~~~b) ^^^ (~~~a &&& b) = a ^^^ b := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
  cases a[i] <;> cases b[i] <;> decide

public theorem complementary_masks_xor_refines_xor (w : Nat) (a b : LLVM.Int w) :
    LLVM.Int.xor
        (LLVM.Int.and a (LLVM.Int.xor b (.val (BitVec.ofInt w (-1)))))
        (LLVM.Int.and (LLVM.Int.xor a (.val (BitVec.ofInt w (-1)))) b) ⊒
      LLVM.Int.xor a b := by
  cases a <;> cases b <;> simp [LLVM.Int.xor, LLVM.Int.and, Id.run]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  simp only [BitVec.xor_allOnes]
  rw [bitvec_complementary_masks_xor_eq_xor]
  exact isRefinedBy_refl _

public theorem bitvec_complementary_ors_eq_xor {w : Nat} (a b : BitVec w) :
    (a ||| ~~~b) ^^^ (~~~a ||| b) = a ^^^ b := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_or, BitVec.getElem_not]
  cases a[i] <;> cases b[i] <;> decide

public theorem complementary_ors_xor_refines_xor (w : Nat) (a b : LLVM.Int w)
    (leftDisjoint rightDisjoint : Bool) :
    LLVM.Int.xor
        (LLVM.Int.or a (LLVM.Int.xor b (.val (BitVec.ofInt w (-1)))) leftDisjoint)
        (LLVM.Int.or (LLVM.Int.xor a (.val (BitVec.ofInt w (-1)))) b rightDisjoint) ⊒
      LLVM.Int.xor a b := by
  apply isRefinedBy_trans (xor_refine_mono w
    (or_flags_refine w a (LLVM.Int.xor b (.val (BitVec.ofInt w (-1)))) leftDisjoint)
    (or_flags_refine w (LLVM.Int.xor a (.val (BitVec.ofInt w (-1)))) b rightDisjoint))
  cases a <;> cases b <;> simp [LLVM.Int.xor, LLVM.Int.or, Id.run]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  simp only [BitVec.xor_allOnes]
  rw [bitvec_complementary_ors_eq_xor]
  exact isRefinedBy_refl _

public theorem bitvec_and_or_not_or_eq_not_xor {w : Nat} (a b : BitVec w) :
    (a &&& b) ||| ~~~(a ||| b) = ~~~(a ^^^ b) := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not,
    BitVec.getElem_or]
  cases a[i] <;> cases b[i] <;> decide

public theorem and_or_not_or_refines_not_xor (w : Nat) (a b : LLVM.Int w)
    (innerDisjoint outerDisjoint : Bool) :
    LLVM.Int.or (LLVM.Int.and a b)
        (LLVM.Int.xor (LLVM.Int.or a b innerDisjoint)
          (.val (BitVec.ofInt w (-1)))) outerDisjoint ⊒
      LLVM.Int.xor (LLVM.Int.xor a b) (.val (BitVec.ofInt w (-1))) := by
  apply isRefinedBy_trans (or_flags_refine w _ _ outerDisjoint)
  apply isRefinedBy_trans (or_refine_mono w false (isRefinedBy_refl _)
    (xor_refine_mono w (or_flags_refine w a b innerDisjoint) (isRefinedBy_refl _)))
  cases a <;> cases b <;> simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  simp only [BitVec.xor_allOnes]
  rw [bitvec_and_or_not_or_eq_not_xor]
  exact isRefinedBy_refl _

public theorem bitvec_xor_or_not_or_eq_not_and {w : Nat} (a b : BitVec w) :
    (a ^^^ b) ||| ~~~(a ||| b) = ~~~(a &&& b) := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not,
    BitVec.getElem_or]
  cases a[i] <;> cases b[i] <;> decide

public theorem xor_or_not_or_refines_not_and (w : Nat) (a b : LLVM.Int w)
    (innerDisjoint outerDisjoint : Bool) :
    LLVM.Int.or (LLVM.Int.xor a b)
        (LLVM.Int.xor (LLVM.Int.or a b innerDisjoint)
          (.val (BitVec.ofInt w (-1)))) outerDisjoint ⊒
      LLVM.Int.xor (LLVM.Int.and a b) (.val (BitVec.ofInt w (-1))) := by
  apply isRefinedBy_trans (or_flags_refine w _ _ outerDisjoint)
  apply isRefinedBy_trans (or_refine_mono w false (isRefinedBy_refl _)
    (xor_refine_mono w (or_flags_refine w a b innerDisjoint) (isRefinedBy_refl _)))
  cases a <;> cases b <;> simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  simp only [BitVec.xor_allOnes]
  rw [bitvec_xor_or_not_or_eq_not_and]
  exact isRefinedBy_refl _

public theorem bitvec_complementary_ors_and_eq_not_xor {w : Nat} (a b : BitVec w) :
    (a ||| ~~~b) &&& (~~~a ||| b) = ~~~(a ^^^ b) := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not,
    BitVec.getElem_or]
  cases a[i] <;> cases b[i] <;> decide

public theorem complementary_ors_and_refines_not_xor (w : Nat) (a b : LLVM.Int w)
    (leftDisjoint rightDisjoint : Bool) :
    LLVM.Int.and
        (LLVM.Int.or a (LLVM.Int.xor b (.val (BitVec.ofInt w (-1)))) leftDisjoint)
        (LLVM.Int.or (LLVM.Int.xor a (.val (BitVec.ofInt w (-1)))) b rightDisjoint) ⊒
      LLVM.Int.xor (LLVM.Int.xor a b) (.val (BitVec.ofInt w (-1))) := by
  apply isRefinedBy_trans (and_refine_mono w
    (or_flags_refine w a (LLVM.Int.xor b (.val (BitVec.ofInt w (-1)))) leftDisjoint)
    (or_flags_refine w (LLVM.Int.xor a (.val (BitVec.ofInt w (-1)))) b rightDisjoint))
  cases a <;> cases b <;> simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  simp only [BitVec.xor_allOnes]
  rw [bitvec_complementary_ors_and_eq_not_xor]
  exact isRefinedBy_refl _

public theorem bitvec_not_not_and_eq_or_not {w : Nat} (x y : BitVec w) :
    ~~~(~~~x &&& y) = x ||| ~~~y := by
  ext i
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or]
  cases x[i] <;> cases y[i] <;> decide

public theorem not_not_and_refines_or_not (w : Nat) (x y : LLVM.Int w) :
    LLVM.Int.xor
        (LLVM.Int.and (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) y)
        (.val (BitVec.ofInt w (-1))) ⊒
      LLVM.Int.or x (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))) false := by
  cases x <;> cases y <;> simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  simp only [BitVec.xor_allOnes]
  rw [bitvec_not_not_and_eq_or_not]
  exact isRefinedBy_refl _

public theorem bitvec_not_not_or_eq_and_not {w : Nat} (x y : BitVec w) :
    ~~~(~~~x ||| y) = x &&& ~~~y := by
  ext i
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or]
  cases x[i] <;> cases y[i] <;> decide

public theorem not_not_or_refines_and_not (w : Nat) (x y : LLVM.Int w)
    (disjoint : Bool) :
    LLVM.Int.xor
        (LLVM.Int.or (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) y disjoint)
        (.val (BitVec.ofInt w (-1))) ⊒
      LLVM.Int.and x (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))) := by
  apply isRefinedBy_trans (xor_refine_mono w
    (or_flags_refine w (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) y disjoint)
    (isRefinedBy_refl _))
  cases x <;> cases y <;> simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  simp only [BitVec.xor_allOnes]
  rw [bitvec_not_not_or_eq_and_not]
  exact isRefinedBy_refl _

public theorem bitvec_or_xor_not_and_eq_not_xor {w : Nat} (a b : BitVec w) :
    (a ||| b) ^^^ ~~~(a &&& b) = ~~~(a ^^^ b) := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not,
    BitVec.getElem_or]
  cases a[i] <;> cases b[i] <;> decide

public theorem or_xor_not_and_refines_not_xor (w : Nat) (a b : LLVM.Int w)
    (disjoint : Bool) :
    LLVM.Int.xor (LLVM.Int.or a b disjoint)
        (LLVM.Int.xor (LLVM.Int.and a b) (.val (BitVec.ofInt w (-1)))) ⊒
      LLVM.Int.xor (LLVM.Int.xor a b) (.val (BitVec.ofInt w (-1))) := by
  apply isRefinedBy_trans (xor_refine_mono w (or_flags_refine w a b disjoint)
    (isRefinedBy_refl _))
  cases a <;> cases b <;> simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  simp only [BitVec.xor_allOnes]
  rw [bitvec_or_xor_not_and_eq_not_xor]
  exact isRefinedBy_refl _

public theorem bitvec_and_xor_not_or_eq_not_xor {w : Nat} (a b : BitVec w) :
    (a &&& b) ^^^ ~~~(a ||| b) = ~~~(a ^^^ b) := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not,
    BitVec.getElem_or]
  cases a[i] <;> cases b[i] <;> decide

public theorem and_xor_not_or_refines_not_xor (w : Nat) (a b : LLVM.Int w)
    (disjoint : Bool) :
    LLVM.Int.xor (LLVM.Int.and a b)
        (LLVM.Int.xor (LLVM.Int.or a b disjoint) (.val (BitVec.ofInt w (-1)))) ⊒
      LLVM.Int.xor (LLVM.Int.xor a b) (.val (BitVec.ofInt w (-1))) := by
  apply isRefinedBy_trans (xor_refine_mono w (isRefinedBy_refl _)
    (xor_refine_mono w (or_flags_refine w a b disjoint) (isRefinedBy_refl _)))
  cases a <;> cases b <;> simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  simp only [BitVec.xor_allOnes]
  rw [bitvec_and_xor_not_or_eq_not_xor]
  exact isRefinedBy_refl _

end Veir.Passes.InstCombineLLVM
