module

public import Veir.Passes.InstCombineLLVM.BitwiseSemantics
import all Veir.Data.LLVM.Int.Basic

namespace Veir.Passes.InstCombineLLVM

open Veir Veir.Data

public theorem llvm_add_comm_flags {w : Nat} (x y : LLVM.Int w) (nsw nuw : Bool) :
    LLVM.Int.add x y nsw nuw = LLVM.Int.add y x nsw nuw := by
  cases x <;> cases y <;>
    simp [LLVM.Int.add, Id.run, BitVec.add_comm, BitVec.saddOverflow_comm,
      BitVec.uaddOverflow_comm]

public theorem bitvec_not_neg_or {w : Nat} (x y : BitVec w) :
    ~~~ ((-x) ||| y) = (x - 1#w) &&& ~~~y := by
  rw [BitVec.not_or, BitVec.not_neg]

public theorem bitvec_not_add {w : Nat} (x c : BitVec w) :
    ~~~ (x + c) = ~~~c - x := by
  rw [BitVec.not_eq_neg_add, BitVec.neg_add, BitVec.not_eq_neg_add]
  simp only [BitVec.sub_eq_add_neg]
  ac_rfl

public theorem bitvec_not_sub {w : Nat} (x y : BitVec w) :
    ~~~ (x - y) = ~~~x + y := by
  rw [BitVec.not_eq_neg_add, BitVec.not_eq_neg_add]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg]
  ac_rfl

public theorem bitvec_add_one_not {w : Nat} (a b : BitVec w) :
    (a + 1#w) + ~~~b = a - b := by
  rw [BitVec.not_eq_neg_add]
  simp only [BitVec.sub_eq_add_neg]
  change (a + (1#w)) + (-b + (-1#w)) = a + -b
  calc
    (a + (1#w)) + (-b + (-1#w)) = a + (-b + ((1#w) + (-1#w))) := by ac_rfl
    _ = a + (-b + 0#w) := by
      rw [show (1#w) + (-1#w) = 0#w by
        rw [← BitVec.sub_eq_add_neg]
        exact BitVec.sub_self _]
    _ = a + -b := by rw [BitVec.add_zero]

public theorem bitvec_add_allones_sub {w : Nat} (x y : BitVec w) :
    (x + BitVec.ofInt w (-1)) - y =
      (y ^^^ BitVec.ofInt w (-1)) + x := by
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  rw [BitVec.xor_allOnes, ← BitVec.neg_one_eq_allOnes]
  rw [BitVec.not_eq_neg_add]
  simp only [BitVec.sub_eq_add_neg]
  ac_rfl

public theorem bitvec_sub_sub_constant {w : Nat} (x c c2 : BitVec w) :
    c - (c2 - x) = x + (c - c2) := by
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg]
  ac_rfl

public theorem bitvec_or_sub_self {w : Nat} (x y : BitVec w) :
    (x ||| y) - x = ~~~x &&& y := by
  have hor : x ||| y = x + (~~~x &&& y) := by
    rw [BitVec.add_eq_or_of_and_eq_zero]
    · ext i
      simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
      cases x[i] <;> cases y[i] <;> decide
    · ext i
      simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
      cases x[i] <;> cases y[i] <;> decide
  rw [hor, BitVec.add_comm]
  exact BitVec.add_sub_cancel _ _

public theorem bitvec_not_shared_and_xor_or {w : Nat} (a b d : BitVec w) :
    ~~~ ((a &&& b) ^^^ (a ||| d)) =
      (a &&& b) ||| ~~~(a ||| d) := by
  ext i
  simp only [BitVec.getElem_not, BitVec.getElem_xor, BitVec.getElem_and,
    BitVec.getElem_or]
  cases a[i] <;> cases b[i] <;> cases d[i] <;> decide

public theorem bitvec_masked_merge_not {w : Nat} (b x m : BitVec w) :
    b ^^^ ((b ^^^ x) &&& ~~~m) = ((b ^^^ x) &&& m) ^^^ x := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
  cases b[i] <;> cases x[i] <;> cases m[i] <;> decide

public theorem bitvec_ofInt_neg_sub_one_eq_not {w : Nat} (c : Int) :
    BitVec.ofInt w (-c - 1) = ~~~(BitVec.ofInt w c) := by
  rw [show -c - 1 = -c + -1 by omega, BitVec.ofInt_add, BitVec.ofInt_neg,
    BitVec.ofInt_neg]
  change -BitVec.ofInt w c + (-1#w) = ~~~(BitVec.ofInt w c)
  rw [BitVec.not_eq_neg_add, BitVec.sub_eq_add_neg]

private theorem notValue_eq_xor_allOnes {w : Nat} (x : BitVec w) :
    ~~~x = x ^^^ BitVec.ofInt w (-1) := by
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes, BitVec.xor_allOnes]

private theorem bitvec_not_neg_or_xor_form {w : Nat} (x y : BitVec w) :
    ((-x) ||| y) ^^^ BitVec.ofInt w (-1) =
      (x + BitVec.ofInt w (-1)) &&& (y ^^^ BitVec.ofInt w (-1)) := by
  rw [← notValue_eq_xor_allOnes, ← notValue_eq_xor_allOnes]
  rw [show BitVec.ofInt w (-1) = -1#w by
      rw [BitVec.ofInt_neg, BitVec.ofInt_ofNat],
    ← BitVec.sub_eq_add_neg]
  exact bitvec_not_neg_or x y

private theorem bitvec_not_add_xor_form {w : Nat} (x c : BitVec w) :
    (x + c) ^^^ BitVec.ofInt w (-1) =
      (c ^^^ BitVec.ofInt w (-1)) - x := by
  rw [← notValue_eq_xor_allOnes, ← notValue_eq_xor_allOnes]
  exact bitvec_not_add x c

private theorem bitvec_not_sub_xor_form {w : Nat} (x y : BitVec w) :
    (x - y) ^^^ BitVec.ofInt w (-1) =
      (x ^^^ BitVec.ofInt w (-1)) + y := by
  rw [← notValue_eq_xor_allOnes, ← notValue_eq_xor_allOnes]
  exact bitvec_not_sub x y

private theorem bitvec_add_one_xor_allones {w : Nat} (a b : BitVec w) :
    (a + 1#w) + (b ^^^ BitVec.ofInt w (-1)) = a - b := by
  rw [← notValue_eq_xor_allOnes]
  exact bitvec_add_one_not a b

private theorem bitvec_not_shared_and_xor_or_xor_form {w : Nat}
    (a b d : BitVec w) :
    ((a &&& b) ^^^ (a ||| d)) ^^^ BitVec.ofInt w (-1) =
      (a &&& b) ||| ((a ||| d) ^^^ BitVec.ofInt w (-1)) := by
  rw [← notValue_eq_xor_allOnes, ← notValue_eq_xor_allOnes]
  exact bitvec_not_shared_and_xor_or a b d

public theorem not_neg_or_refines_dec_and_not (w : Nat) (x y : LLVM.Int w)
    (negNsw negNuw disjoint : Bool) :
    LLVM.Int.xor
        (LLVM.Int.or
          (LLVM.Int.sub (.val (BitVec.ofInt w 0)) x negNsw negNuw) y disjoint)
        (.val (BitVec.ofInt w (-1))) ⊒
      LLVM.Int.and
        (LLVM.Int.add x (.val (BitVec.ofInt w (-1))))
        (LLVM.Int.xor y (.val (BitVec.ofInt w (-1))) ) := by
  apply isRefinedBy_trans (xor_refine_mono w
    (isRefinedBy_trans
      (or_refine_mono w disjoint
        (sub_flags_refine w (.val (BitVec.ofInt w 0)) x negNsw negNuw)
        (isRefinedBy_refl _))
      (or_flags_refine w (LLVM.Int.sub (.val (BitVec.ofInt w 0)) x) y disjoint))
    (isRefinedBy_refl _))
  cases x <;> cases y <;> simp [LLVM.Int.sub, LLVM.Int.add, LLVM.Int.or,
    LLVM.Int.xor, LLVM.Int.and, Id.run, bitvec_not_neg_or_xor_form]

public theorem not_or_neg_refines_dec_and_not (w : Nat) (x y : LLVM.Int w)
    (negNsw negNuw disjoint : Bool) :
    LLVM.Int.xor
        (LLVM.Int.or y
          (LLVM.Int.sub (.val (BitVec.ofInt w 0)) x negNsw negNuw) disjoint)
        (.val (BitVec.ofInt w (-1))) ⊒
      LLVM.Int.and
        (LLVM.Int.add x (.val (BitVec.ofInt w (-1))))
        (LLVM.Int.xor y (.val (BitVec.ofInt w (-1))) ) := by
  rw [llvm_or_comm y (LLVM.Int.sub (.val (BitVec.ofInt w 0)) x negNsw negNuw)]
  exact not_neg_or_refines_dec_and_not w x y negNsw negNuw disjoint

public theorem not_add_refines_not_constant_sub (w : Nat) (x : LLVM.Int w)
    (c : BitVec w) (addNsw addNuw : Bool) :
    LLVM.Int.xor (LLVM.Int.add x (.val c) addNsw addNuw)
        (.val (BitVec.ofInt w (-1))) ⊒
      LLVM.Int.sub (LLVM.Int.xor (.val c) (.val (BitVec.ofInt w (-1)))) x := by
  apply isRefinedBy_trans (xor_refine_mono w
    (add_flags_refine w x (.val c) addNsw addNuw) (isRefinedBy_refl _))
  cases x <;> simp [LLVM.Int.sub, LLVM.Int.add, LLVM.Int.xor, Id.run,
    bitvec_not_add_xor_form]

public theorem not_add_refines_folded_constant_sub (w : Nat) (x : LLVM.Int w)
    (c : Int) (addNsw addNuw : Bool) :
    LLVM.Int.xor (LLVM.Int.add x (.val (BitVec.ofInt w c)) addNsw addNuw)
        (.val (BitVec.ofInt w (-1))) ⊒
      LLVM.Int.sub (.val (BitVec.ofInt w (-c - 1))) x := by
  rw [bitvec_ofInt_neg_sub_one_eq_not]
  rw [notValue_eq_xor_allOnes]
  exact not_add_refines_not_constant_sub w x (BitVec.ofInt w c) addNsw addNuw

public theorem not_sub_refines_not_add (w : Nat) (x y : LLVM.Int w)
    (subNsw subNuw : Bool) :
    LLVM.Int.xor (LLVM.Int.sub x y subNsw subNuw)
        (.val (BitVec.ofInt w (-1))) ⊒
      LLVM.Int.add (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) y := by
  apply isRefinedBy_trans (xor_refine_mono w
    (sub_flags_refine w x y subNsw subNuw) (isRefinedBy_refl _))
  cases x <;> cases y <;> simp [LLVM.Int.sub, LLVM.Int.add, LLVM.Int.xor, Id.run,
    bitvec_not_sub_xor_form]

public theorem add_one_not_refines_sub (w : Nat) (a b : LLVM.Int w)
    (innerNsw innerNuw outerNsw outerNuw : Bool) :
    LLVM.Int.add (LLVM.Int.add a (.val (BitVec.ofInt w 1)) innerNsw innerNuw)
        (LLVM.Int.xor b (.val (BitVec.ofInt w (-1)))) outerNsw outerNuw ⊒
      LLVM.Int.sub a b := by
  apply isRefinedBy_trans (add_flags_refine w _ _ outerNsw outerNuw)
  apply isRefinedBy_trans (add_refine_mono w
    (add_flags_refine w a (.val (BitVec.ofInt w 1)) innerNsw innerNuw)
    (isRefinedBy_refl _))
  cases a <;> cases b <;> simp [LLVM.Int.sub, LLVM.Int.add, LLVM.Int.xor, Id.run,
    bitvec_add_one_xor_allones]

private theorem bitvec_not_add_one_xor_allones {w : Nat} (a b : BitVec w) :
    (b ^^^ BitVec.ofInt w (-1)) + a + 1#w = a - b := by
  rw [BitVec.add_comm (b ^^^ BitVec.ofInt w (-1)) a]
  rw [BitVec.add_assoc, BitVec.add_comm (b ^^^ BitVec.ofInt w (-1)) (1#w),
    ← BitVec.add_assoc]
  exact bitvec_add_one_xor_allones a b

public theorem not_add_one_refines_sub (w : Nat) (a b : LLVM.Int w)
    (innerNsw innerNuw outerNsw outerNuw : Bool) :
    LLVM.Int.add
        (LLVM.Int.add (LLVM.Int.xor b (.val (BitVec.ofInt w (-1)))) a
          innerNsw innerNuw)
        (.val (BitVec.ofInt w 1)) outerNsw outerNuw ⊒
      LLVM.Int.sub a b := by
  apply isRefinedBy_trans (add_flags_refine w _ _ outerNsw outerNuw)
  apply isRefinedBy_trans (add_refine_mono w
    (add_flags_refine w (LLVM.Int.xor b (.val (BitVec.ofInt w (-1)))) a
      innerNsw innerNuw)
    (isRefinedBy_refl _))
  cases a <;> cases b <;> simp [LLVM.Int.sub, LLVM.Int.add, LLVM.Int.xor, Id.run,
    bitvec_not_add_one_xor_allones]

public theorem not_plus_add_one_refines_sub (w : Nat) (a b : LLVM.Int w)
    (innerNsw innerNuw outerNsw outerNuw : Bool) :
    LLVM.Int.add (LLVM.Int.xor b (.val (BitVec.ofInt w (-1))))
        (LLVM.Int.add a (.val (BitVec.ofInt w 1)) innerNsw innerNuw)
        outerNsw outerNuw ⊒
      LLVM.Int.sub a b := by
  rw [llvm_add_comm_flags (LLVM.Int.xor b (.val (BitVec.ofInt w (-1))))]
  exact add_one_not_refines_sub w a b innerNsw innerNuw outerNsw outerNuw

public theorem add_not_one_refines_sub (w : Nat) (a b : LLVM.Int w)
    (innerNsw innerNuw outerNsw outerNuw : Bool) :
    LLVM.Int.add
        (LLVM.Int.add a (LLVM.Int.xor b (.val (BitVec.ofInt w (-1))))
          innerNsw innerNuw)
        (.val (BitVec.ofInt w 1)) outerNsw outerNuw ⊒
      LLVM.Int.sub a b := by
  rw [llvm_add_comm_flags a (LLVM.Int.xor b (.val (BitVec.ofInt w (-1))))]
  exact not_add_one_refines_sub w a b innerNsw innerNuw outerNsw outerNuw

public theorem sub_add_allones_refines_not_add (w : Nat) (x y : LLVM.Int w)
    (addNsw addNuw subNsw subNuw : Bool) :
    LLVM.Int.sub
        (LLVM.Int.add x (.val (BitVec.ofInt w (-1))) addNsw addNuw) y
        subNsw subNuw ⊒
      LLVM.Int.add (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))) x := by
  apply isRefinedBy_trans (sub_flags_refine w _ y subNsw subNuw)
  apply isRefinedBy_trans (sub_refine_mono w
    (add_flags_refine w x (.val (BitVec.ofInt w (-1))) addNsw addNuw)
    (isRefinedBy_refl _))
  cases x <;> cases y <;> simp [LLVM.Int.sub, LLVM.Int.add, LLVM.Int.xor, Id.run,
    bitvec_add_allones_sub]

public theorem sub_sub_constants_refine (w : Nat) (x : LLVM.Int w) (c c2 : BitVec w)
    (innerNsw innerNuw outerNsw outerNuw : Bool) :
    LLVM.Int.sub (.val c) (LLVM.Int.sub (.val c2) x innerNsw innerNuw)
        outerNsw outerNuw ⊒
      LLVM.Int.add x (.val (c - c2)) := by
  apply isRefinedBy_trans (sub_flags_refine w _ _ outerNsw outerNuw)
  apply isRefinedBy_trans (sub_refine_mono w (isRefinedBy_refl _)
    (sub_flags_refine w (.val c2) x innerNsw innerNuw))
  cases x <;> simp [LLVM.Int.sub, LLVM.Int.add, Id.run, bitvec_sub_sub_constant]

public theorem sub_or_self_refines_and_not (w : Nat) (x y : LLVM.Int w)
    (disjoint subNsw subNuw : Bool) :
    LLVM.Int.sub (LLVM.Int.or x y disjoint) x subNsw subNuw ⊒
      LLVM.Int.and (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) y := by
  apply isRefinedBy_trans (sub_flags_refine w _ x subNsw subNuw)
  apply isRefinedBy_trans (sub_refine_mono w (or_flags_refine w x y disjoint)
    (isRefinedBy_refl _))
  cases x <;> cases y <;> simp [LLVM.Int.sub, LLVM.Int.or, LLVM.Int.and, LLVM.Int.xor,
    Id.run, bitvec_or_sub_self, notValue_eq_xor_allOnes]

public theorem bitvec_or_neg_add_eq_xor {w : Nat} (x c : BitVec w) :
    (x ||| -c) + c = (x ||| -c) ^^^ -c := by
  calc
    (x ||| -c) + c = (x ||| -c) - (-c) := by simp [BitVec.sub_eq_add_neg]
    _ = ~~~(-c) &&& x := by
      rw [BitVec.or_comm]
      exact bitvec_or_sub_self (-c) x
    _ = x &&& ~~~(-c) := BitVec.and_comm _ _
    _ = (-c) ^^^ (x ||| -c) := (bitvec_self_xor_or_eq_and_not x (-c)).symm
    _ = (x ||| -c) ^^^ -c := BitVec.xor_comm _ _

public theorem add_or_negated_constant_refines_xor (w : Nat)
    (x : LLVM.Int w) (c c2 : BitVec w) (h : c2 = -c)
    (disjoint nsw nuw : Bool) :
    LLVM.Int.add (LLVM.Int.or x (.val c2) disjoint) (.val c) nsw nuw ⊒
      LLVM.Int.xor (LLVM.Int.or x (.val c2) disjoint) (.val c2) := by
  apply isRefinedBy_trans (add_flags_refine w _ _ nsw nuw)
  subst c2
  cases x with
  | poison => simp [LLVM.Int.add, LLVM.Int.or, LLVM.Int.xor, Id.run]
  | val x =>
    cases disjoint
    · simp only [LLVM.Int.add, LLVM.Int.or, LLVM.Int.xor, Id.run, Bool.false_eq_true,
        false_and, ↓reduceIte]
      rw [bitvec_or_neg_add_eq_xor]
      exact isRefinedBy_refl _
    · by_cases hd : x &&& -c = 0
      · simp only [LLVM.Int.add, LLVM.Int.or, LLVM.Int.xor, Id.run, true_and, hd,
          ne_eq, not_true_eq_false, Bool.false_eq_true, false_and, ↓reduceIte]
        rw [bitvec_or_neg_add_eq_xor]
        exact isRefinedBy_refl _
      · simp only [LLVM.Int.add, LLVM.Int.or, LLVM.Int.xor, Id.run,
          Bool.false_eq_true, false_and, ↓reduceIte, true_and]
        rw [if_pos hd]
        exact poison_isRefinedBy _

public theorem not_shared_and_xor_or (w : Nat) (a b d : LLVM.Int w)
    (disjoint : Bool) :
    LLVM.Int.xor
        (LLVM.Int.xor (LLVM.Int.and a b) (LLVM.Int.or a d disjoint))
        (.val (BitVec.ofInt w (-1))) =
      LLVM.Int.or (LLVM.Int.and a b)
        (LLVM.Int.xor (LLVM.Int.or a d disjoint)
          (.val (BitVec.ofInt w (-1)))) := by
  cases a with
  | poison => simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run]
  | val a =>
    cases b with
    | poison => simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run]
    | val b =>
      cases d with
      | poison => simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run]
      | val d =>
        cases disjoint
        · simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run,
            bitvec_not_shared_and_xor_or_xor_form]
        · by_cases h : a &&& d = 0#w
          · simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run, h,
              bitvec_not_shared_and_xor_or_xor_form]
          · simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run, h]

public theorem not_shared_or_xor_and (w : Nat) (a b d : LLVM.Int w)
    (disjoint : Bool) :
    LLVM.Int.xor
        (LLVM.Int.xor (LLVM.Int.or a d disjoint) (LLVM.Int.and a b))
        (.val (BitVec.ofInt w (-1))) =
      LLVM.Int.or (LLVM.Int.and a b)
        (LLVM.Int.xor (LLVM.Int.or a d disjoint)
          (.val (BitVec.ofInt w (-1)))) := by
  rw [llvm_xor_comm (LLVM.Int.or a d disjoint) (LLVM.Int.and a b)]
  exact not_shared_and_xor_or w a b d disjoint

public theorem not_shared_and_xor_commuted_or (w : Nat) (a b d : LLVM.Int w)
    (disjoint : Bool) :
    LLVM.Int.xor
        (LLVM.Int.xor (LLVM.Int.and a b) (LLVM.Int.or d a disjoint))
        (.val (BitVec.ofInt w (-1))) =
      LLVM.Int.or (LLVM.Int.and a b)
        (LLVM.Int.xor (LLVM.Int.or d a disjoint)
          (.val (BitVec.ofInt w (-1)))) := by
  rw [llvm_or_comm d a]
  exact not_shared_and_xor_or w a b d disjoint

public theorem not_commuted_and_xor_or (w : Nat) (a b d : LLVM.Int w)
    (disjoint : Bool) :
    LLVM.Int.xor
        (LLVM.Int.xor (LLVM.Int.and b a) (LLVM.Int.or a d disjoint))
        (.val (BitVec.ofInt w (-1))) =
      LLVM.Int.or (LLVM.Int.and b a)
        (LLVM.Int.xor (LLVM.Int.or a d disjoint)
          (.val (BitVec.ofInt w (-1)))) := by
  rw [llvm_and_comm b a]
  exact not_shared_and_xor_or w a b d disjoint

public theorem not_commuted_and_xor_commuted_or (w : Nat)
    (a b d : LLVM.Int w) (disjoint : Bool) :
    LLVM.Int.xor
        (LLVM.Int.xor (LLVM.Int.and b a) (LLVM.Int.or d a disjoint))
        (.val (BitVec.ofInt w (-1))) =
      LLVM.Int.or (LLVM.Int.and b a)
        (LLVM.Int.xor (LLVM.Int.or d a disjoint)
          (.val (BitVec.ofInt w (-1)))) := by
  rw [llvm_and_comm b a, llvm_or_comm d a]
  exact not_shared_and_xor_or w a b d disjoint

public theorem not_commuted_or_xor_and (w : Nat) (a b d : LLVM.Int w)
    (disjoint : Bool) :
    LLVM.Int.xor
        (LLVM.Int.xor (LLVM.Int.or d a disjoint) (LLVM.Int.and a b))
        (.val (BitVec.ofInt w (-1))) =
      LLVM.Int.or (LLVM.Int.and a b)
        (LLVM.Int.xor (LLVM.Int.or d a disjoint)
          (.val (BitVec.ofInt w (-1)))) := by
  rw [llvm_or_comm d a]
  exact not_shared_or_xor_and w a b d disjoint

public theorem not_or_xor_commuted_and (w : Nat) (a b d : LLVM.Int w)
    (disjoint : Bool) :
    LLVM.Int.xor
        (LLVM.Int.xor (LLVM.Int.or a d disjoint) (LLVM.Int.and b a))
        (.val (BitVec.ofInt w (-1))) =
      LLVM.Int.or (LLVM.Int.and b a)
        (LLVM.Int.xor (LLVM.Int.or a d disjoint)
          (.val (BitVec.ofInt w (-1)))) := by
  rw [llvm_and_comm b a]
  exact not_shared_or_xor_and w a b d disjoint

public theorem not_commuted_or_xor_commuted_and (w : Nat)
    (a b d : LLVM.Int w) (disjoint : Bool) :
    LLVM.Int.xor
        (LLVM.Int.xor (LLVM.Int.or d a disjoint) (LLVM.Int.and b a))
        (.val (BitVec.ofInt w (-1))) =
      LLVM.Int.or (LLVM.Int.and b a)
        (LLVM.Int.xor (LLVM.Int.or d a disjoint)
          (.val (BitVec.ofInt w (-1)))) := by
  rw [llvm_and_comm b a, llvm_or_comm d a]
  exact not_shared_or_xor_and w a b d disjoint

public theorem masked_merge_not (w : Nat) (b x m : LLVM.Int w) :
    LLVM.Int.xor b
        (LLVM.Int.and (LLVM.Int.xor b x)
          (LLVM.Int.xor m (.val (BitVec.ofInt w (-1))))) =
      LLVM.Int.xor (LLVM.Int.and (LLVM.Int.xor b x) m) x := by
  cases b <;> cases x <;> cases m <;>
    simp only [LLVM.Int.xor, LLVM.Int.and, Id.run, pure, LLVM.Int.val.injEq]
  rw [← notValue_eq_xor_allOnes]
  exact bitvec_masked_merge_not _ _ _

public theorem masked_merge_not_permuted (w : Nat) (b x m : LLVM.Int w)
    (rootCommuted andCommuted deltaCommuted : Bool) :
    let delta := if deltaCommuted then LLVM.Int.xor x b else LLVM.Int.xor b x
    let notMask := LLVM.Int.xor m (.val (BitVec.ofInt w (-1)))
    let masked := if andCommuted then LLVM.Int.and notMask delta
      else LLVM.Int.and delta notMask
    let source := if rootCommuted then LLVM.Int.xor masked b
      else LLVM.Int.xor b masked
    source = LLVM.Int.xor (LLVM.Int.and delta m) x := by
  cases rootCommuted <;> cases andCommuted <;> cases deltaCommuted <;>
    simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals
    cases b <;> cases x <;> cases m <;>
      simp only [LLVM.Int.xor, LLVM.Int.and, Id.run, pure, LLVM.Int.val.injEq]
    rename_i b x m
    rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
      rw [BitVec.ofInt_neg]
      exact BitVec.neg_one_eq_allOnes, BitVec.xor_allOnes]
    ext i
    simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
    cases b[i] <;> cases x[i] <;> cases m[i] <;> decide

public theorem masked_merge_not_000 (w : Nat) (b x m : LLVM.Int w) :
    LLVM.Int.xor b (LLVM.Int.and (LLVM.Int.xor b x)
      (LLVM.Int.xor m (.val (BitVec.ofInt w (-1))))) =
      LLVM.Int.xor (LLVM.Int.and (LLVM.Int.xor b x) m) x := by
  simpa only [Bool.false_eq_true, ite_false] using
    (masked_merge_not_permuted w b x m false false false)

public theorem masked_merge_not_001 (w : Nat) (b x m : LLVM.Int w) :
    LLVM.Int.xor b (LLVM.Int.and (LLVM.Int.xor x b)
      (LLVM.Int.xor m (.val (BitVec.ofInt w (-1))))) =
      LLVM.Int.xor (LLVM.Int.and (LLVM.Int.xor x b) m) x := by
  simpa only [Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] using
    (masked_merge_not_permuted w b x m false false true)

public theorem masked_merge_not_010 (w : Nat) (b x m : LLVM.Int w) :
    LLVM.Int.xor b (LLVM.Int.and
      (LLVM.Int.xor m (.val (BitVec.ofInt w (-1)))) (LLVM.Int.xor b x)) =
      LLVM.Int.xor (LLVM.Int.and (LLVM.Int.xor b x) m) x := by
  simpa only [Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] using
    (masked_merge_not_permuted w b x m false true false)

public theorem masked_merge_not_011 (w : Nat) (b x m : LLVM.Int w) :
    LLVM.Int.xor b (LLVM.Int.and
      (LLVM.Int.xor m (.val (BitVec.ofInt w (-1)))) (LLVM.Int.xor x b)) =
      LLVM.Int.xor (LLVM.Int.and (LLVM.Int.xor x b) m) x := by
  simpa only [Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] using
    (masked_merge_not_permuted w b x m false true true)

public theorem masked_merge_not_100 (w : Nat) (b x m : LLVM.Int w) :
    LLVM.Int.xor (LLVM.Int.and (LLVM.Int.xor b x)
      (LLVM.Int.xor m (.val (BitVec.ofInt w (-1))))) b =
      LLVM.Int.xor (LLVM.Int.and (LLVM.Int.xor b x) m) x := by
  simpa only [Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] using
    (masked_merge_not_permuted w b x m true false false)

public theorem masked_merge_not_101 (w : Nat) (b x m : LLVM.Int w) :
    LLVM.Int.xor (LLVM.Int.and (LLVM.Int.xor x b)
      (LLVM.Int.xor m (.val (BitVec.ofInt w (-1))))) b =
      LLVM.Int.xor (LLVM.Int.and (LLVM.Int.xor x b) m) x := by
  simpa only [Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] using
    (masked_merge_not_permuted w b x m true false true)

public theorem masked_merge_not_110 (w : Nat) (b x m : LLVM.Int w) :
    LLVM.Int.xor (LLVM.Int.and
      (LLVM.Int.xor m (.val (BitVec.ofInt w (-1)))) (LLVM.Int.xor b x)) b =
      LLVM.Int.xor (LLVM.Int.and (LLVM.Int.xor b x) m) x := by
  simpa only [Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] using
    (masked_merge_not_permuted w b x m true true false)

public theorem masked_merge_not_111 (w : Nat) (b x m : LLVM.Int w) :
    LLVM.Int.xor (LLVM.Int.and
      (LLVM.Int.xor m (.val (BitVec.ofInt w (-1)))) (LLVM.Int.xor x b)) b =
      LLVM.Int.xor (LLVM.Int.and (LLVM.Int.xor x b) m) x := by
  simpa only [Bool.true_eq, ite_true] using
    (masked_merge_not_permuted w b x m true true true)

end Veir.Passes.InstCombineLLVM
