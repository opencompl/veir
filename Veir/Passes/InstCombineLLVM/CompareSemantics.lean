module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement

namespace Veir.Passes.InstCombineLLVM

open Veir Veir.Data Veir.Puddle

private theorem bitvec_beq_comm {w : Nat} (a b : BitVec w) : (a == b) = (b == a) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact eq_comm

public theorem llvm_icmp_eq_comm {w : Nat} (a b : LLVM.Int w) :
    LLVM.Int.icmp a b .eq = LLVM.Int.icmp b a .eq := by
  cases a <;> cases b <;>
    simp [LLVM.Int.icmp, LLVM.IntPred.eval, Id.run, bitvec_beq_comm]

public theorem llvm_icmp_ne_comm {w : Nat} (a b : LLVM.Int w) :
    LLVM.Int.icmp a b .ne = LLVM.Int.icmp b a .ne := by
  cases a <;> cases b <;>
    simp [LLVM.Int.icmp, LLVM.IntPred.eval, Id.run, bne_comm]

public theorem icmp_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .icmp : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .icmp) props #[IntegerType.mk 1 signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int 1 (LLVM.Int.icmp x y props.predicate) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', ne_eq, not_true_eq_false, ↓reduceDIte, LLVM.Int.cast_self,
    Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
    List.cons.injEq, and_true, TypeAttr.of_val]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · rintro rfl
    constructor
    · exact RuntimeValue.Conforms.integerType.mpr ⟨x.icmp y props.predicate, rfl⟩
    · intro memory
      simp [interpretOp', Llvm.interpretOp', TypeAttr.of_val]

public theorem icmp_and_ult_ne {w : Nat} (x y : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.and x y) x .ult =
      LLVM.Int.icmp (LLVM.Int.and x y) x .ne := by
  cases x with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.and, Id.run]
  | val x => cases y with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.and, Id.run]
    | val y =>
      simp only [LLVM.Int.icmp, LLVM.Int.and, LLVM.IntPred.eval, Id.run]
      congr 2
      change decide ((x &&& y).toNat < x.toNat) = decide (x &&& y ≠ x)
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      constructor
      · intro hlt heq
        have := congrArg BitVec.toNat heq
        omega
      · intro hne
        apply Nat.lt_of_le_of_ne
        · simpa only [BitVec.toNat_and] using (Nat.and_le_left : x.toNat &&& y.toNat ≤ x.toNat)
        · intro heq
          exact hne (BitVec.eq_of_toNat_eq heq)

public theorem icmp_and_uge_eq {w : Nat} (x y : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.and x y) x .uge =
      LLVM.Int.icmp (LLVM.Int.and x y) x .eq := by
  cases x with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.and, Id.run]
  | val x => cases y with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.and, Id.run]
    | val y =>
      simp only [LLVM.Int.icmp, LLVM.Int.and, LLVM.IntPred.eval, Id.run]
      congr 2
      change decide (x.toNat ≤ (x &&& y).toNat) = decide (x &&& y = x)
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      constructor
      · intro hle
        apply BitVec.eq_of_toNat_eq
        apply Nat.le_antisymm
        · simpa only [BitVec.toNat_and] using
            (Nat.and_le_left : x.toNat &&& y.toNat ≤ x.toNat)
        · exact hle
      · intro h
        rw [h]
        exact Nat.le_refl _

public theorem icmp_or_ule_eq {w : Nat} (x y : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.or x y false) x .ule =
      LLVM.Int.icmp (LLVM.Int.or x y false) x .eq := by
  cases x with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.or, Id.run]
  | val x => cases y with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.or, Id.run]
    | val y =>
      simp only [LLVM.Int.icmp, LLVM.Int.or, LLVM.IntPred.eval, Id.run,
        Bool.false_eq_true, false_and, if_false]
      congr 2
      change decide ((x ||| y).toNat ≤ x.toNat) = decide (x ||| y = x)
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      constructor
      · intro hle
        apply BitVec.eq_of_toNat_eq
        apply Nat.le_antisymm hle
        simpa only [BitVec.toNat_or] using
          (Nat.left_le_or : x.toNat ≤ x.toNat ||| y.toNat)
      · intro h
        rw [h]
        exact Nat.le_refl _

public theorem icmp_or_ugt_ne {w : Nat} (x y : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.or x y false) x .ugt =
      LLVM.Int.icmp (LLVM.Int.or x y false) x .ne := by
  cases x with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.or, Id.run]
  | val x => cases y with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.or, Id.run]
    | val y =>
      simp only [LLVM.Int.icmp, LLVM.Int.or, LLVM.IntPred.eval, Id.run,
        Bool.false_eq_true, false_and, ite_false]
      congr 2
      change decide (x.toNat < (x ||| y).toNat) = decide (x ||| y ≠ x)
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      constructor
      · intro hlt heq
        have := congrArg BitVec.toNat heq
        omega
      · intro hne
        apply Nat.lt_of_le_of_ne
        · simpa only [BitVec.toNat_or] using
            (Nat.left_le_or : x.toNat ≤ x.toNat ||| y.toNat)
        · intro heq
          exact hne (BitVec.eq_of_toNat_eq heq.symm)

public theorem icmp_and_ugt_ne_swapped {w : Nat} (x y : LLVM.Int w) :
    LLVM.Int.icmp x (LLVM.Int.and x y) .ugt =
      LLVM.Int.icmp x (LLVM.Int.and x y) .ne := by
  have h := icmp_and_ult_ne x y
  cases x <;> cases y <;>
    simpa [LLVM.Int.icmp, LLVM.IntPred.eval, Id.run, eq_comm, bne_comm] using h

public theorem icmp_and_ule_eq_swapped {w : Nat} (x y : LLVM.Int w) :
    LLVM.Int.icmp x (LLVM.Int.and x y) .ule =
      LLVM.Int.icmp x (LLVM.Int.and x y) .eq := by
  have h := icmp_and_uge_eq x y
  cases x <;> cases y <;>
    simpa [LLVM.Int.icmp, LLVM.IntPred.eval, Id.run, eq_comm, bitvec_beq_comm] using h

public theorem icmp_or_uge_eq_swapped {w : Nat} (x y : LLVM.Int w) :
    LLVM.Int.icmp x (LLVM.Int.or x y false) .uge =
      LLVM.Int.icmp x (LLVM.Int.or x y false) .eq := by
  have h := icmp_or_ule_eq x y
  cases x <;> cases y <;>
    simpa [LLVM.Int.icmp, LLVM.IntPred.eval, Id.run, eq_comm, bitvec_beq_comm] using h

public theorem icmp_or_ult_ne_swapped {w : Nat} (x y : LLVM.Int w) :
    LLVM.Int.icmp x (LLVM.Int.or x y false) .ult =
      LLVM.Int.icmp x (LLVM.Int.or x y false) .ne := by
  have h := icmp_or_ugt_ne x y
  cases x <;> cases y <;>
    simpa [LLVM.Int.icmp, LLVM.IntPred.eval, Id.run, eq_comm, bne_comm] using h

public theorem icmp_or_ule_eq_disjoint {w : Nat} (x y : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.or x y true) x .ule =
      LLVM.Int.icmp (LLVM.Int.or x y true) x .eq := by
  cases x with
  | poison => simp [LLVM.Int.or, LLVM.Int.icmp, Id.run]
  | val x => cases y with
    | poison => simp [LLVM.Int.or, LLVM.Int.icmp, Id.run]
    | val y =>
      have base := icmp_or_ule_eq (.val x) (.val y)
      by_cases h : x &&& y = (0#w)
      · simpa [LLVM.Int.or, Id.run, h] using base
      · simp [LLVM.Int.or, LLVM.Int.icmp, Id.run, h]

public theorem icmp_or_uge_eq_swapped_disjoint {w : Nat} (x y : LLVM.Int w) :
    LLVM.Int.icmp x (LLVM.Int.or x y true) .uge =
      LLVM.Int.icmp x (LLVM.Int.or x y true) .eq := by
  cases x with
  | poison => simp [LLVM.Int.or, LLVM.Int.icmp, Id.run]
  | val x => cases y with
    | poison => simp [LLVM.Int.or, LLVM.Int.icmp, Id.run]
    | val y =>
      have base := icmp_or_uge_eq_swapped (.val x) (.val y)
      by_cases h : x &&& y = (0#w)
      · simpa [LLVM.Int.or, Id.run, h] using base
      · simp [LLVM.Int.or, LLVM.Int.icmp, Id.run, h]

public theorem icmp_or_ugt_ne_disjoint {w : Nat} (x y : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.or x y true) x .ugt =
      LLVM.Int.icmp (LLVM.Int.or x y true) x .ne := by
  cases x with
  | poison => simp [LLVM.Int.or, LLVM.Int.icmp, Id.run]
  | val x => cases y with
    | poison => simp [LLVM.Int.or, LLVM.Int.icmp, Id.run]
    | val y =>
      have base := icmp_or_ugt_ne (.val x) (.val y)
      by_cases h : x &&& y = (0#w)
      · simpa [LLVM.Int.or, Id.run, h] using base
      · simp [LLVM.Int.or, LLVM.Int.icmp, Id.run, h]

public theorem icmp_or_ult_ne_swapped_disjoint {w : Nat} (x y : LLVM.Int w) :
    LLVM.Int.icmp x (LLVM.Int.or x y true) .ult =
      LLVM.Int.icmp x (LLVM.Int.or x y true) .ne := by
  cases x with
  | poison => simp [LLVM.Int.or, LLVM.Int.icmp, Id.run]
  | val x => cases y with
    | poison => simp [LLVM.Int.or, LLVM.Int.icmp, Id.run]
    | val y =>
      have base := icmp_or_ult_ne_swapped (.val x) (.val y)
      by_cases h : x &&& y = (0#w)
      · simpa [LLVM.Int.or, Id.run, h] using base
      · simp [LLVM.Int.or, LLVM.Int.icmp, Id.run, h]

public theorem icmp_xor_xor_ne {w : Nat} (a b d : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.xor a b) (LLVM.Int.xor a d) .ne ⊒
      LLVM.Int.icmp b d .ne := by
  cases a <;> cases b <;> cases d <;>
    simp [LLVM.Int.icmp, LLVM.Int.xor, LLVM.IntPred.eval, Id.run, isRefinedBy]
  apply congrArg BitVec.ofBool
  rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
  exact not_congr (BitVec.xor_right_inj _)

public theorem icmp_xor_xor_ne_right {w : Nat} (a b c : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.xor a b) (LLVM.Int.xor c a) .ne ⊒ LLVM.Int.icmp b c .ne := by
  rw [llvm_xor_comm c a]; exact icmp_xor_xor_ne a b c

public theorem icmp_xor_xor_ne_cross {w : Nat} (a b d : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.xor a b) (LLVM.Int.xor b d) .ne ⊒ LLVM.Int.icmp a d .ne := by
  rw [llvm_xor_comm a b]; exact icmp_xor_xor_ne b a d

public theorem icmp_xor_xor_ne_second {w : Nat} (a b c : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.xor a b) (LLVM.Int.xor c b) .ne ⊒ LLVM.Int.icmp a c .ne := by
  rw [llvm_xor_comm a b, llvm_xor_comm c b]; exact icmp_xor_xor_ne b a c

public theorem icmp_add_self_eq_zero {w : Nat} (a b : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.add a b false false) a .eq ⊒
      LLVM.Int.icmp b (.val 0) .eq := by
  cases a <;> cases b <;>
    simp [LLVM.Int.icmp, LLVM.Int.add, LLVM.IntPred.eval, Id.run, isRefinedBy]
  apply congrArg BitVec.ofBool
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact BitVec.add_right_eq_self

public theorem icmp_self_add_eq_zero {w : Nat} (a d : LLVM.Int w) :
    LLVM.Int.icmp a (LLVM.Int.add a d false false) .eq ⊒
      LLVM.Int.icmp (.val 0) d .eq := by
  cases a <;> cases d <;>
    simp [LLVM.Int.icmp, LLVM.Int.add, LLVM.IntPred.eval, Id.run, isRefinedBy]
  apply congrArg BitVec.ofBool
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  simp only [BitVec.self_eq_add_right, eq_comm]

public theorem icmp_add_add_eq {w : Nat} (a b d : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.add a b false false) (LLVM.Int.add a d false false) .eq ⊒
      LLVM.Int.icmp b d .eq := by
  cases a <;> cases b <;> cases d <;>
    simp [LLVM.Int.icmp, LLVM.Int.add, LLVM.IntPred.eval, Id.run, isRefinedBy]
  apply congrArg BitVec.ofBool
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact BitVec.add_right_inj _

public theorem icmp_sub_sub_eq {w : Nat} (a b c : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.sub a b false false) (LLVM.Int.sub c b false false) .eq ⊒
      LLVM.Int.icmp a c .eq := by
  cases a <;> cases b <;> cases c <;>
    simp [LLVM.Int.icmp, LLVM.Int.sub, LLVM.IntPred.eval, Id.run, isRefinedBy]
  apply congrArg BitVec.ofBool
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact BitVec.sub_left_inj _

public theorem icmp_xor_xor_eq {w : Nat} (a b d : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.xor a b) (LLVM.Int.xor a d) .eq ⊒
      LLVM.Int.icmp b d .eq := by
  cases a <;> cases b <;> cases d <;>
    simp [LLVM.Int.icmp, LLVM.Int.xor, LLVM.IntPred.eval, Id.run, isRefinedBy]
  apply congrArg BitVec.ofBool
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact BitVec.xor_right_inj _

public theorem icmp_xor_xor_eq_right {w : Nat} (a b c : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.xor a b) (LLVM.Int.xor c a) .eq ⊒
      LLVM.Int.icmp b c .eq := by
  rw [llvm_xor_comm c a]
  exact icmp_xor_xor_eq a b c

public theorem icmp_xor_xor_eq_cross {w : Nat} (a b d : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.xor a b) (LLVM.Int.xor b d) .eq ⊒
      LLVM.Int.icmp a d .eq := by
  rw [llvm_xor_comm a b]
  exact icmp_xor_xor_eq b a d

public theorem icmp_xor_xor_eq_second {w : Nat} (a b c : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.xor a b) (LLVM.Int.xor c b) .eq ⊒
      LLVM.Int.icmp a c .eq := by
  rw [llvm_xor_comm a b, llvm_xor_comm c b]
  exact icmp_xor_xor_eq b a c

public theorem icmp_add_self_eq_zero_flags {w : Nat} (a b : LLVM.Int w)
    (nsw nuw : Bool) :
    LLVM.Int.icmp (LLVM.Int.add a b nsw nuw) a .eq ⊒
      LLVM.Int.icmp b (.val 0) .eq := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
  | val a => cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
    | val b =>
      by_cases hs : nsw ∧ BitVec.saddOverflow a b
      · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hs]
      · by_cases hu : nuw ∧ BitVec.uaddOverflow a b
        · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hs, hu]
        · simp only [LLVM.Int.icmp, LLVM.Int.add, LLVM.IntPred.eval, Id.run, hs, hu,
            if_false, isRefinedBy]
          apply congrArg BitVec.ofBool
          rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
          exact BitVec.add_right_eq_self

public abbrev compareCancellationAllowed (pred : LLVM.IntPred) (nsw nuw : Bool) : Bool :=
  match pred with
  | .eq | .ne => true
  | .ugt | .uge | .ult | .ule => nuw
  | .sgt | .sge | .slt | .sle => nsw

public abbrev isUnsignedPredicate : LLVM.IntPred → Bool
  | .ugt | .uge | .ult | .ule => true
  | _ => false

public abbrev isSignedPredicate : LLVM.IntPred → Bool
  | .sgt | .sge | .slt | .sle => true
  | _ => false

public theorem icmp_add_self_pred_flags {w : Nat} (pred : LLVM.IntPred) (a b : LLVM.Int w)
    (nsw nuw : Bool) (hallow : compareCancellationAllowed pred nsw nuw = true) :
    LLVM.Int.icmp (LLVM.Int.add a b nsw nuw) a pred ⊒
      LLVM.Int.icmp b (.val 0) pred := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
  | val a => cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
    | val b =>
      by_cases hs : nsw ∧ BitVec.saddOverflow a b
      · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hs]
      · by_cases hu : nuw ∧ BitVec.uaddOverflow a b
        · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hs, hu]
        · simp only [LLVM.Int.icmp, LLVM.Int.add, Id.run, hs, hu, ite_false, isRefinedBy]
          apply congrArg BitVec.ofBool
          cases pred <;> simp only [compareCancellationAllowed] at hallow <;> simp only [LLVM.IntPred.eval]
          · rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
            exact BitVec.add_right_eq_self
          · rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
            exact not_congr BitVec.add_right_eq_self
          · rw [Bool.eq_iff_iff, BitVec.ult_iff_toNat_lt, BitVec.ult_iff_toNat_lt]
            have hno : ¬ BitVec.uaddOverflow a b = true := by simpa [hallow] using hu
            rw [BitVec.toNat_add_of_not_uaddOverflow hno]
            rw [show BitVec.toNat (0 : BitVec w) = 0 by rfl]
            omega

          · rw [Bool.eq_iff_iff, BitVec.ule_iff_toNat_le, BitVec.ule_iff_toNat_le]
            have hno : ¬ BitVec.uaddOverflow a b = true := by simpa [hallow] using hu
            rw [BitVec.toNat_add_of_not_uaddOverflow hno]
            rw [show BitVec.toNat (0 : BitVec w) = 0 by rfl]
            omega
          · rw [Bool.eq_iff_iff, BitVec.ult_iff_toNat_lt, BitVec.ult_iff_toNat_lt]
            have hno : ¬ BitVec.uaddOverflow a b = true := by simpa [hallow] using hu
            rw [BitVec.toNat_add_of_not_uaddOverflow hno]
            rw [show BitVec.toNat (0 : BitVec w) = 0 by rfl]
            omega
          · rw [Bool.eq_iff_iff, BitVec.ule_iff_toNat_le, BitVec.ule_iff_toNat_le]
            have hno : ¬ BitVec.uaddOverflow a b = true := by simpa [hallow] using hu
            rw [BitVec.toNat_add_of_not_uaddOverflow hno]
            rw [show BitVec.toNat (0 : BitVec w) = 0 by rfl]
            omega
          · rw [Bool.eq_iff_iff, BitVec.slt_iff_toInt_lt, BitVec.slt_iff_toInt_lt]
            have hno : ¬ BitVec.saddOverflow a b = true := by simpa [hallow] using hs
            rw [BitVec.toInt_add_of_not_saddOverflow hno]
            rw [show BitVec.toInt (0 : BitVec w) = 0 by simp [BitVec.toInt]]
            omega
          · rw [Bool.eq_iff_iff, BitVec.sle_iff_toInt_le, BitVec.sle_iff_toInt_le]
            have hno : ¬ BitVec.saddOverflow a b = true := by simpa [hallow] using hs
            rw [BitVec.toInt_add_of_not_saddOverflow hno]
            rw [show BitVec.toInt (0 : BitVec w) = 0 by simp [BitVec.toInt]]
            omega
          · rw [Bool.eq_iff_iff, BitVec.slt_iff_toInt_lt, BitVec.slt_iff_toInt_lt]
            have hno : ¬ BitVec.saddOverflow a b = true := by simpa [hallow] using hs
            rw [BitVec.toInt_add_of_not_saddOverflow hno]
            rw [show BitVec.toInt (0 : BitVec w) = 0 by simp [BitVec.toInt]]
            omega
          · rw [Bool.eq_iff_iff, BitVec.sle_iff_toInt_le, BitVec.sle_iff_toInt_le]
            have hno : ¬ BitVec.saddOverflow a b = true := by simpa [hallow] using hs
            rw [BitVec.toInt_add_of_not_saddOverflow hno]
            rw [show BitVec.toInt (0 : BitVec w) = 0 by simp [BitVec.toInt]]
            omega

public abbrev swapPredicate : LLVM.IntPred → LLVM.IntPred
  | .eq => .eq | .ne => .ne
  | .ugt => .ult | .uge => .ule | .ult => .ugt | .ule => .uge
  | .sgt => .slt | .sge => .sle | .slt => .sgt | .sle => .sge

public theorem llvm_icmp_swap {w : Nat} (a b : LLVM.Int w) (pred : LLVM.IntPred) :
    LLVM.Int.icmp a b pred = LLVM.Int.icmp b a (swapPredicate pred) := by
  cases a <;> cases b <;> cases pred <;>
    simp [LLVM.Int.icmp, LLVM.IntPred.eval, Id.run, BitVec.ult, BitVec.ule,
      BitVec.slt, BitVec.sle, bitvec_beq_comm, bne_comm]

public theorem cancellationAllowed_swap (pred : LLVM.IntPred) (nsw nuw : Bool) :
    compareCancellationAllowed (swapPredicate pred) nsw nuw =
      compareCancellationAllowed pred nsw nuw := by
  cases pred <;> rfl

public theorem icmp_self_add_pred_flags {w : Nat} (pred : LLVM.IntPred) (a d : LLVM.Int w)
    (nsw nuw : Bool) (hallow : compareCancellationAllowed pred nsw nuw = true) :
    LLVM.Int.icmp a (LLVM.Int.add a d nsw nuw) pred ⊒
      LLVM.Int.icmp (.val 0) d pred := by
  rw [llvm_icmp_swap a (LLVM.Int.add a d nsw nuw) pred,
    llvm_icmp_swap (.val 0) d pred]
  have hallow' : compareCancellationAllowed (swapPredicate pred) nsw nuw = true := by
    rw [cancellationAllowed_swap]
    exact hallow
  exact icmp_add_self_pred_flags (swapPredicate pred) a d nsw nuw hallow'

public theorem llvm_add_comm_flags {w : Nat} (a b : LLVM.Int w) (nsw nuw : Bool) :
    LLVM.Int.add a b nsw nuw = LLVM.Int.add b a nsw nuw := by
  cases a <;> cases b <;>
    simp [LLVM.Int.add, Id.run, BitVec.add_comm, BitVec.saddOverflow_comm,
      BitVec.uaddOverflow_comm]

public theorem icmp_add_self_ne_zero_flags {w : Nat} (a b : LLVM.Int w)
    (nsw nuw : Bool) :
    LLVM.Int.icmp (LLVM.Int.add a b nsw nuw) a .ne ⊒
      LLVM.Int.icmp b (.val 0) .ne := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
  | val a => cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
    | val b =>
      by_cases hs : nsw ∧ BitVec.saddOverflow a b
      · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hs]
      · by_cases hu : nuw ∧ BitVec.uaddOverflow a b
        · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hs, hu]
        · simp only [LLVM.Int.icmp, LLVM.Int.add, LLVM.IntPred.eval, Id.run, hs, hu,
            if_false, isRefinedBy]
          apply congrArg BitVec.ofBool
          rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
          exact not_congr BitVec.add_right_eq_self

public theorem icmp_self_add_eq_zero_flags {w : Nat} (a d : LLVM.Int w)
    (nsw nuw : Bool) :
    LLVM.Int.icmp a (LLVM.Int.add a d nsw nuw) .eq ⊒
      LLVM.Int.icmp (.val 0) d .eq := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
  | val a => cases d with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
    | val d =>
      by_cases hs : nsw ∧ BitVec.saddOverflow a d
      · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hs]
      · by_cases hu : nuw ∧ BitVec.uaddOverflow a d
        · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hs, hu]
        · simp only [LLVM.Int.icmp, LLVM.Int.add, LLVM.IntPred.eval, Id.run, hs, hu,
            if_false, isRefinedBy]
          apply congrArg BitVec.ofBool
          rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
          rw [BitVec.self_eq_add_right]
          exact eq_comm

public theorem icmp_self_add_ne_zero_flags {w : Nat} (a d : LLVM.Int w)
    (nsw nuw : Bool) :
    LLVM.Int.icmp a (LLVM.Int.add a d nsw nuw) .ne ⊒
      LLVM.Int.icmp (.val 0) d .ne := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
  | val a => cases d with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
    | val d =>
      by_cases hs : nsw ∧ BitVec.saddOverflow a d
      · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hs]
      · by_cases hu : nuw ∧ BitVec.uaddOverflow a d
        · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hs, hu]
        · simp only [LLVM.Int.icmp, LLVM.Int.add, LLVM.IntPred.eval, Id.run, hs, hu,
            if_false, isRefinedBy]
          apply congrArg BitVec.ofBool
          rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
          exact not_congr (by rw [BitVec.self_eq_add_right]; exact eq_comm)

public theorem icmp_add_add_pred_flags {w : Nat} (pred : LLVM.IntPred) (a b d : LLVM.Int w)
    (lnsw lnuw rnsw rnuw : Bool)
    (hl : compareCancellationAllowed pred lnsw lnuw = true)
    (hr : compareCancellationAllowed pred rnsw rnuw = true) :
    LLVM.Int.icmp (LLVM.Int.add a b lnsw lnuw) (LLVM.Int.add a d rnsw rnuw) pred ⊒
      LLVM.Int.icmp b d pred := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
  | val a => cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
    | val b => cases d with
      | poison =>
        cases h : LLVM.Int.add (.val a) (.val b) lnsw lnuw <;>
          simp [h, LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
      | val d =>
        by_cases hls : lnsw ∧ BitVec.saddOverflow a b
        · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hls]
        · by_cases hlu : lnuw ∧ BitVec.uaddOverflow a b
          · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hls, hlu]
          · by_cases hrs : rnsw ∧ BitVec.saddOverflow a d
            · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hls, hlu, hrs]
            · by_cases hru : rnuw ∧ BitVec.uaddOverflow a d
              · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hls, hlu, hrs, hru]
              · simp only [LLVM.Int.icmp, LLVM.Int.add, Id.run, hls, hlu, hrs, hru, ite_false, isRefinedBy]
                apply congrArg BitVec.ofBool
                cases pred <;> simp only [compareCancellationAllowed] at hl hr <;> simp only [LLVM.IntPred.eval]
                · rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
                  exact BitVec.add_right_inj _
                · rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
                  exact not_congr (BitVec.add_right_inj _)
                · rw [Bool.eq_iff_iff, BitVec.ult_iff_toNat_lt, BitVec.ult_iff_toNat_lt]
                  have hb : ¬ BitVec.uaddOverflow a b = true := by simpa [hl] using hlu
                  have hd : ¬ BitVec.uaddOverflow a d = true := by simpa [hr] using hru
                  rw [BitVec.toNat_add_of_not_uaddOverflow hb, BitVec.toNat_add_of_not_uaddOverflow hd]
                  omega
                · rw [Bool.eq_iff_iff, BitVec.ule_iff_toNat_le, BitVec.ule_iff_toNat_le]
                  have hb : ¬ BitVec.uaddOverflow a b = true := by simpa [hl] using hlu
                  have hd : ¬ BitVec.uaddOverflow a d = true := by simpa [hr] using hru
                  rw [BitVec.toNat_add_of_not_uaddOverflow hb, BitVec.toNat_add_of_not_uaddOverflow hd]
                  omega
                · rw [Bool.eq_iff_iff, BitVec.ult_iff_toNat_lt, BitVec.ult_iff_toNat_lt]
                  have hb : ¬ BitVec.uaddOverflow a b = true := by simpa [hl] using hlu
                  have hd : ¬ BitVec.uaddOverflow a d = true := by simpa [hr] using hru
                  rw [BitVec.toNat_add_of_not_uaddOverflow hb, BitVec.toNat_add_of_not_uaddOverflow hd]
                  omega
                · rw [Bool.eq_iff_iff, BitVec.ule_iff_toNat_le, BitVec.ule_iff_toNat_le]
                  have hb : ¬ BitVec.uaddOverflow a b = true := by simpa [hl] using hlu
                  have hd : ¬ BitVec.uaddOverflow a d = true := by simpa [hr] using hru
                  rw [BitVec.toNat_add_of_not_uaddOverflow hb, BitVec.toNat_add_of_not_uaddOverflow hd]
                  omega
                · rw [Bool.eq_iff_iff, BitVec.slt_iff_toInt_lt, BitVec.slt_iff_toInt_lt]
                  have hb : ¬ BitVec.saddOverflow a b = true := by simpa [hl] using hls
                  have hd : ¬ BitVec.saddOverflow a d = true := by simpa [hr] using hrs
                  rw [BitVec.toInt_add_of_not_saddOverflow hb, BitVec.toInt_add_of_not_saddOverflow hd]
                  omega
                · rw [Bool.eq_iff_iff, BitVec.sle_iff_toInt_le, BitVec.sle_iff_toInt_le]
                  have hb : ¬ BitVec.saddOverflow a b = true := by simpa [hl] using hls
                  have hd : ¬ BitVec.saddOverflow a d = true := by simpa [hr] using hrs
                  rw [BitVec.toInt_add_of_not_saddOverflow hb, BitVec.toInt_add_of_not_saddOverflow hd]
                  omega
                · rw [Bool.eq_iff_iff, BitVec.slt_iff_toInt_lt, BitVec.slt_iff_toInt_lt]
                  have hb : ¬ BitVec.saddOverflow a b = true := by simpa [hl] using hls
                  have hd : ¬ BitVec.saddOverflow a d = true := by simpa [hr] using hrs
                  rw [BitVec.toInt_add_of_not_saddOverflow hb, BitVec.toInt_add_of_not_saddOverflow hd]
                  omega
                · rw [Bool.eq_iff_iff, BitVec.sle_iff_toInt_le, BitVec.sle_iff_toInt_le]
                  have hb : ¬ BitVec.saddOverflow a b = true := by simpa [hl] using hls
                  have hd : ¬ BitVec.saddOverflow a d = true := by simpa [hr] using hrs
                  rw [BitVec.toInt_add_of_not_saddOverflow hb, BitVec.toInt_add_of_not_saddOverflow hd]
                  omega

public theorem icmp_add_add_eq_flags {w : Nat} (a b d : LLVM.Int w)
    (lnsw lnuw rnsw rnuw : Bool) :
    LLVM.Int.icmp (LLVM.Int.add a b lnsw lnuw) (LLVM.Int.add a d rnsw rnuw) .eq ⊒
      LLVM.Int.icmp b d .eq := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
  | val a => cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
    | val b => cases d with
      | poison =>
        cases h : LLVM.Int.add (.val a) (.val b) lnsw lnuw <;>
          simp [h, LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
      | val d =>
        by_cases hls : lnsw ∧ BitVec.saddOverflow a b
        · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hls]
        · by_cases hlu : lnuw ∧ BitVec.uaddOverflow a b
          · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hls, hlu]
          · by_cases hrs : rnsw ∧ BitVec.saddOverflow a d
            · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hls, hlu, hrs]
            · by_cases hru : rnuw ∧ BitVec.uaddOverflow a d
              · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hls, hlu, hrs, hru]
              · simpa [LLVM.Int.add, Id.run, hls, hlu, hrs, hru] using
                  icmp_add_add_eq (.val a) (.val b) (.val d)

public theorem icmp_add_add_ne_flags {w : Nat} (a b d : LLVM.Int w)
    (lnsw lnuw rnsw rnuw : Bool) :
    LLVM.Int.icmp (LLVM.Int.add a b lnsw lnuw) (LLVM.Int.add a d rnsw rnuw) .ne ⊒
      LLVM.Int.icmp b d .ne := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
  | val a => cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
    | val b => cases d with
      | poison =>
        cases h : LLVM.Int.add (.val a) (.val b) lnsw lnuw <;>
          simp [h, LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy]
      | val d =>
        by_cases hls : lnsw ∧ BitVec.saddOverflow a b
        · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hls]
        · by_cases hlu : lnuw ∧ BitVec.uaddOverflow a b
          · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hls, hlu]
          · by_cases hrs : rnsw ∧ BitVec.saddOverflow a d
            · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hls, hlu, hrs]
            · by_cases hru : rnuw ∧ BitVec.uaddOverflow a d
              · simp [LLVM.Int.icmp, LLVM.Int.add, Id.run, isRefinedBy, hls, hlu, hrs, hru]
              · simp only [LLVM.Int.icmp, LLVM.Int.add, LLVM.IntPred.eval, Id.run, hls,
                  hlu, hrs, hru, ite_false, isRefinedBy]
                apply congrArg BitVec.ofBool
                rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
                exact not_congr (BitVec.add_right_inj _)

public theorem icmp_sub_self_eq_zero_flags {w : Nat} (a b : LLVM.Int w)
    (nsw nuw : Bool) :
    LLVM.Int.icmp (LLVM.Int.sub a b nsw nuw) a .eq ⊒
      LLVM.Int.icmp (.val 0) b .eq := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy]
  | val a => cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy]
    | val b =>
      by_cases hs : nsw ∧ BitVec.ssubOverflow a b
      · simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy, hs]
      · by_cases hu : nuw ∧ BitVec.usubOverflow a b
        · simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy, hs, hu]
        · simp only [LLVM.Int.icmp, LLVM.Int.sub, LLVM.IntPred.eval, Id.run, hs, hu,
            ite_false, isRefinedBy]
          apply congrArg BitVec.ofBool
          rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
          rw [BitVec.sub_eq_iff_eq_add, BitVec.self_eq_add_right]
          exact eq_comm

public theorem icmp_sub_self_ne_zero_flags {w : Nat} (a b : LLVM.Int w)
    (nsw nuw : Bool) :
    LLVM.Int.icmp (LLVM.Int.sub a b nsw nuw) a .ne ⊒
      LLVM.Int.icmp (.val 0) b .ne := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy]
  | val a => cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy]
    | val b =>
      by_cases hs : nsw ∧ BitVec.ssubOverflow a b
      · simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy, hs]
      · by_cases hu : nuw ∧ BitVec.usubOverflow a b
        · simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy, hs, hu]
        · simp only [LLVM.Int.icmp, LLVM.Int.sub, LLVM.IntPred.eval, Id.run, hs, hu,
            ite_false, isRefinedBy]
          apply congrArg BitVec.ofBool
          rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
          exact not_congr (by
            rw [BitVec.sub_eq_iff_eq_add, BitVec.self_eq_add_right]
            exact eq_comm)

public theorem icmp_sub_sub_eq_flags {w : Nat} (a b c : LLVM.Int w)
    (lnsw lnuw rnsw rnuw : Bool) :
    LLVM.Int.icmp (LLVM.Int.sub a b lnsw lnuw) (LLVM.Int.sub c b rnsw rnuw) .eq ⊒
      LLVM.Int.icmp a c .eq := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy]
  | val a => cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy]
    | val b => cases c with
      | poison =>
        cases h : LLVM.Int.sub (.val a) (.val b) lnsw lnuw <;>
          simp [h, LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy]
      | val c =>
        by_cases hls : lnsw ∧ BitVec.ssubOverflow a b
        · simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy, hls]
        · by_cases hlu : lnuw ∧ BitVec.usubOverflow a b
          · simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy, hls, hlu]
          · by_cases hrs : rnsw ∧ BitVec.ssubOverflow c b
            · simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy, hls, hlu, hrs]
            · by_cases hru : rnuw ∧ BitVec.usubOverflow c b
              · simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy, hls, hlu, hrs, hru]
              · simpa [LLVM.Int.sub, Id.run, hls, hlu, hrs, hru] using
                  icmp_sub_sub_eq (.val a) (.val b) (.val c)

public theorem icmp_sub_sub_ne_flags {w : Nat} (a b c : LLVM.Int w)
    (lnsw lnuw rnsw rnuw : Bool) :
    LLVM.Int.icmp (LLVM.Int.sub a b lnsw lnuw) (LLVM.Int.sub c b rnsw rnuw) .ne ⊒
      LLVM.Int.icmp a c .ne := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy]
  | val a => cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy]
    | val b => cases c with
      | poison =>
        cases h : LLVM.Int.sub (.val a) (.val b) lnsw lnuw <;>
          simp [h, LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy]
      | val c =>
        by_cases hls : lnsw ∧ BitVec.ssubOverflow a b
        · simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy, hls]
        · by_cases hlu : lnuw ∧ BitVec.usubOverflow a b
          · simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy, hls, hlu]
          · by_cases hrs : rnsw ∧ BitVec.ssubOverflow c b
            · simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy, hls, hlu, hrs]
            · by_cases hru : rnuw ∧ BitVec.usubOverflow c b
              · simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy, hls, hlu, hrs, hru]
              · simp only [LLVM.Int.icmp, LLVM.Int.sub, LLVM.IntPred.eval, Id.run, hls,
                  hlu, hrs, hru, ite_false, isRefinedBy]
                apply congrArg BitVec.ofBool
                rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
                exact not_congr (BitVec.sub_left_inj _)

public theorem icmp_xor_self_eq_zero {w : Nat} (a b : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.xor a b) a .eq ⊒ LLVM.Int.icmp b (.val 0) .eq := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run, isRefinedBy]
  | val av => cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run, isRefinedBy]
    | val bv =>
      simp only [LLVM.Int.icmp, LLVM.Int.xor, LLVM.IntPred.eval, Id.run, isRefinedBy]
      apply congrArg BitVec.ofBool
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
      simpa [BitVec.xor_comm] using
        (BitVec.xor_right_inj (x := bv) (y := (0#w)) av)

public theorem icmp_xor_self_ne_zero {w : Nat} (a b : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.xor a b) a .ne ⊒ LLVM.Int.icmp b (.val 0) .ne := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run, isRefinedBy]
  | val av => cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run, isRefinedBy]
    | val bv =>
      simp only [LLVM.Int.icmp, LLVM.Int.xor, LLVM.IntPred.eval, Id.run, isRefinedBy]
      apply congrArg BitVec.ofBool
      rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
      exact not_congr (by simpa [BitVec.xor_comm] using
        (BitVec.xor_right_inj (x := bv) (y := (0#w)) av))

public theorem icmp_self_xor_eq_zero {w : Nat} (a b : LLVM.Int w) :
    LLVM.Int.icmp a (LLVM.Int.xor a b) .eq ⊒ LLVM.Int.icmp b (.val 0) .eq := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run, isRefinedBy]
  | val av => cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run, isRefinedBy]
    | val bv =>
      simpa [LLVM.Int.icmp, LLVM.Int.xor, LLVM.IntPred.eval, Id.run, isRefinedBy,
        eq_comm, bitvec_beq_comm] using icmp_xor_self_eq_zero (.val av) (.val bv)

public theorem icmp_self_xor_ne_zero {w : Nat} (a b : LLVM.Int w) :
    LLVM.Int.icmp a (LLVM.Int.xor a b) .ne ⊒ LLVM.Int.icmp b (.val 0) .ne := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run, isRefinedBy]
  | val av => cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run, isRefinedBy]
    | val bv =>
      simpa [LLVM.Int.icmp, LLVM.Int.xor, LLVM.IntPred.eval, Id.run, isRefinedBy,
        eq_comm, bne_comm] using icmp_xor_self_ne_zero (.val av) (.val bv)

public theorem icmp_xor_move_eq {w : Nat} (a b k : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.xor a k) b .eq ⊒
      LLVM.Int.icmp (LLVM.Int.xor a b) k .eq := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run, isRefinedBy]
  | val av => cases b with
    | poison => cases k <;> simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run, isRefinedBy]
    | val bv => cases k with
      | poison => simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run, isRefinedBy]
      | val kv =>
        simp only [LLVM.Int.icmp, LLVM.Int.xor, LLVM.IntPred.eval, Id.run, isRefinedBy]
        apply congrArg BitVec.ofBool
        rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
        constructor
        · intro h
          calc
            av ^^^ bv = av ^^^ (av ^^^ kv) := congrArg (fun x => av ^^^ x) h.symm
            _ = kv := by
              rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
        · intro h
          calc
            av ^^^ kv = av ^^^ (av ^^^ bv) := (congrArg (fun x => av ^^^ x) h).symm
            _ = bv := by
              rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

public theorem icmp_xor_move_ne {w : Nat} (a b k : LLVM.Int w) :
    LLVM.Int.icmp (LLVM.Int.xor a k) b .ne ⊒
      LLVM.Int.icmp (LLVM.Int.xor a b) k .ne := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run, isRefinedBy]
  | val av => cases b with
    | poison => cases k <;> simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run, isRefinedBy]
    | val bv => cases k with
      | poison => simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run, isRefinedBy]
      | val kv =>
        simp only [LLVM.Int.icmp, LLVM.Int.xor, LLVM.IntPred.eval, Id.run, isRefinedBy]
        apply congrArg BitVec.ofBool
        rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
        exact not_congr (by
          constructor
          · intro h
            calc
              av ^^^ bv = av ^^^ (av ^^^ kv) := congrArg (fun x => av ^^^ x) h.symm
              _ = kv := by
                rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
          · intro h
            calc
              av ^^^ kv = av ^^^ (av ^^^ bv) :=
                (congrArg (fun x => av ^^^ x) h).symm
              _ = bv := by
                rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor])


public theorem icmp_sub_self_pred_flags {w : Nat} (pred : LLVM.IntPred) (a b : LLVM.Int w)
    (nsw nuw : Bool) (hallow : compareCancellationAllowed pred nsw nuw = true) :
    LLVM.Int.icmp (LLVM.Int.sub a b nsw nuw) a pred ⊒
      LLVM.Int.icmp (.val 0) b pred := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy]
  | val a => cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy]
    | val b =>
      by_cases hs : nsw ∧ BitVec.ssubOverflow a b
      · simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy, hs]
      · by_cases hu : nuw ∧ BitVec.usubOverflow a b
        · simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy, hs, hu]
        · simp only [LLVM.Int.icmp, LLVM.Int.sub, Id.run, hs, hu, ite_false, isRefinedBy]
          apply congrArg BitVec.ofBool
          cases pred <;> simp only [compareCancellationAllowed] at hallow <;> simp only [LLVM.IntPred.eval]
          · rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
            rw [BitVec.sub_eq_iff_eq_add, BitVec.self_eq_add_right]
            exact eq_comm
          · rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
            exact not_congr (by rw [BitVec.sub_eq_iff_eq_add, BitVec.self_eq_add_right]; exact eq_comm)
          · rw [Bool.eq_iff_iff, BitVec.ult_iff_toNat_lt, BitVec.ult_iff_toNat_lt]
            have hno : ¬ BitVec.usubOverflow a b = true := by simpa [hallow] using hu
            rw [BitVec.toNat_sub_of_not_usubOverflow hno]
            rw [show BitVec.toNat (0 : BitVec w) = 0 by rfl]
            simp only [BitVec.usubOverflow, decide_eq_true_eq] at hno
            omega
          · rw [Bool.eq_iff_iff, BitVec.ule_iff_toNat_le, BitVec.ule_iff_toNat_le]
            have hno : ¬ BitVec.usubOverflow a b = true := by simpa [hallow] using hu
            rw [BitVec.toNat_sub_of_not_usubOverflow hno]
            rw [show BitVec.toNat (0 : BitVec w) = 0 by rfl]
            simp only [BitVec.usubOverflow, decide_eq_true_eq] at hno
            omega
          · rw [Bool.eq_iff_iff, BitVec.ult_iff_toNat_lt, BitVec.ult_iff_toNat_lt]
            have hno : ¬ BitVec.usubOverflow a b = true := by simpa [hallow] using hu
            rw [BitVec.toNat_sub_of_not_usubOverflow hno]
            rw [show BitVec.toNat (0 : BitVec w) = 0 by rfl]
            simp only [BitVec.usubOverflow, decide_eq_true_eq] at hno
            omega
          · rw [Bool.eq_iff_iff, BitVec.ule_iff_toNat_le, BitVec.ule_iff_toNat_le]
            have hno : ¬ BitVec.usubOverflow a b = true := by simpa [hallow] using hu
            rw [BitVec.toNat_sub_of_not_usubOverflow hno]
            rw [show BitVec.toNat (0 : BitVec w) = 0 by rfl]
            simp only [BitVec.usubOverflow, decide_eq_true_eq] at hno
            omega
          · rw [Bool.eq_iff_iff, BitVec.slt_iff_toInt_lt, BitVec.slt_iff_toInt_lt]
            have hno : ¬ BitVec.ssubOverflow a b = true := by simpa [hallow] using hs
            rw [BitVec.toInt_sub_of_not_ssubOverflow hno]
            rw [show BitVec.toInt (0 : BitVec w) = 0 by simp [BitVec.toInt]]
            omega
          · rw [Bool.eq_iff_iff, BitVec.sle_iff_toInt_le, BitVec.sle_iff_toInt_le]
            have hno : ¬ BitVec.ssubOverflow a b = true := by simpa [hallow] using hs
            rw [BitVec.toInt_sub_of_not_ssubOverflow hno]
            rw [show BitVec.toInt (0 : BitVec w) = 0 by simp [BitVec.toInt]]
            omega
          · rw [Bool.eq_iff_iff, BitVec.slt_iff_toInt_lt, BitVec.slt_iff_toInt_lt]
            have hno : ¬ BitVec.ssubOverflow a b = true := by simpa [hallow] using hs
            rw [BitVec.toInt_sub_of_not_ssubOverflow hno]
            rw [show BitVec.toInt (0 : BitVec w) = 0 by simp [BitVec.toInt]]
            omega
          · rw [Bool.eq_iff_iff, BitVec.sle_iff_toInt_le, BitVec.sle_iff_toInt_le]
            have hno : ¬ BitVec.ssubOverflow a b = true := by simpa [hallow] using hs
            rw [BitVec.toInt_sub_of_not_ssubOverflow hno]
            rw [show BitVec.toInt (0 : BitVec w) = 0 by simp [BitVec.toInt]]
            omega

public theorem icmp_sub_sub_pred_flags {w : Nat} (pred : LLVM.IntPred) (a b c : LLVM.Int w)
    (lnsw lnuw rnsw rnuw : Bool)
    (hl : compareCancellationAllowed pred lnsw lnuw = true)
    (hr : compareCancellationAllowed pred rnsw rnuw = true) :
    LLVM.Int.icmp (LLVM.Int.sub a b lnsw lnuw) (LLVM.Int.sub c b rnsw rnuw) pred ⊒
      LLVM.Int.icmp a c pred := by
  cases a with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy]
  | val a => cases b with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy]
    | val b => cases c with
      | poison =>
        cases h : LLVM.Int.sub (.val a) (.val b) lnsw lnuw <;>
          simp [h, LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy]
      | val c =>
        by_cases hls : lnsw ∧ BitVec.ssubOverflow a b
        · simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy, hls]
        · by_cases hlu : lnuw ∧ BitVec.usubOverflow a b
          · simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy, hls, hlu]
          · by_cases hrs : rnsw ∧ BitVec.ssubOverflow c b
            · simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy, hls, hlu, hrs]
            · by_cases hru : rnuw ∧ BitVec.usubOverflow c b
              · simp [LLVM.Int.icmp, LLVM.Int.sub, Id.run, isRefinedBy, hls, hlu, hrs, hru]
              · simp only [LLVM.Int.icmp, LLVM.Int.sub, Id.run, hls, hlu, hrs, hru, ite_false, isRefinedBy]
                apply congrArg BitVec.ofBool
                cases pred <;> simp only [compareCancellationAllowed] at hl hr <;> simp only [LLVM.IntPred.eval]
                · rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
                  exact BitVec.sub_left_inj b
                · rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
                  exact not_congr (BitVec.sub_left_inj b)
                · rw [Bool.eq_iff_iff, BitVec.ult_iff_toNat_lt, BitVec.ult_iff_toNat_lt]
                  have ha : ¬ BitVec.usubOverflow a b = true := by simpa [hl] using hlu
                  have hc : ¬ BitVec.usubOverflow c b = true := by simpa [hr] using hru
                  rw [BitVec.toNat_sub_of_not_usubOverflow ha, BitVec.toNat_sub_of_not_usubOverflow hc]
                  simp only [BitVec.usubOverflow, decide_eq_true_eq] at ha hc
                  omega
                · rw [Bool.eq_iff_iff, BitVec.ule_iff_toNat_le, BitVec.ule_iff_toNat_le]
                  have ha : ¬ BitVec.usubOverflow a b = true := by simpa [hl] using hlu
                  have hc : ¬ BitVec.usubOverflow c b = true := by simpa [hr] using hru
                  rw [BitVec.toNat_sub_of_not_usubOverflow ha, BitVec.toNat_sub_of_not_usubOverflow hc]
                  simp only [BitVec.usubOverflow, decide_eq_true_eq] at ha hc
                  omega
                · rw [Bool.eq_iff_iff, BitVec.ult_iff_toNat_lt, BitVec.ult_iff_toNat_lt]
                  have ha : ¬ BitVec.usubOverflow a b = true := by simpa [hl] using hlu
                  have hc : ¬ BitVec.usubOverflow c b = true := by simpa [hr] using hru
                  rw [BitVec.toNat_sub_of_not_usubOverflow ha, BitVec.toNat_sub_of_not_usubOverflow hc]
                  simp only [BitVec.usubOverflow, decide_eq_true_eq] at ha hc
                  omega
                · rw [Bool.eq_iff_iff, BitVec.ule_iff_toNat_le, BitVec.ule_iff_toNat_le]
                  have ha : ¬ BitVec.usubOverflow a b = true := by simpa [hl] using hlu
                  have hc : ¬ BitVec.usubOverflow c b = true := by simpa [hr] using hru
                  rw [BitVec.toNat_sub_of_not_usubOverflow ha, BitVec.toNat_sub_of_not_usubOverflow hc]
                  simp only [BitVec.usubOverflow, decide_eq_true_eq] at ha hc
                  omega
                · rw [Bool.eq_iff_iff, BitVec.slt_iff_toInt_lt, BitVec.slt_iff_toInt_lt]
                  have ha : ¬ BitVec.ssubOverflow a b = true := by simpa [hl] using hls
                  have hc : ¬ BitVec.ssubOverflow c b = true := by simpa [hr] using hrs
                  rw [BitVec.toInt_sub_of_not_ssubOverflow ha, BitVec.toInt_sub_of_not_ssubOverflow hc]
                  omega
                · rw [Bool.eq_iff_iff, BitVec.sle_iff_toInt_le, BitVec.sle_iff_toInt_le]
                  have ha : ¬ BitVec.ssubOverflow a b = true := by simpa [hl] using hls
                  have hc : ¬ BitVec.ssubOverflow c b = true := by simpa [hr] using hrs
                  rw [BitVec.toInt_sub_of_not_ssubOverflow ha, BitVec.toInt_sub_of_not_ssubOverflow hc]
                  omega
                · rw [Bool.eq_iff_iff, BitVec.slt_iff_toInt_lt, BitVec.slt_iff_toInt_lt]
                  have ha : ¬ BitVec.ssubOverflow a b = true := by simpa [hl] using hls
                  have hc : ¬ BitVec.ssubOverflow c b = true := by simpa [hr] using hrs
                  rw [BitVec.toInt_sub_of_not_ssubOverflow ha, BitVec.toInt_sub_of_not_ssubOverflow hc]
                  omega
                · rw [Bool.eq_iff_iff, BitVec.sle_iff_toInt_le, BitVec.sle_iff_toInt_le]
                  have ha : ¬ BitVec.ssubOverflow a b = true := by simpa [hl] using hls
                  have hc : ¬ BitVec.ssubOverflow c b = true := by simpa [hr] using hrs
                  rw [BitVec.toInt_sub_of_not_ssubOverflow ha, BitVec.toInt_sub_of_not_ssubOverflow hc]
                  omega


private theorem disjoint_no_uadd_overflow {w} (a b: BitVec w) (h:a&&&b=0) : a.uaddOverflow b = false := by
  have ht := BitVec.toNat_add_of_and_eq_zero h
  have hi := (a+b).isLt
  rw [ht] at hi
  simp [BitVec.uaddOverflow, show ¬ 2^w ≤ a.toNat+b.toNat by omega]

private theorem disjoint_no_sadd_overflow {w} (a b: BitVec w) (h:a&&&b=0) : a.saddOverflow b = false := by
  have hm := congrArg BitVec.msb h
  rw [BitVec.saddOverflow_eq, BitVec.add_eq_or_of_and_eq_zero a b h]
  simp only [BitVec.msb_and, BitVec.msb_or] at hm ⊢
  cases ha : a.msb <;> cases hb : b.msb <;> simp_all

public theorem disjoint_or_refines_add {w : Nat} (a b : LLVM.Int w) :
    LLVM.Int.or a b true ⊒ LLVM.Int.add a b true true := by
  cases a with
  | poison => simp [LLVM.Int.or, LLVM.Int.add, Id.run, isRefinedBy]
  | val a => cases b with
    | poison => simp [LLVM.Int.or, LLVM.Int.add, Id.run, isRefinedBy]
    | val b =>
      by_cases h : a &&& b = 0
      · have hu := disjoint_no_uadd_overflow a b h
        have hs := disjoint_no_sadd_overflow a b h
        simp [LLVM.Int.or, LLVM.Int.add, Id.run, isRefinedBy, h, hs, hu,
          ← BitVec.add_eq_or_of_and_eq_zero a b h]
      · simp [LLVM.Int.or, Id.run, isRefinedBy]
        split <;> simp_all

public theorem icmp_refine_mono {w : Nat} {a a' b b' : LLVM.Int w} (pred : LLVM.IntPred)
    (ha : a ⊒ a') (hb : b ⊒ b') : LLVM.Int.icmp a b pred ⊒ LLVM.Int.icmp a' b' pred := by
  cases a <;> cases a' <;> cases b <;> cases b' <;>
    simp_all [LLVM.Int.icmp, Id.run, isRefinedBy]

end Veir.Passes.InstCombineLLVM
