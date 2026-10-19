import Veir.Dialects.Arith.Puddle

namespace Veir.ArithCanonicalize

open Veir Veir.Data

theorem sub_sub_target_nsw_safe (w : Nat) (a b : BitVec w)
    (h0 : ¬ BitVec.ssubOverflow a b)
    (h1 : ¬ BitVec.ssubOverflow (a - b) a) :
    ¬ BitVec.ssubOverflow (0#w) b := by
  have hinner := BitVec.toInt_sub_of_not_ssubOverflow h0
  simp only [BitVec.ssubOverflow] at h0 h1 ⊢
  rw [hinner] at h1
  simp at h0 h1 ⊢
  omega

theorem sub_sub_target_nuw_safe (w : Nat) (a b : BitVec w)
    (h0 : ¬ BitVec.usubOverflow a b)
    (h1 : ¬ BitVec.usubOverflow (a - b) a) :
    ¬ BitVec.usubOverflow (0#w) b := by
  have hinner := BitVec.toNat_sub_of_not_usubOverflow h0
  simp only [BitVec.usubOverflow] at h0 h1 ⊢
  rw [hinner] at h1
  simp at h0 h1 ⊢
  omega

private theorem sub_val_cases (w : Nat) (a b : BitVec w) (nsw nuw : Bool) :
    LLVM.Int.sub (.val a) (.val b) nsw nuw = .poison ∨
      LLVM.Int.sub (.val a) (.val b) nsw nuw = .val (a - b) := by
  simp [LLVM.Int.sub, Id.run, pure]
  split <;> simp_all [pure]

private theorem sub_val_nsw_safe (w : Nat) (a b : BitVec w)
    (nsw nuw : Bool) (v : BitVec w)
    (h : LLVM.Int.sub (.val a) (.val b) nsw nuw = .val v)
    (hf : nsw = true) : ¬ BitVec.ssubOverflow a b := by
  intro hover
  simp [LLVM.Int.sub, hf, hover, Id.run, pure] at h

private theorem sub_val_nuw_safe (w : Nat) (a b : BitVec w)
    (nsw nuw : Bool) (v : BitVec w)
    (h : LLVM.Int.sub (.val a) (.val b) nsw nuw = .val v)
    (hf : nuw = true) : ¬ BitVec.usubOverflow a b := by
  intro hover
  simp [LLVM.Int.sub, hf, hover, Id.run, pure] at h

private theorem sub_sub_bits (w : Nat) (a b : BitVec w) :
    (a - b) - a = 0#w - b := by
  calc
    (a - b) - a = -a + (a + -b) := by
      simp [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm]
    _ = (-a + a) + -b := by rw [BitVec.add_assoc]
    _ = 0#w - b := by simp [BitVec.add_left_neg, BitVec.sub_eq_add_neg]

theorem sub_sub_flagged_refines (w : Nat) (x y : LLVM.Int w)
    (innerNsw innerNuw outerNsw outerNuw : Bool) :
    RuntimeValue.int w
      (LLVM.Int.sub (LLVM.Int.sub x y innerNsw innerNuw) x outerNsw outerNuw) ⊒
      .int w (LLVM.Int.sub (.val 0) y
        (innerNsw && outerNsw) (innerNuw && outerNuw)) := by
  cases x with
  | poison => simp [RuntimeValue.isRefinedBy, LLVM.Int.sub, isRefinedBy, Id.run]
  | val a =>
    cases y with
    | poison => simp [RuntimeValue.isRefinedBy, LLVM.Int.sub, isRefinedBy, Id.run]
    | val b =>
      rcases sub_val_cases w a b innerNsw innerNuw with hi | hi
      · rw [hi]
        simp [RuntimeValue.isRefinedBy, LLVM.Int.sub, isRefinedBy, Id.run]
      · rw [hi]
        rcases sub_val_cases w (a - b) a outerNsw outerNuw with ho | ho
        · simp [ho, RuntimeValue.isRefinedBy, isRefinedBy]
        · rw [ho]
          have hs : ¬ ((innerNsw && outerNsw) = true ∧
              BitVec.ssubOverflow (0#w) b = true) := by
            rintro ⟨hf, hover⟩
            obtain ⟨fi, fo⟩ := Bool.and_eq_true_iff.mp hf
            have hsafe := sub_sub_target_nsw_safe w a b
              (sub_val_nsw_safe w a b innerNsw innerNuw (a - b) hi fi)
              (sub_val_nsw_safe w (a - b) a outerNsw outerNuw
                ((a - b) - a) ho fo)
            exact hsafe (by simpa using hover)
          have hu : ¬ ((innerNuw && outerNuw) = true ∧
              BitVec.usubOverflow (0#w) b = true) := by
            rintro ⟨hf, hover⟩
            obtain ⟨fi, fo⟩ := Bool.and_eq_true_iff.mp hf
            have hsafe := sub_sub_target_nuw_safe w a b
              (sub_val_nuw_safe w a b innerNsw innerNuw (a - b) hi fi)
              (sub_val_nuw_safe w (a - b) a outerNsw outerNuw
                ((a - b) - a) ho fo)
            exact hsafe (by simpa using hover)
          have ht : LLVM.Int.sub (.val 0) (.val b)
              (innerNsw && outerNsw) (innerNuw && outerNuw) =
              .val (0#w - b) := by
            simp only [Bool.and_eq_true_iff] at hs hu
            simp [LLVM.Int.sub, Id.run, hs, hu]
          rw [ht]
          simpa [RuntimeValue.isRefinedBy, isRefinedBy] using sub_sub_bits w a b

end Veir.ArithCanonicalize
