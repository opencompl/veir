import Veir.Passes.ArithCanonicalize.CastSupport

set_option linter.unusedSimpArgs false
namespace Veir.ArithCanonicalize.CmpCastSupport
open Veir Veir.Data
private theorem sext_inj (x y : BitVec a) (hab : a ≤ b) :
    (x.signExtend b = y.signExtend b) ↔ x = y := by
  constructor
  · intro h
    apply (BitVec.toInt_inj).mp
    have hh := congrArg BitVec.toInt h
    simpa only [BitVec.toInt_signExtend_of_le hab] using hh
  · intro h; rw [h]
private theorem zext_inj (x y : BitVec a) (hab : a ≤ b) :
    (x.zeroExtend b = y.zeroExtend b) ↔ x = y := by
  constructor
  · intro h
    apply (BitVec.toNat_inj).mp
    have hh := congrArg BitVec.toNat h
    simpa only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth_of_le hab] using hh
  · intro h; rw [h]
private theorem sext_beq (x y : BitVec a) (hab : a ≤ b) :
    (x.signExtend b == y.signExtend b) = (x == y) := by
  by_cases h : x = y
  · subst y; simp
  · have hn : x.signExtend b ≠ y.signExtend b := by
      intro hh
      exact h ((sext_inj x y hab).mp hh)
    have h1 : (x == y) = false := beq_eq_false_iff_ne.mpr h
    have h2 : (x.signExtend b == y.signExtend b) = false := beq_eq_false_iff_ne.mpr hn
    simp [h1, h2]
private theorem sext_bne (x y : BitVec a) (hab : a ≤ b) :
    (x.signExtend b != y.signExtend b) = (x != y) := by
  simp only [bne, sext_beq x y hab]
theorem icmp_sext_eq_ne (p : LLVM.IntPred) (h : p = .eq ∨ p = .ne) (x y : LLVM.Int a) (hab : a < b) :
    LLVM.Int.icmp (LLVM.Int.sext x b hab) (LLVM.Int.sext y b hab) p = LLVM.Int.icmp x y p := by
  rcases h with h | h <;> subst p
  all_goals cases x <;> cases y <;>
    simp [LLVM.Int.icmp, LLVM.Int.sext, LLVM.IntPred.eval, (sext_beq _ _ (Nat.le_of_lt hab)), (sext_bne _ _ (Nat.le_of_lt hab)), Id.run]

private theorem zext_beq (x y : BitVec a) (hab : a ≤ b) :
    (x.zeroExtend b == y.zeroExtend b) = (x == y) := by
  by_cases h : x = y
  · subst y; simp
  · have hn : x.zeroExtend b ≠ y.zeroExtend b := by
      intro hh
      exact h ((zext_inj x y hab).mp hh)
    have h1 : (x == y) = false := beq_eq_false_iff_ne.mpr h
    have h2 : (x.zeroExtend b == y.zeroExtend b) = false := beq_eq_false_iff_ne.mpr hn
    simp [h1, h2]
private theorem zext_bne (x y : BitVec a) (hab : a ≤ b) :
    (x.zeroExtend b != y.zeroExtend b) = (x != y) := by
  simp only [bne, zext_beq x y hab]
theorem icmp_zext_eq_ne_refines (p : LLVM.IntPred) (h : p = .eq ∨ p = .ne) (x y : LLVM.Int a)
    (hab : a < b) (nx ny : Bool) :
    RuntimeValue.int 1
      (LLVM.Int.icmp (LLVM.Int.zext x b nx hab) (LLVM.Int.zext y b ny hab) p) ⊒
      .int 1 (LLVM.Int.icmp x y p) := by
  rcases h with h | h <;> subst p
  all_goals
    cases x with
    | poison =>
      cases y <;> simp [LLVM.Int.icmp, LLVM.Int.zext,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val vx =>
      cases y with
      | poison =>
        by_cases hn : nx = true ∧ vx.msb = true <;>
          simp [LLVM.Int.icmp, LLVM.Int.zext, hn,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      | val vy =>
        by_cases hn : nx = true ∧ vx.msb = true
        · simp [LLVM.Int.icmp, LLVM.Int.zext, hn,
            RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
        · by_cases hm : ny = true ∧ vy.msb = true
          · simp [LLVM.Int.icmp, LLVM.Int.zext, hn, hm,
              RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
          · simp [LLVM.Int.icmp, LLVM.Int.zext, LLVM.IntPred.eval, hn, hm,
              (zext_beq vx vy (Nat.le_of_lt hab)),
              (zext_bne vx vy (Nat.le_of_lt hab)),
              RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
end Veir.ArithCanonicalize.CmpCastSupport
