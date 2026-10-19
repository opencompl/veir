import Veir.Passes.ArithCanonicalize.DivisionSupport

set_option linter.unusedSimpArgs false

namespace Veir.ArithCanonicalize

open Veir Veir.Data

theorem sceil_one_refines (w : Nat) (x : LLVM.Int w)
    (hdiv : LLVM.Int.isSignedDivisionUB x (.val (BitVec.ofInt w 1)) = false) :
    RuntimeValue.int w (sceilResult x (.val (BitVec.ofInt w 1))) ⊒ .int w x := by
  cases x with
  | poison =>
    simp [RuntimeValue.isRefinedBy, isRefinedBy, sceilResult,
      LLVM.Int.select, LLVM.Int.icmp, LLVM.Int.mul, LLVM.Int.sdiv,
      LLVM.Int.and, LLVM.Int.add, LLVM.IntPred.eval, Id.run]
  | val a =>
    simp [LLVM.Int.isSignedDivisionUB] at hdiv
    have hsafe : ¬(w = 0 ∨ a = BitVec.intMin w ∧ (1#w : BitVec w) = -1#w) := by
      rcases hdiv with ⟨hw, hnot⟩
      exact not_or.mpr ⟨hw, fun h => hnot h.2 h.1⟩
    simp [RuntimeValue.isRefinedBy, isRefinedBy, sceilResult,
      LLVM.Int.select, LLVM.Int.icmp, LLVM.Int.mul, LLVM.Int.sdiv,
      LLVM.Int.and, LLVM.Int.add, LLVM.IntPred.eval, Id.run,
      BitVec.sdiv_one, hsafe]

theorem sceil_zero_refines (w : Nat) (x : LLVM.Int w)
    (hdiv : LLVM.Int.isSignedDivisionUB (.val 0) x = false) :
    RuntimeValue.int w (sceilResult (.val 0) x) ⊒ .int w (.val 0) := by
  cases x with
  | poison => simp [LLVM.Int.isSignedDivisionUB] at hdiv
  | val b =>
    simp [LLVM.Int.isSignedDivisionUB] at hdiv
    have hs : ¬(0#w = BitVec.intMin w ∧ b = -1#w) := by
      exact fun ⟨h0,h1⟩ => hdiv.2 h1 h0
    have hb : b ≠ 0#w := by
      exact hdiv.1
    simp [RuntimeValue.isRefinedBy, isRefinedBy, sceilResult,
      LLVM.Int.select, LLVM.Int.icmp, LLVM.Int.mul, LLVM.Int.sdiv,
      LLVM.Int.and, LLVM.Int.add, LLVM.IntPred.eval, Id.run, hb, hs]

theorem sceil_self_refines (w : Nat) (x : LLVM.Int w)
    (hdiv : LLVM.Int.isSignedDivisionUB x x = false) :
    RuntimeValue.int w (sceilResult x x) ⊒
      .int w (.val (BitVec.ofInt w 1)) := by
  cases x with
  | poison => simp [LLVM.Int.isSignedDivisionUB] at hdiv
  | val a =>
    simp [LLVM.Int.isSignedDivisionUB] at hdiv
    have ha : a ≠ 0#w := hdiv.1
    have hs : ¬(a = BitVec.intMin w ∧ a = -1#w) := by
      exact fun ⟨h0,h1⟩ => hdiv.2 h1 h0
    have hbeq : (a == 0#w) = false := by simpa [beq_iff_eq] using ha
    simp [RuntimeValue.isRefinedBy, isRefinedBy, sceilResult,
      LLVM.Int.select, LLVM.Int.icmp, LLVM.Int.mul, LLVM.Int.sdiv,
      LLVM.Int.and, LLVM.Int.add, LLVM.IntPred.eval, Id.run,
      hs, ha, hbeq, BitVec.sdiv_self]

theorem sfloor_one_refines (w : Nat) (x : LLVM.Int w)
    (hdiv : LLVM.Int.isSignedDivisionUB x (.val (BitVec.ofInt w 1)) = false) :
    RuntimeValue.int w (sfloorResult x (.val (BitVec.ofInt w 1))) ⊒ .int w x := by
  cases x with
  | poison =>
    simp [RuntimeValue.isRefinedBy, isRefinedBy, sfloorResult,
      LLVM.Int.select, LLVM.Int.icmp, LLVM.Int.mul, LLVM.Int.sdiv,
      LLVM.Int.and, LLVM.Int.add, LLVM.IntPred.eval, Id.run]
  | val a =>
    simp [LLVM.Int.isSignedDivisionUB] at hdiv
    have hsafe : ¬(w = 0 ∨ a = BitVec.intMin w ∧ (1#w : BitVec w) = -1#w) := by
      rcases hdiv with ⟨hw, hnot⟩
      exact not_or.mpr ⟨hw, fun h => hnot h.2 h.1⟩
    simp [RuntimeValue.isRefinedBy, isRefinedBy, sfloorResult,
      LLVM.Int.select, LLVM.Int.icmp, LLVM.Int.mul, LLVM.Int.sdiv,
      LLVM.Int.and, LLVM.Int.add, LLVM.IntPred.eval, Id.run,
      BitVec.sdiv_one, hsafe]

theorem sfloor_zero_refines (w : Nat) (x : LLVM.Int w)
    (hdiv : LLVM.Int.isSignedDivisionUB (.val 0) x = false) :
    RuntimeValue.int w (sfloorResult (.val 0) x) ⊒ .int w (.val 0) := by
  cases x with
  | poison => simp [LLVM.Int.isSignedDivisionUB] at hdiv
  | val b =>
    simp [LLVM.Int.isSignedDivisionUB] at hdiv
    have hs : ¬(0#w = BitVec.intMin w ∧ b = -1#w) := by
      exact fun ⟨h0,h1⟩ => hdiv.2 h1 h0
    have hb : b ≠ 0#w := by
      exact hdiv.1
    simp [RuntimeValue.isRefinedBy, isRefinedBy, sfloorResult,
      LLVM.Int.select, LLVM.Int.icmp, LLVM.Int.mul, LLVM.Int.sdiv,
      LLVM.Int.and, LLVM.Int.add, LLVM.IntPred.eval, Id.run, hb, hs]

theorem sfloor_self_refines (w : Nat) (x : LLVM.Int w)
    (hdiv : LLVM.Int.isSignedDivisionUB x x = false) :
    RuntimeValue.int w (sfloorResult x x) ⊒
      .int w (.val (BitVec.ofInt w 1)) := by
  cases x with
  | poison => simp [LLVM.Int.isSignedDivisionUB] at hdiv
  | val a =>
    simp [LLVM.Int.isSignedDivisionUB] at hdiv
    have ha : a ≠ 0#w := hdiv.1
    have hs : ¬(a = BitVec.intMin w ∧ a = -1#w) := by
      exact fun ⟨h0,h1⟩ => hdiv.2 h1 h0
    have hbeq : (a == 0#w) = false := by simpa [beq_iff_eq] using ha
    simp [RuntimeValue.isRefinedBy, isRefinedBy, sfloorResult,
      LLVM.Int.select, LLVM.Int.icmp, LLVM.Int.mul, LLVM.Int.sdiv,
      LLVM.Int.and, LLVM.Int.add, LLVM.IntPred.eval, Id.run,
      hs, ha, hbeq, BitVec.sdiv_self]

end Veir.ArithCanonicalize
