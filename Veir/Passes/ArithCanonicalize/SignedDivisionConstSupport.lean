import Veir.Passes.ArithCanonicalize.DivisionSupport

namespace Veir.ArithCanonicalize

open Veir Veir.Data
theorem bool_bv_true (p : Bool) :
    (BitVec.ofBool p = 1#1) ↔ p = true := by cases p <;> decide
theorem bool_bv_beq (p q : Bool) :
    (BitVec.ofBool p == BitVec.ofBool q) = (p == q) := by
  cases p <;> cases q <;> decide
def sceilBits {w : Nat} (a b : BitVec w) : BitVec w :=
  let q := a.sdiv b
  if (a != q * b) && (a.slt 0#w == b.slt 0#w) then q + 1#w else q
theorem sceil_const (w : Nat) (a b : BitVec w)
    (hdiv : LLVM.Int.isSignedDivisionUB (.val a) (.val b) = false) :
    sceilResult (.val a) (.val b) = .val (sceilBits a b) := by
  simp [LLVM.Int.isSignedDivisionUB] at hdiv
  have hb : b ≠ 0#w := hdiv.1
  have hs : ¬(a = BitVec.intMin w ∧ b = -1#w) := by
    exact fun ⟨h0,h1⟩ => hdiv.2 h1 h0
  simp [sceilResult, sceilBits, LLVM.Int.select, LLVM.Int.icmp,
    LLVM.Int.mul, LLVM.Int.sdiv, LLVM.Int.and, LLVM.Int.add,
    LLVM.IntPred.eval, Id.run, hb, hs]
  simp only [bool_bv_beq, bool_bv_true, beq_iff_eq, bne_iff_ne,
    Bool.and_eq_true]
  simp only [ne_eq]
  split <;> simp_all

theorem bool_bv_bne (p q : Bool) :
    (BitVec.ofBool p != BitVec.ofBool q) = (p != q) := by
  cases p <;> cases q <;> decide
def sfloorBits {w : Nat} (a b : BitVec w) : BitVec w :=
  let q := a.sdiv b
  if (a != q * b) && (a.slt 0#w != b.slt 0#w) then q + BitVec.allOnes w else q
theorem sfloor_const (w : Nat) (a b : BitVec w)
    (hdiv : LLVM.Int.isSignedDivisionUB (.val a) (.val b) = false) :
    sfloorResult (.val a) (.val b) = .val (sfloorBits a b) := by
  simp [LLVM.Int.isSignedDivisionUB] at hdiv
  have hb : b ≠ 0#w := hdiv.1
  have hs : ¬(a = BitVec.intMin w ∧ b = -1#w) := by
    exact fun ⟨h0,h1⟩ => hdiv.2 h1 h0
  simp [sfloorResult, sfloorBits, LLVM.Int.select, LLVM.Int.icmp,
    LLVM.Int.mul, LLVM.Int.sdiv, LLVM.Int.and, LLVM.Int.add,
    LLVM.IntPred.eval, Id.run, hb, hs]
  simp only [bool_bv_bne, bool_bv_true, bne_iff_ne,
    Bool.and_eq_true]
  simp only [ne_eq]
  split <;> simp_all

theorem sceil_const_refines (w : Nat) (a b : BitVec w)
    (hdiv : LLVM.Int.isSignedDivisionUB (.val a) (.val b) = false) :
    RuntimeValue.int w (sceilResult (.val a) (.val b)) ⊒
      .int w (.val (sceilBits a b)) := by
  rw [sceil_const w a b hdiv]
  simp [RuntimeValue.isRefinedBy, isRefinedBy]

theorem sfloor_const_refines (w : Nat) (a b : BitVec w)
    (hdiv : LLVM.Int.isSignedDivisionUB (.val a) (.val b) = false) :
    RuntimeValue.int w (sfloorResult (.val a) (.val b)) ⊒
      .int w (.val (sfloorBits a b)) := by
  rw [sfloor_const w a b hdiv]
  simp [RuntimeValue.isRefinedBy, isRefinedBy]

end Veir.ArithCanonicalize
