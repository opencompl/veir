import Veir.Dialects.Arith.Puddle

set_option linter.unusedSimpArgs false

namespace Veir.ArithCanonicalize

open Veir Veir.Puddle Veir.Data

def uceilResult {w : Nat} (a b : LLVM.Int w) : LLVM.Int w :=
  LLVM.Int.select (LLVM.Int.icmp a (.val 0) .eq) (.val 0)
    (LLVM.Int.add (LLVM.Int.udiv (LLVM.Int.sub a (.val 1)) b) (.val 1))

theorem ceildivui_iff {s : IntegerType.Signedness} (w : Nat)
    (a b : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .ceildivui) () #[IntegerType.mk w s]
      #[.int w a, .int w b] #[v] ↔
      LLVM.Int.isUnsignedDivisionUB b = false ∧
        v = .int w (uceilResult a b) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp', uceilResult,
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    grind [h .empty]
  · grind

theorem uceil_one_refines (w : Nat) (x : LLVM.Int w)
    (hdiv : LLVM.Int.isUnsignedDivisionUB (.val (BitVec.ofInt w 1)) = false) :
    RuntimeValue.int w (uceilResult x (.val (BitVec.ofInt w 1))) ⊒
      .int w x := by
  have hw : w ≠ 0 := by
    simpa [LLVM.Int.isUnsignedDivisionUB] using hdiv
  cases x with
  | poison =>
    simp [RuntimeValue.isRefinedBy, isRefinedBy, uceilResult,
      LLVM.Int.select, LLVM.Int.icmp, Id.run]
  | val a =>
    by_cases hz : a = 0#w
    · simp [RuntimeValue.isRefinedBy, isRefinedBy, uceilResult,
        LLVM.Int.select, LLVM.Int.icmp, LLVM.IntPred.eval,
        Id.run, hz]
    · simp [RuntimeValue.isRefinedBy, isRefinedBy, uceilResult,
        LLVM.Int.select, LLVM.Int.icmp, LLVM.Int.udiv, LLVM.Int.sub,
        LLVM.Int.add, LLVM.IntPred.eval, Id.run, pure,
        hw, hz, BitVec.udiv_one, BitVec.sub_add_cancel]
      have hbeq : (a == 0#w) = false := by simpa [beq_iff_eq] using hz
      simp [hbeq, isRefinedBy]

theorem uceil_zero_refines (w : Nat) (x : LLVM.Int w) :
    RuntimeValue.int w (uceilResult (.val 0) x) ⊒
      .int w (.val 0) := by
  simp [RuntimeValue.isRefinedBy, isRefinedBy, uceilResult,
    LLVM.Int.select, LLVM.Int.icmp, LLVM.IntPred.eval, Id.run]

private theorem sub_one_lt_self {w : Nat} (a : BitVec w) (ha : a ≠ 0#w) :
    a - 1#w < a := by
  have hw : 0 < w := by
    by_cases h : 0 < w
    · exact h
    · have hz : w = 0 := by omega
      subst w
      exact False.elim (ha BitVec.of_length_zero)
  have ha0 : a.toNat ≠ 0 := by
    intro h
    apply ha
    exact BitVec.eq_of_toNat_eq (by simpa using h)
  have hle : (1#w : BitVec w) ≤ a := by
    simp [BitVec.le_def, BitVec.toNat_one hw]
    omega
  rw [BitVec.lt_def, BitVec.toNat_sub_of_le hle, BitVec.toNat_one hw]
  omega

theorem uceil_self_refines (w : Nat) (x : LLVM.Int w)
    (h : LLVM.Int.isUnsignedDivisionUB x = false) :
    RuntimeValue.int w (uceilResult x x) ⊒
      .int w (.val (BitVec.ofInt w 1)) := by
  cases x with
  | poison => simp [LLVM.Int.isUnsignedDivisionUB] at h
  | val a =>
    have ha : a ≠ 0#w := by simpa [LLVM.Int.isUnsignedDivisionUB] using h
    have hlt := sub_one_lt_self a ha
    have hq : (a - 1#w) / a = 0#w :=
      BitVec.udiv_eq_zero_iff_eq_zero_or_lt.mpr (Or.inr hlt)
    have hbeq : (a == 0#w) = false := by simpa [beq_iff_eq] using ha
    simp [RuntimeValue.isRefinedBy, isRefinedBy, uceilResult,
      LLVM.Int.select, LLVM.Int.icmp, LLVM.IntPred.eval,
      LLVM.Int.udiv, LLVM.Int.sub, LLVM.Int.add, Id.run,
      hbeq, ha, hq]

def sceilResult {w : Nat} (a b : LLVM.Int w) : LLVM.Int w :=
  let zero : LLVM.Int w := .val 0
  let one : LLVM.Int w := .val 1
  let z := LLVM.Int.sdiv a b
  let notExact := LLVM.Int.icmp a (LLVM.Int.mul z b) .ne
  let signEqual := LLVM.Int.icmp (LLVM.Int.icmp a zero .slt)
    (LLVM.Int.icmp b zero .slt) .eq
  LLVM.Int.select (LLVM.Int.and notExact signEqual) (LLVM.Int.add z one) z

theorem ceildivsi_iff {s : IntegerType.Signedness} (w : Nat)
    (a b : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .ceildivsi) () #[IntegerType.mk w s]
      #[.int w a, .int w b] #[v] ↔
      LLVM.Int.isSignedDivisionUB a b = false ∧
        v = .int w (sceilResult a b) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp', sceilResult,
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    grind [h .empty]
  · grind

def sfloorResult {w : Nat} (a b : LLVM.Int w) : LLVM.Int w :=
  let zero : LLVM.Int w := .val 0
  let negOne : LLVM.Int w := .val (BitVec.allOnes w)
  let z := LLVM.Int.sdiv a b
  let notExact := LLVM.Int.icmp a (LLVM.Int.mul z b) .ne
  let signOpposite := LLVM.Int.icmp (LLVM.Int.icmp a zero .slt)
    (LLVM.Int.icmp b zero .slt) .ne
  LLVM.Int.select (LLVM.Int.and notExact signOpposite)
    (LLVM.Int.add z negOne) z

theorem floordivsi_iff {s : IntegerType.Signedness} (w : Nat)
    (a b : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .floordivsi) () #[IntegerType.mk w s]
      #[.int w a, .int w b] #[v] ↔
      LLVM.Int.isSignedDivisionUB a b = false ∧
        v = .int w (sfloorResult a b) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp', sfloorResult,
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    grind [h .empty]
  · grind

end Veir.ArithCanonicalize
