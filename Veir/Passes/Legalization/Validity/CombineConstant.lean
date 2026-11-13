module

import all Veir.Passes.Legalization.Validity.Common
import all Veir.Passes.Legalization.LegalizerHelper
import all Veir.Passes.Legalization.LegalizationArtifactCombiner
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
import all Veir.Passes.Legalization.CombinerHelper
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR.Properties
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.GMIR.Semantics
import all Veir.Dialects.GMIR_RISCV.OpInfo
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Init.Data.Array.Basic
import all Init.Data.Nat.Power2.Basic

import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.Tactic.BVDecide

/-! CTree validity of the gMIR combines that test or compute the value of a matched `g_constant`.

`matchConstant` requires the constant's attribute to have the type of its result, as the verifier
does, so the combines read the constant at the width it has: `normalizeConstants` splits its
properties and substitutes that type, which leaves each constant as `BitVec.ofInt w v` with the
matcher's predicate as a hypothesis on it. Each goal is then closed by a local lemma stated for an
arbitrary constant `c`, mostly in `Veir.Passes.Legalization.Proofs`; the lemmas that mention the
private `shiftAmount` of the gMIR semantics are here.

Two matchers also needed a typing condition: `select_into_binop_pattern` skips `i0`, where the
shift by the created `0` is out of range, and `matchFunnelShiftConstAmt` matches the result at the
type of the shifted value, since `funnel_shift_overshift_pattern` reduces the amount modulo the
result width while the funnel shift takes it modulo the width of its operands. -/

namespace Veir.Legalization.CTreeProofs

open Puddle
open Puddle.CTree
open _root_.CTree

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  GMIR.interpretOp' GMIR.interpretOpCTree GMIR_RISCV.interpretOp'

attribute [local simp] GMIR.isTerminator GMIR.getEffects GMIR_RISCV.base

attribute [local implicit_reducible] TypeAttr

/-- The predicates the combines test on a matched constant, read at the width of its result. -/
local macro "simpConstantPreds" : tactic => `(tactic|
  simp only [GMIRConstantProperties.bits, GMIRConstantProperties.isZero, GMIRConstantProperties.isOne,
    GMIRConstantProperties.isAllOnes, GMIRConstantProperties.isMinSigned, GMIRConstantProperties.neg,
    GMIRConstantProperties.isOffsetOf, GMIRConstantProperties.log2?, GMIRConstantProperties.ulog2?,
    GMIRConstantProperties.slog2?, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.or_eq_true] at *)

/-- Normalize the goals of a combine that matches constants: split each constant's properties and
substitute its type, which `matchConstant` equates to the result type, so that each constant is
`BitVec.ofInt w v` at its result width `w`. -/
macro "normalizeConstants" : tactic => `(tactic| (
  all_goals intros
  all_goals (casesLocalsOf GMIRConstantProperties IntegerAttr)
  all_goals casesIntegerTypes
  all_goals (try simp only [IntegerType.mk.injEq] at *)
  all_goals (try casesExistsAnd)
  all_goals (try subst_vars)
  all_goals (try simpConstantPreds)))

/-- Closes a hypothesis of a local correctness lemma: a predicate of the matcher, or a
comparison or constant arm that is zero or one. -/
macro "closeConstSide" : tactic => `(tactic| first
  | assumption
  | exact Data.LLVM.zext_i1_eq_poison_or_zero_or_one ‹_› _
  | exact Data.LLVM.icmp_eq_poison_or_zero_or_one _ _ _
  | exact Data.LLVM.boolArm_of_constant _ ‹_›
  | simp_all
  | omega)

/-- Closes a value goal with the first of the lemmas that applies. -/
syntax "closeConstWith" term,+ : tactic
macro_rules
  | `(tactic| closeConstWith $l) => `(tactic| (apply $l <;> closeConstSide))
  | `(tactic| closeConstWith $l, $ls,*) =>
    `(tactic| first | (apply $l <;> closeConstSide) | closeConstWith $ls,*)

/-- Prove the validity of a combine that matches constants, closing each value goal with one of the
local correctness lemmas, whose hypotheses on the constants are those of the matcher. -/
macro "proveConstValid" "using" ls:term,+ : tactic => `(tactic| (
  conv => arg 1; cbv
  simpPuddleValid
  simpLegalSemantics
  normalizeLegalValid
  normalizeConstants
  all_goals closeConstWith $ls,*))

/-- Normalize a combine whose types are `TypeAttr`s, as the funnel shifts: also split each type, so
that the type of the constant, which `matchConstant` equates, substitutes, and normalize again. -/
macro "normalizeTypedConstants" : tactic => `(tactic| (
  conv => arg 1; cbv
  simpPuddleValid
  simpLegalSemantics
  normalizeLegalValid
  normalizeConstants
  all_goals (casesLocalsOf Subtype)
  all_goals (try subst_vars)
  all_goals (try simp_all)
  normalizeLegalValid))

/-! ### Shifts by a matched zero

`shiftAmount` is private to the gMIR semantics, so these lemmas are stated here. -/

/-- A shift by a zero amount, in range at a positive width and out of range at width 0. -/
private theorem shiftAmount_zero {w v : Nat} (c : BitVec v) (hc : c = 0) :
    shiftAmount w (Data.LLVM.Int.val c) = .val (if 0 < w then 0#w else BitVec.allOnes w) := by
  subst hc; simp [shiftAmount]

private theorem id_pure {α : Type} (x : α) : (pure x : Id α) = x := rfl

/-- At a positive width, a shift by zero is in range. -/
private theorem zero_lt_width {w : Nat} (hw : 0 < w) : ¬ (0#w ≥ (w : BitVec w)) := by
  rw [ge_iff_le, BitVec.le_def, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt Nat.lt_two_pow_self]
  simp; omega

private theorem ofNat_self_ne_zero {w : Nat} (hw : 0 < w) : BitVec.ofNat w w ≠ 0#w := by
  intro h
  have := congrArg BitVec.toNat h
  simp [Nat.mod_eq_of_lt Nat.lt_two_pow_self] at this
  omega

/-- At width 0, every shift is out of range. -/
private theorem zero_width_ge (y : BitVec 0) : y ≥ ((0 : Nat) : BitVec 0) := by
  simp [BitVec.le_def, BitVec.toNat_of_zero_length]

private theorem right_identity_zero_shl {w v : Nat} (x : Data.LLVM.Int w) (c : BitVec v) (hc : c = 0)
    (n u : Bool) : x.shl (shiftAmount w (.val c)) n u ⊒ x := by
  rw [shiftAmount_zero c hc]
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · cases x <;> simp [Data.LLVM.Int.shl, Id.run, poison_isRefinedBy, zero_width_ge, id_pure]
  · cases x <;> simp [hw, zero_lt_width hw, ofNat_self_ne_zero hw, Data.LLVM.Int.shl, Id.run, isRefinedBy_refl, poison_isRefinedBy]

private theorem right_identity_zero_lshr {w v : Nat} (x : Data.LLVM.Int w) (c : BitVec v) (hc : c = 0)
    (e : Bool) : x.lshr (shiftAmount w (.val c)) e ⊒ x := by
  rw [shiftAmount_zero c hc]
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · cases x <;> simp [Data.LLVM.Int.lshr, Id.run, poison_isRefinedBy, zero_width_ge, id_pure]
  · cases x <;> simp [hw, zero_lt_width hw, ofNat_self_ne_zero hw, Data.LLVM.Int.lshr, Id.run, isRefinedBy_refl, poison_isRefinedBy]

private theorem right_identity_zero_ashr {w v : Nat} (x : Data.LLVM.Int w) (c : BitVec v) (hc : c = 0)
    (e : Bool) : x.ashr (shiftAmount w (.val c)) e ⊒ x := by
  rw [shiftAmount_zero c hc]
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · cases x <;> simp [Data.LLVM.Int.ashr, Id.run, poison_isRefinedBy, zero_width_ge, id_pure]
  · cases x <;> simp [hw, zero_lt_width hw, ofNat_self_ne_zero hw, Data.LLVM.Int.ashr, Id.run, isRefinedBy_refl, poison_isRefinedBy,
      BitVec.sshiftRight']


/-! ### Powers of two

The matcher reads a power of two `±2^k` with `exactLog2?`, and the rewrite shifts by `k`. -/

private theorem exactLog2?_eq_some {n k : Nat} (h : exactLog2? n = some k) : n = 2 ^ k := by
  unfold exactLog2? at h
  split at h
  · rename_i hn
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 ^ j := Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo.mp hn
    simp only [Option.some.injEq, Nat.log2_two_pow] at h
    rw [h]
  · cases h

private theorem shiftAmount_ofNat {w k : Nat} (hk : k < w) :
    shiftAmount w (Data.LLVM.Int.val (BitVec.ofNat w k)) = Data.LLVM.Int.constant w k := by
  have : k < 2 ^ w := Nat.lt_trans hk Nat.lt_two_pow_self
  simp [shiftAmount, Data.LLVM.Int.constant, Nat.mod_eq_of_lt this, hk]

private theorem shiftAmount_ofInt {w k : Nat} (hk : k < w) :
    shiftAmount w (Data.LLVM.Int.val (BitVec.ofInt w (k : Int))) = Data.LLVM.Int.constant w k := by
  rw [BitVec.ofInt_natCast]; exact shiftAmount_ofNat hk

private theorem two_pow_cast (k : Nat) : ((2 ^ k : Nat) : Int) = 2 ^ k := by push_cast; rfl

/-- A constant `2^k` that is positive as a signed integer. -/
private theorem eq_twoPow_of_toInt {w k : Nat} {c : BitVec w} (h : c.toInt = 2 ^ k) :
    k + 1 < w ∧ c = BitVec.twoPow w k := by
  have hc := BitVec.toInt_eq_toNat_cond c
  have hP := two_pow_cast k
  have hQ := two_pow_cast w
  have := c.isLt
  have := Nat.one_le_two_pow (n := k)
  have hn : c.toNat = 2 ^ k ∧ 2 * 2 ^ k < 2 ^ w := by
    split at hc <;> omega
  have hk : k + 1 < w := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (by rw [Nat.pow_succ]; omega)
  exact ⟨hk, BitVec.eq_of_toNat_eq (by rw [hn.1, BitVec.toNat_twoPow_of_lt (by omega)])⟩

/-- A constant `-2^k`, including the minimum signed value. -/
private theorem eq_neg_twoPow_of_toInt {w k : Nat} {c : BitVec w} (h : c.toInt = -2 ^ k) :
    k < w ∧ c = -BitVec.twoPow w k := by
  have hc := BitVec.toInt_eq_toNat_cond c
  have hP := two_pow_cast k
  have hQ := two_pow_cast w
  have := c.isLt
  have := Nat.one_le_two_pow (n := k)
  have hn : c.toNat = 2 ^ w - 2 ^ k ∧ 2 ^ k < 2 ^ w := by
    split at hc <;> omega
  have hk : k < w := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hn.2
  refine ⟨hk, BitVec.eq_of_toNat_eq ?_⟩
  rw [hn.1, BitVec.toNat_neg, BitVec.toNat_twoPow_of_lt hk, Nat.mod_eq_of_lt (by omega)]

private theorem udiv_pow2 {w : Nat} (x : Data.LLVM.Int w) (c : BitVec w)
    (hc : (exactLog2? c.toNat).isSome = true) (e : Bool) :
    x.udiv (.val c) e ⊒
      x.lshr (shiftAmount w (.val (BitVec.ofNat w (exactLog2? c.toNat).get!))) := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hc
  have hc2 := exactLog2?_eq_some hk
  have hkw : k < w := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (hc2 ▸ c.isLt)
  have : c = BitVec.twoPow w k :=
    BitVec.eq_of_toNat_eq (by rw [hc2, BitVec.toNat_twoPow_of_lt hkw])
  rw [hk, Option.get!_some, shiftAmount_ofNat hkw, this]
  exact Data.LLVM.udiv_by_pow2 x k hkw e

/-- The signed power of two `±2^k` that `slog2?` reads. -/
private theorem slog2_some {w k : Nat} {c : BitVec w} (hk : exactLog2? c.toInt.natAbs = some k) :
    (c.toInt < 0 → c.toInt = -2 ^ k) ∧ (¬ c.toInt < 0 → c.toInt = 2 ^ k) := by
  have habs := exactLog2?_eq_some hk
  have hP := two_pow_cast k
  constructor <;> intro hneg <;> omega

private theorem sdiv_exact_pow2_pos {w : Nat} (x : Data.LLVM.Int w) (c : BitVec w)
    (h : Option.any (fun x => !x.snd)
      (Option.map (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)) = true) :
    x.sdiv (.val c) true ⊒
      x.ashr (shiftAmount w (.val (BitVec.ofNat w
        (Option.map (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)).get!.fst))) := by
  cases hk : exactLog2? c.toInt.natAbs with
  | none => simp [hk] at h
  | some k =>
    simp only [hk, Option.map_some, Option.any_some, Bool.not_eq_true', decide_eq_false_iff_not] at h
    simp only [Option.map_some, Option.get!_some]
    obtain ⟨hkw, rfl⟩ := eq_twoPow_of_toInt ((slog2_some hk).2 h)
    rw [shiftAmount_ofNat (by omega)]
    exact Data.LLVM.sdiv_exact_by_pow2_pos x k hkw

private theorem sdiv_exact_pow2_neg {w : Nat} (x : Data.LLVM.Int w) (c : BitVec w)
    (h : Option.any (fun x => x.snd)
      (Option.map (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)) = true) :
    x.sdiv (.val c) true ⊒
      (Data.LLVM.Int.val 0#w).sub (x.ashr (shiftAmount w (.val (BitVec.ofNat w
        (Option.map (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)).get!.fst)))) := by
  cases hk : exactLog2? c.toInt.natAbs with
  | none => simp [hk] at h
  | some k =>
    simp only [hk, Option.map_some, Option.any_some, decide_eq_true_eq] at h
    simp only [Option.map_some, Option.get!_some]
    obtain ⟨hkw, rfl⟩ := eq_neg_twoPow_of_toInt ((slog2_some hk).1 h)
    rw [shiftAmount_ofNat hkw]
    simpa [Data.LLVM.Int.constant] using Data.LLVM.sdiv_exact_by_pow2_neg x k hkw

/-- The shift amounts that `sdiv_by_pow2_pattern` creates are in range. -/
private theorem sdiv_shift_amounts {w k : Nat} (hk0 : 0 < k) (hkw : k < w) :
    shiftAmount w (Data.LLVM.Int.val (BitVec.ofInt w ((w : Int) - 1))) =
        Data.LLVM.Int.constant w (w - 1 : Nat) ∧
      shiftAmount w (Data.LLVM.Int.val (BitVec.ofInt w ((w : Int) - (k : Int)))) =
        Data.LLVM.Int.constant w (w - k : Nat) := by
  constructor
  · rw [show (w : Int) - 1 = ((w - 1 : Nat) : Int) by omega, shiftAmount_ofInt (by omega)]
  · rw [show (w : Int) - (k : Int) = ((w - k : Nat) : Int) by omega, shiftAmount_ofInt (by omega)]

private theorem sdiv_pow2_pos {w : Nat} (x : Data.LLVM.Int w) (c : BitVec w)
    (h : Option.any (fun x => !decide (x.fst = 0) && !x.snd)
      (Option.map (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)) = true) :
    x.sdiv (.val c) ⊒
      (x.add ((x.ashr (shiftAmount w (.val (BitVec.ofInt w ((w : Int) - 1))))).lshr
          (shiftAmount w (.val (BitVec.ofInt w ((w : Int) - ((Option.map
            (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)).get!.fst : Nat))))))).ashr
        (shiftAmount w (.val (BitVec.ofNat w
          (Option.map (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)).get!.fst))) := by
  cases hk : exactLog2? c.toInt.natAbs with
  | none => simp [hk] at h
  | some k =>
    simp only [hk, Option.map_some, Option.any_some, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h
    simp only [Option.map_some, Option.get!_some]
    obtain ⟨hkw, rfl⟩ := eq_twoPow_of_toInt ((slog2_some hk).2 h.2)
    obtain ⟨h₁, h₂⟩ := sdiv_shift_amounts (Nat.pos_of_ne_zero h.1) (by omega : k < w)
    rw [h₁, h₂, shiftAmount_ofNat (by omega)]
    exact Data.LLVM.sdiv_by_pow2_pos x k (Nat.pos_of_ne_zero h.1) hkw

private theorem sdiv_pow2_neg {w : Nat} (x : Data.LLVM.Int w) (c : BitVec w)
    (h : Option.any (fun x => !decide (x.fst = 0) && x.snd)
      (Option.map (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)) = true) :
    x.sdiv (.val c) ⊒
      (Data.LLVM.Int.val 0#w).sub
        ((x.add ((x.ashr (shiftAmount w (.val (BitVec.ofInt w ((w : Int) - 1))))).lshr
          (shiftAmount w (.val (BitVec.ofInt w ((w : Int) - ((Option.map
            (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)).get!.fst : Nat))))))).ashr
        (shiftAmount w (.val (BitVec.ofNat w
          (Option.map (fun x => (x, decide (c.toInt < 0))) (exactLog2? c.toInt.natAbs)).get!.fst)))) := by
  cases hk : exactLog2? c.toInt.natAbs with
  | none => simp [hk] at h
  | some k =>
    simp only [hk, Option.map_some, Option.any_some, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq] at h
    simp only [Option.map_some, Option.get!_some]
    obtain ⟨hkw, rfl⟩ := eq_neg_twoPow_of_toInt ((slog2_some hk).1 h.2)
    obtain ⟨h₁, h₂⟩ := sdiv_shift_amounts (Nat.pos_of_ne_zero h.1) hkw
    rw [h₁, h₂, shiftAmount_ofNat hkw]
    simpa [Data.LLVM.Int.constant, Data.LLVM.sdivPow2Shift] using
      Data.LLVM.sdiv_by_pow2_neg x k (Nat.pos_of_ne_zero h.1) hkw

/-- The positive power of two `2^k` that `log2?` reads. -/
private theorem log2_some {w : Nat} {c : BitVec w}
    (h : (if 0 < c.toInt then exactLog2? c.toInt.toNat else none).isSome = true) :
    ∃ k, (if 0 < c.toInt then exactLog2? c.toInt.toNat else none) = some k ∧ k + 1 < w ∧
      c = BitVec.twoPow w k := by
  split at h
  · obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h
    have habs := exactLog2?_eq_some hk
    have hP := two_pow_cast k
    have hci : c.toInt = 2 ^ k := by omega
    obtain ⟨hkw, hc⟩ := eq_twoPow_of_toInt hci
    exact ⟨k, by rw [ite_eq_left_of_eq_true _ _ (eq_true ‹_›)]; exact hk, hkw, hc⟩
  · simp at h

private theorem mul_pow2 {w : Nat} (x : Data.LLVM.Int w) (c : BitVec w)
    (h : (if 0 < c.toInt then exactLog2? c.toInt.toNat else none).isSome = true) (n u : Bool) :
    x.mul (.val c) n u ⊒
      x.shl (shiftAmount w (.val (BitVec.ofNat w
        (if 0 < c.toInt then exactLog2? c.toInt.toNat else none).get!))) n u := by
  obtain ⟨k, hk, hkw, rfl⟩ := log2_some h
  rw [hk, Option.get!_some, shiftAmount_ofNat (by omega)]
  exact Data.LLVM.mul_twoPow_shl x k hkw n u

private theorem urem_pow2 {w : Nat} (x : Data.LLVM.Int w) (c : BitVec w)
    (h : (if 0 < c.toInt then exactLog2? c.toInt.toNat else none).isSome = true) :
    x.urem (.val c) ⊒ x.and (.val (BitVec.ofInt w (c.toInt - 1))) := by
  obtain ⟨k, -, hkw, rfl⟩ := log2_some h
  have hlt : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
  have hne : BitVec.twoPow w k ≠ 0#w := by
    intro h0; have := congrArg BitVec.toNat h0
    simp [BitVec.toNat_twoPow_of_lt (by omega : k < w)] at this
  have hti : (BitVec.twoPow w k).toInt = 2 ^ k := by
    rw [BitVec.toInt_twoPow]
    simp only [show ¬ w ≤ k by omega, show ¬ k + 1 = w by omega, ite_false]
  have hmask : BitVec.ofInt w ((BitVec.twoPow w k).toInt - 1) = BitVec.ofNat w (2 ^ k - 1) := by
    have := Nat.one_le_two_pow (n := k)
    have hP := two_pow_cast k
    rw [hti, show (2 : Int) ^ k - 1 = ((2 ^ k - 1 : Nat) : Int) by omega, BitVec.ofInt_natCast]
  rw [hmask]
  cases x with
  | poison => simp [Data.LLVM.Int.urem, Id.run, poison_isRefinedBy]
  | val x =>
    have hv : x % BitVec.twoPow w k = x &&& BitVec.ofNat w (2 ^ k - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_umod, BitVec.toNat_and, BitVec.toNat_twoPow_of_lt (by omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le (2 ^ k) 1) hlt),
        Nat.and_two_pow_sub_one_eq_mod]
    simp [Data.LLVM.Int.urem, Data.LLVM.Int.and, Id.run, hne, hv, isRefinedBy_refl]

/-! ### Selects of a shift on the other arm -/

private theorem shiftAmount_selectNonzero {w : Nat} (c : Data.LLVM.Int 1) (a b : Data.LLVM.Int w) :
    shiftAmount w (GMIR.selectNonzero c a b) =
      GMIR.selectNonzero c (shiftAmount w a) (shiftAmount w b) := by
  cases c <;> simp only [GMIR.selectNonzero, Id.run] <;> (try split) <;> rfl

private theorem shiftAmount_zero_of_pos {w : Nat} (hw : 0 < w) :
    shiftAmount w (Data.LLVM.Int.val 0#w) = Data.LLVM.Int.constant w 0 := by
  simp [shiftAmount, Data.LLVM.Int.constant, hw]

private theorem select_into_shl' {w : Nat} (hw : 0 < w) (c : Data.LLVM.Int 1) (x : Data.LLVM.Int w)
    (k : BitVec w) (nsw nuw : Bool) :
    GMIR.selectNonzero c (x.shl (shiftAmount w (.val k)) nsw nuw) x ⊒
      x.shl (shiftAmount w (GMIR.selectNonzero c (.val k) (.val 0#w))) := by
  rw [shiftAmount_selectNonzero, shiftAmount_zero_of_pos hw]
  exact Data.LLVM.select_into_shl hw c x _ nsw nuw

private theorem select_into_lshr' {w : Nat} (hw : 0 < w) (c : Data.LLVM.Int 1) (x : Data.LLVM.Int w)
    (k : BitVec w) (exact : Bool) :
    GMIR.selectNonzero c (x.lshr (shiftAmount w (.val k)) exact) x ⊒
      x.lshr (shiftAmount w (GMIR.selectNonzero c (.val k) (.val 0#w))) := by
  rw [shiftAmount_selectNonzero, shiftAmount_zero_of_pos hw]
  exact Data.LLVM.select_into_lshr hw c x _ exact

private theorem select_into_ashr' {w : Nat} (hw : 0 < w) (c : Data.LLVM.Int 1) (x : Data.LLVM.Int w)
    (k : BitVec w) (exact : Bool) :
    GMIR.selectNonzero c (x.ashr (shiftAmount w (.val k)) exact) x ⊒
      x.ashr (shiftAmount w (GMIR.selectNonzero c (.val k) (.val 0#w))) := by
  rw [shiftAmount_selectNonzero, shiftAmount_zero_of_pos hw]
  exact Data.LLVM.select_into_ashr hw c x _ exact

private theorem select_into_shl_swapped' {w : Nat} (hw : 0 < w) (c : Data.LLVM.Int 1)
    (x : Data.LLVM.Int w) (k : BitVec w) (nsw nuw : Bool) :
    GMIR.selectNonzero c x (x.shl (shiftAmount w (.val k)) nsw nuw) ⊒
      x.shl (shiftAmount w (GMIR.selectNonzero c (.val 0#w) (.val k))) := by
  rw [shiftAmount_selectNonzero, shiftAmount_zero_of_pos hw]
  exact Data.LLVM.select_into_shl_swapped hw c x _ nsw nuw

private theorem select_into_lshr_swapped' {w : Nat} (hw : 0 < w) (c : Data.LLVM.Int 1)
    (x : Data.LLVM.Int w) (k : BitVec w) (exact : Bool) :
    GMIR.selectNonzero c x (x.lshr (shiftAmount w (.val k)) exact) ⊒
      x.lshr (shiftAmount w (GMIR.selectNonzero c (.val 0#w) (.val k))) := by
  rw [shiftAmount_selectNonzero, shiftAmount_zero_of_pos hw]
  exact Data.LLVM.select_into_lshr_swapped hw c x _ exact

private theorem select_into_ashr_swapped' {w : Nat} (hw : 0 < w) (c : Data.LLVM.Int 1)
    (x : Data.LLVM.Int w) (k : BitVec w) (exact : Bool) :
    GMIR.selectNonzero c x (x.ashr (shiftAmount w (.val k)) exact) ⊒
      x.ashr (shiftAmount w (GMIR.selectNonzero c (.val 0#w) (.val k))) := by
  rw [shiftAmount_selectNonzero, shiftAmount_zero_of_pos hw]
  exact Data.LLVM.select_into_ashr_swapped hw c x _ exact

/-! ### Funnel shifts by a constant -/

/-- The matcher of `funnel_shift_overshift_pattern` only accepts an integer result type. -/
private theorem overshiftAmount?_isSome {p : GMIRConstantProperties} {attr : Attribute}
    {h : attr.isType = true} (hs : (overshiftAmount? p ⟨attr, h⟩).isSome = true) :
    ∃ t, attr = .integerType t := by
  cases attr <;> simp [overshiftAmount?] at hs ⊢ <;> exact ⟨_, rfl⟩

/-- `overshiftAmount?` at an integer result type. -/
private theorem overshiftAmount?_integerType (v : Int) (t' t : IntegerType)
    (h : (Attribute.integerType t).isType = true) :
    overshiftAmount? ⟨⟨v, t'⟩⟩ ⟨.integerType t, h⟩ =
      if (BitVec.ofInt t'.bitwidth v).toNat < t.bitwidth then none
      else some ⟨IntegerAttr.ofInt (((BitVec.ofInt t'.bitwidth v).toNat % t.bitwidth : Nat) : Int) t'⟩ := by
  by_cases hc : (BitVec.ofInt t'.bitwidth v).toNat < t.bitwidth <;>
    simp only [overshiftAmount?, GMIRConstantProperties.bits, hc, ite_true, ite_false] <;> rfl

private theorem fshr_zero {w v : Nat} (x y : Data.LLVM.Int w) (c : BitVec v) (hc : c = 0) :
    x.fshr y (GMIR.funnelShiftAmount w (.val c)) ⊒ y := by
  subst hc
  cases x <;> cases y <;> simp [Data.LLVM.Int.fshr, GMIR.funnelShiftAmount, Id.run, poison_isRefinedBy]
  ext i hi; simp [hi, BitVec.getLsbD_append]

private theorem fshl_zero {w v : Nat} (x y : Data.LLVM.Int w) (c : BitVec v) (hc : c = 0) :
    x.fshl y (GMIR.funnelShiftAmount w (.val c)) ⊒ x := by
  subst hc
  cases x <;> cases y <;> simp [Data.LLVM.Int.fshl, GMIR.funnelShiftAmount, Id.run, poison_isRefinedBy]
  ext i hi; simp [hi, BitVec.getLsbD_append, BitVec.getElem_extractLsb', BitVec.getElem_append,
    show ¬ w + i < w by omega]

/-- The amount `C % w` that replaces an over-large constant amount `C`: the funnel shift takes its
amount modulo `w` anyway. -/
private theorem funnelShiftAmount_overshift {w v : Nat} (c : BitVec v) (s : IntegerType.Signedness) :
    GMIR.funnelShiftAmount w
        (Data.LLVM.Int.val (BitVec.ofInt v (IntegerAttr.ofInt ((c.toNat % w : Nat) : Int) ⟨v, s⟩).value)) =
      GMIR.funnelShiftAmount w (.val c) := by
  rw [ofInt_ofInt_value, BitVec.ofInt_natCast]
  simp only [GMIR.funnelShiftAmount, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) c.isLt), Nat.mod_mod]

/-- `funnelShiftAmount_overshift`, in the normal form of `simp`. -/
private theorem funnelShiftAmount_overshift' {w v : Nat} (x : Int) (s : IntegerType.Signedness) :
    GMIR.funnelShiftAmount w
        (Data.LLVM.Int.val (BitVec.ofInt v (IntegerAttr.ofInt (max (x % 2 ^ v) 0 % (w : Int)) ⟨v, s⟩).value)) =
      GMIR.funnelShiftAmount w (.val (BitVec.ofInt v x)) := by
  have := funnelShiftAmount_overshift (w := w) (BitVec.ofInt v x) s
  simpa using this

/-! ### Selects of two constants -/

private theorem ofInt_one_neg_one : BitVec.ofInt 1 (-1) = 1#1 := by decide

private theorem constant_eq {w : Nat} (v : Int) :
    Data.LLVM.Int.constant w v = .val (BitVec.ofInt w v) := rfl

private theorem notI1_eq (c : Data.LLVM.Int 1) : Data.LLVM.notI1 c = c.xor (.val 1#1) := by
  simp [Data.LLVM.notI1, constant_eq, ofInt_one_neg_one]

private theorem soc_one_zero {w : Nat} (h : 1 < w) (_hw : w ≤ 64) (c : Data.LLVM.Int 1) (t f : BitVec w)
    (hf : f = 0) (ht : t = 1) :
    GMIR.selectNonzero c (.val t) (.val f) ⊒ c.zext w false h := by
  subst hf ht; simpa [constant_eq] using Data.LLVM.select_one_zero h c

private theorem soc_allOnes_zero {w : Nat} (h : 1 < w) (_hw : w ≤ 64) (c : Data.LLVM.Int 1)
    (t f : BitVec w) (hf : f = 0) (ht : t = -1) :
    GMIR.selectNonzero c (.val t) (.val f) ⊒ c.sext w h := by
  subst hf ht; simpa [constant_eq, Data.LLVM.ofInt_neg_one, BitVec.neg_one_eq_allOnes] using
    Data.LLVM.select_allOnes_zero h c

private theorem soc_zero_one {w : Nat} (h : 1 < w) (_hw : w ≤ 64) (c : Data.LLVM.Int 1)
    (t f : BitVec w) (hf : f = 1) (ht : t = 0) :
    GMIR.selectNonzero c (.val t) (.val f) ⊒ (c.xor (.val 1#1)).zext w false h := by
  subst hf ht; simpa [constant_eq, notI1_eq] using Data.LLVM.select_zero_one h c

private theorem soc_zero_allOnes {w : Nat} (h : 1 < w) (_hw : w ≤ 64) (c : Data.LLVM.Int 1)
    (t f : BitVec w) (hf : f = -1) (ht : t = 0) :
    GMIR.selectNonzero c (.val t) (.val f) ⊒ (c.xor (.val 1#1)).sext w h := by
  subst hf ht; simpa [constant_eq, notI1_eq, Data.LLVM.ofInt_neg_one, BitVec.neg_one_eq_allOnes] using
    Data.LLVM.select_zero_allOnes h c

private theorem soc_succ {w : Nat} (h : 1 < w) (_hw : w ≤ 64) (c : Data.LLVM.Int 1) (v₁ v : Int)
    (ht : BitVec.ofInt w v₁ = BitVec.ofInt w (v + 1)) :
    GMIR.selectNonzero c (.val (BitVec.ofInt w v₁)) (.val (BitVec.ofInt w v)) ⊒
      (c.zext w false h).add (.val (BitVec.ofInt w v)) := by
  rw [ht, BitVec.ofInt_add, show BitVec.ofInt w 1 = 1#w by simp]
  exact Data.LLVM.select_succ h c _

private theorem soc_pred {w : Nat} (h : 1 < w) (_hw : w ≤ 64) (c : Data.LLVM.Int 1) (v₁ v : Int)
    (ht : BitVec.ofInt w v₁ = BitVec.ofInt w (v + -1)) :
    GMIR.selectNonzero c (.val (BitVec.ofInt w v₁)) (.val (BitVec.ofInt w v)) ⊒
      (c.sext w h).add (.val (BitVec.ofInt w v)) := by
  rw [ht, BitVec.ofInt_add, Data.LLVM.ofInt_neg_one, ← BitVec.neg_one_eq_allOnes,
    ← BitVec.sub_eq_add_neg]
  exact Data.LLVM.select_pred h c _

/-- The constant `2^k` that `ulog2?` reads. -/
private theorem ulog2_some {w : Nat} {t : BitVec w} (h : (exactLog2? t.toNat).isSome = true) :
    ∃ k, exactLog2? t.toNat = some k ∧ k < w ∧ t = BitVec.twoPow w k := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h
  have hc2 := exactLog2?_eq_some hk
  have hkw : k < w := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (hc2 ▸ t.isLt)
  exact ⟨k, hk, hkw, BitVec.eq_of_toNat_eq (by rw [hc2, BitVec.toNat_twoPow_of_lt hkw])⟩

private theorem soc_pow2_zero {w : Nat} (h : 1 < w) (_hw : w ≤ 64) (c : Data.LLVM.Int 1)
    (t f : BitVec w) (ht : (exactLog2? t.toNat).isSome = true) (hf : f = 0) :
    GMIR.selectNonzero c (.val t) (.val f) ⊒
      (c.zext w false h).shl (shiftAmount w (.val (BitVec.ofNat w (exactLog2? t.toNat).get!))) := by
  obtain ⟨k, hk, hkw, rfl⟩ := ulog2_some ht
  subst hf
  rw [hk, Option.get!_some, shiftAmount_ofNat hkw]
  simpa [constant_eq] using Data.LLVM.select_pow2_zero h c k hkw

private theorem soc_zero_pow2 {w : Nat} (h : 1 < w) (_hw : w ≤ 64) (c : Data.LLVM.Int 1)
    (t f : BitVec w) (hf : (exactLog2? f.toNat).isSome = true) (ht : t = 0) :
    GMIR.selectNonzero c (.val t) (.val f) ⊒
      ((c.xor (.val 1#1)).zext w false h).shl
        (shiftAmount w (.val (BitVec.ofNat w (exactLog2? f.toNat).get!))) := by
  obtain ⟨k, hk, hkw, rfl⟩ := ulog2_some hf
  subst ht
  rw [hk, Option.get!_some, shiftAmount_ofNat hkw]
  simpa [constant_eq, notI1_eq] using Data.LLVM.select_zero_pow2 h c k hkw

private theorem soc_allOnes_const {w : Nat} (h : 1 < w) (_hw : w ≤ 64) (c : Data.LLVM.Int 1)
    (t f : BitVec w) (ht : t = -1) :
    GMIR.selectNonzero c (.val t) (.val f) ⊒ (c.sext w h).or (.val f) := by
  subst ht; simpa [constant_eq, Data.LLVM.ofInt_neg_one, BitVec.neg_one_eq_allOnes] using
    Data.LLVM.select_allOnes_const h c f

private theorem soc_const_allOnes {w : Nat} (h : 1 < w) (_hw : w ≤ 64) (c : Data.LLVM.Int 1)
    (t f : BitVec w) (hf : f = -1) :
    GMIR.selectNonzero c (.val t) (.val f) ⊒ ((c.xor (.val 1#1)).sext w h).or (.val t) := by
  subst hf; simpa [constant_eq, notI1_eq, Data.LLVM.ofInt_neg_one, BitVec.neg_one_eq_allOnes] using
    Data.LLVM.select_const_allOnes h c t

/-! ## Validity of every combine that matches a constant -/

@[combine_valid]
theorem combine_right_identity_zero_sub_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_sub) := by
  proveConstValid using Data.LLVM.right_identity_zero_sub

@[combine_valid]
theorem combine_right_identity_zero_add_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_add) := by
  proveConstValid using Data.LLVM.right_identity_zero_add

@[combine_valid]
theorem combine_right_identity_zero_or_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_or) := by
  proveConstValid using Data.LLVM.right_identity_zero_or

@[combine_valid]
theorem combine_right_identity_zero_xor_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_xor) := by
  proveConstValid using Data.LLVM.right_identity_zero_xor

@[combine_valid]
theorem combine_right_identity_zero_shl_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_shl) := by
  proveConstValid using right_identity_zero_shl

@[combine_valid]
theorem combine_right_identity_zero_ashr_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_ashr) := by
  proveConstValid using right_identity_zero_ashr

@[combine_valid]
theorem combine_right_identity_zero_lshr_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_lshr) := by
  proveConstValid using right_identity_zero_lshr

@[combine_valid]
theorem combine_right_identity_one_int_valid :
    Puddle.CTree.Pattern.Valid (right_identity_one_int_pattern) := by
  proveConstValid using Data.LLVM.right_identity_one_mul

@[combine_valid]
theorem combine_binop_right_to_zero_valid :
    Puddle.CTree.Pattern.Valid (binop_right_to_zero_pattern) := by
  proveConstValid using Data.LLVM.binop_right_to_zero

@[combine_valid]
theorem combine_binop_left_to_zero_shl_valid :
    Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_shl) := by
  proveConstValid using Data.LLVM.binop_left_to_zero_shl

@[combine_valid]
theorem combine_binop_left_to_zero_lshr_valid :
    Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_lshr) := by
  proveConstValid using Data.LLVM.binop_left_to_zero_lshr

@[combine_valid]
theorem combine_binop_left_to_zero_ashr_valid :
    Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_ashr) := by
  proveConstValid using Data.LLVM.binop_left_to_zero_ashr

@[combine_valid]
theorem combine_binop_left_to_zero_mul_valid :
    Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_mul) := by
  proveConstValid using Data.LLVM.binop_left_to_zero_mul

@[combine_valid]
theorem combine_sub_minus_one_valid :
    Puddle.CTree.Pattern.Valid (sub_minus_one_pattern) := by
  proveConstValid using Data.LLVM.sub_minus_one

@[combine_valid]
theorem combine_ZeroMinusAPlusB_valid :
    Puddle.CTree.Pattern.Valid (ZeroMinusAPlusB_pattern) := by
  proveConstValid using Data.LLVM.ZeroMinusAPlusB

@[combine_valid]
theorem combine_APlusZeroMinusB_valid :
    Puddle.CTree.Pattern.Valid (APlusZeroMinusB_pattern) := by
  proveConstValid using Data.LLVM.APlusZeroMinusB

@[combine_valid]
theorem combine_AMinusZeroMinusB_valid :
    Puddle.CTree.Pattern.Valid (AMinusZeroMinusB_pattern) := by
  proveConstValid using Data.LLVM.AMinusZeroMinusB

@[combine_valid]
theorem combine_sub_one_from_sub_valid :
    Puddle.CTree.Pattern.Valid (sub_one_from_sub_pattern) := by
  proveConstValid using Data.LLVM.sub_one_from_sub

@[combine_valid]
theorem combine_APlusC1MinusC2_valid :
    Puddle.CTree.Pattern.Valid (APlusC1MinusC2_pattern) := by
  proveConstValid using Data.LLVM.APlusC1MinusC2

@[combine_valid]
theorem combine_C2MinusAPlusC1_valid :
    Puddle.CTree.Pattern.Valid (C2MinusAPlusC1_pattern) := by
  proveConstValid using Data.LLVM.C2MinusAPlusC1

@[combine_valid]
theorem combine_AMinusC1MinusC2_valid :
    Puddle.CTree.Pattern.Valid (AMinusC1MinusC2_pattern) := by
  proveConstValid using Data.LLVM.AMinusC1MinusC2

@[combine_valid]
theorem combine_C1MinusAMinusC2_valid :
    Puddle.CTree.Pattern.Valid (C1MinusAMinusC2_pattern) := by
  proveConstValid using Data.LLVM.C1MinusAMinusC2

@[combine_valid]
theorem combine_AMinusC1PlusC2_valid :
    Puddle.CTree.Pattern.Valid (AMinusC1PlusC2_pattern) := by
  proveConstValid using Data.LLVM.AMinusC1PlusC2

@[combine_valid]
theorem combine_sub_of_mul_const_valid :
    Puddle.CTree.Pattern.Valid (sub_of_mul_const_pattern) := by
  proveConstValid using Data.LLVM.sub_of_mul_const

@[combine_valid]
theorem combine_mul_by_neg_one_valid :
    Puddle.CTree.Pattern.Valid (mul_by_neg_one_pattern) := by
  proveConstValid using Data.LLVM.mul_by_neg_one

@[combine_valid]
theorem combine_mulo_by_2_valid :
    Puddle.CTree.Pattern.Valid (mulo_by_2_pattern) := by
  proveConstValid using Data.LLVM.mulo_by_2

@[combine_valid]
theorem combine_NotAPlusNegOne_valid :
    Puddle.CTree.Pattern.Valid (NotAPlusNegOne_pattern) := by
  proveConstValid using Data.LLVM.NotAPlusNegOne

@[combine_valid]
theorem combine_add_shift_valid :
    Puddle.CTree.Pattern.Valid (add_shift_pattern false) := by
  proveConstValid using Data.LLVM.add_shift

@[combine_valid]
theorem combine_add_shift_swapped_valid :
    Puddle.CTree.Pattern.Valid (add_shift_pattern true) := by
  proveConstValid using Data.LLVM.add_shift'

@[combine_valid]
theorem combine_or_and_xor_to_or_or_and_valid :
    Puddle.CTree.Pattern.Valid (or_and_xor_to_or_pattern .g_or .g_and) := by
  proveConstValid using Data.LLVM.or_and_xor_to_or

@[combine_valid]
theorem combine_or_and_xor_to_or_and_or_valid :
    Puddle.CTree.Pattern.Valid (or_and_xor_to_or_pattern .g_and .g_or) := by
  proveConstValid using Data.LLVM.or_and_xor_to_or'

@[combine_valid]
theorem combine_or_and_xor_to_xor_or_or_and_valid :
    Puddle.CTree.Pattern.Valid (or_and_xor_to_xor_or_pattern .g_or .g_and) := by
  proveConstValid using Data.LLVM.or_and_xor_to_xor_or

@[combine_valid]
theorem combine_or_and_xor_to_xor_or_and_or_valid :
    Puddle.CTree.Pattern.Valid (or_and_xor_to_xor_or_pattern .g_and .g_or) := by
  proveConstValid using Data.LLVM.or_and_xor_to_xor_or'

@[combine_valid]
theorem combine_simplify_neg_smax_valid :
    Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_smax .g_smin) := by
  proveConstValid using Data.LLVM.simplify_neg_smax

@[combine_valid]
theorem combine_simplify_neg_umax_valid :
    Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_umax .g_umin) := by
  proveConstValid using Data.LLVM.simplify_neg_umax

@[combine_valid]
theorem combine_simplify_neg_smin_valid :
    Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_smin .g_smax) := by
  proveConstValid using Data.LLVM.simplify_neg_smin

@[combine_valid]
theorem combine_simplify_neg_umin_valid :
    Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_umin .g_umax) := by
  proveConstValid using Data.LLVM.simplify_neg_umin

@[combine_valid]
theorem combine_not_cmp_fold_eq_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .eq .ne) := by
  proveConstValid using Data.LLVM.not_cmp_fold_zext, Data.LLVM.not_cmp_fold

@[combine_valid]
theorem combine_not_cmp_fold_ne_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ne .eq) := by
  proveConstValid using Data.LLVM.not_cmp_fold_zext, Data.LLVM.not_cmp_fold

@[combine_valid]
theorem combine_not_cmp_fold_ugt_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ugt .ule) := by
  proveConstValid using Data.LLVM.not_cmp_fold_zext, Data.LLVM.not_cmp_fold

@[combine_valid]
theorem combine_not_cmp_fold_uge_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .uge .ult) := by
  proveConstValid using Data.LLVM.not_cmp_fold_zext, Data.LLVM.not_cmp_fold

@[combine_valid]
theorem combine_not_cmp_fold_ult_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ult .uge) := by
  proveConstValid using Data.LLVM.not_cmp_fold_zext, Data.LLVM.not_cmp_fold

@[combine_valid]
theorem combine_not_cmp_fold_ule_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ule .ugt) := by
  proveConstValid using Data.LLVM.not_cmp_fold_zext, Data.LLVM.not_cmp_fold

@[combine_valid]
theorem combine_not_cmp_fold_sgt_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sgt .sle) := by
  proveConstValid using Data.LLVM.not_cmp_fold_zext, Data.LLVM.not_cmp_fold

@[combine_valid]
theorem combine_not_cmp_fold_sge_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sge .slt) := by
  proveConstValid using Data.LLVM.not_cmp_fold_zext, Data.LLVM.not_cmp_fold

@[combine_valid]
theorem combine_not_cmp_fold_slt_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .slt .sge) := by
  proveConstValid using Data.LLVM.not_cmp_fold_zext, Data.LLVM.not_cmp_fold

@[combine_valid]
theorem combine_not_cmp_fold_sle_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sle .sgt) := by
  proveConstValid using Data.LLVM.not_cmp_fold_zext, Data.LLVM.not_cmp_fold

@[combine_valid]
theorem combine_double_icmp_zero_and_valid :
    Puddle.CTree.Pattern.Valid (double_icmp_zero_pattern .g_and .eq) := by
  proveConstValid using Data.LLVM.double_icmp_zero_and_zext, Data.LLVM.double_icmp_zero_and

@[combine_valid]
theorem combine_double_icmp_zero_or_valid :
    Puddle.CTree.Pattern.Valid (double_icmp_zero_pattern .g_or .ne) := by
  proveConstValid using Data.LLVM.double_icmp_zero_or_zext, Data.LLVM.double_icmp_zero_or

@[combine_valid]
theorem combine_udiv_by_pow2_valid :
    Puddle.CTree.Pattern.Valid (udiv_by_pow2_pattern) := by
  proveConstValid using udiv_pow2

@[combine_valid]
theorem combine_sdiv_exact_by_pow2_pos_valid :
    Puddle.CTree.Pattern.Valid (sdiv_exact_by_pow2_pattern false) := by
  proveConstValid using sdiv_exact_pow2_pos

@[combine_valid]
theorem combine_sdiv_exact_by_pow2_neg_valid :
    Puddle.CTree.Pattern.Valid (sdiv_exact_by_pow2_pattern true) := by
  proveConstValid using sdiv_exact_pow2_neg

@[combine_valid]
theorem combine_sdiv_by_pow2_pos_valid :
    Puddle.CTree.Pattern.Valid (sdiv_by_pow2_pattern false) := by
  proveConstValid using sdiv_pow2_pos

@[combine_valid]
theorem combine_sdiv_by_pow2_neg_valid :
    Puddle.CTree.Pattern.Valid (sdiv_by_pow2_pattern true) := by
  proveConstValid using sdiv_pow2_neg

@[combine_valid]
theorem combine_mul_to_shl_valid :
    Puddle.CTree.Pattern.Valid (mul_to_shl_pattern) := by
  proveConstValid using mul_pow2

@[combine_valid]
theorem combine_urem_pow2_to_mask_valid :
    Puddle.CTree.Pattern.Valid (urem_pow2_to_mask_pattern) := by
  proveConstValid using urem_pow2

@[combine_valid]
theorem combine_constant_fold_add_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_add (fun a b => a + b)) := by
  proveConstValid using Data.LLVM.constant_fold_add

@[combine_valid]
theorem combine_constant_fold_sub_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_sub ((· - ·))) := by
  proveConstValid using Data.LLVM.constant_fold_sub

@[combine_valid]
theorem combine_constant_fold_mul_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_mul ((· * ·))) := by
  proveConstValid using Data.LLVM.constant_fold_mul

@[combine_valid]
theorem combine_constant_fold_smin_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_smin (min)) := by
  proveConstValid using Data.LLVM.constant_fold_smin

@[combine_valid]
theorem combine_constant_fold_smax_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_smax (max)) := by
  proveConstValid using Data.LLVM.constant_fold_smax

@[combine_valid]
theorem combine_select_constant_cmp_nonzero_valid :
    Puddle.CTree.Pattern.Valid (select_constant_cmp_pattern true) := by
  proveConstValid using Data.LLVM.select_constant_cmp_nonzero

@[combine_valid]
theorem combine_select_constant_cmp_zero_valid :
    Puddle.CTree.Pattern.Valid (select_constant_cmp_pattern false) := by
  proveConstValid using Data.LLVM.select_constant_cmp_zero

@[combine_valid]
theorem combine_sub_to_add_valid (info : LegalizerInfo) :
    Puddle.CTree.Pattern.Valid (sub_to_add_pattern info) := by
  proveConstValid using Data.LLVM.sub_to_add

set_option maxHeartbeats 4000000 in
@[combine_valid]
theorem combine_redundant_and_select_icmp_constant_valid :
    Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .icmp .constant) := by
  proveConstValid using Data.LLVM.and_select_bool_odd

set_option maxHeartbeats 4000000 in
@[combine_valid]
theorem combine_redundant_and_select_constant_icmp_valid :
    Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .constant .icmp) := by
  proveConstValid using Data.LLVM.and_select_bool_odd

set_option maxHeartbeats 4000000 in
@[combine_valid]
theorem combine_redundant_and_select_constant_constant_valid :
    Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .constant .constant) := by
  proveConstValid using Data.LLVM.and_select_bool_odd

@[combine_valid]
theorem combine_select_into_shl_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_shl false) := by
  proveConstValid using select_into_shl'

@[combine_valid]
theorem combine_select_into_shl_swapped_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_shl true) := by
  proveConstValid using select_into_shl_swapped'

@[combine_valid]
theorem combine_select_into_lshr_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_lshr false) := by
  proveConstValid using select_into_lshr'

@[combine_valid]
theorem combine_select_into_lshr_swapped_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_lshr true) := by
  proveConstValid using select_into_lshr_swapped'

@[combine_valid]
theorem combine_select_into_ashr_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_ashr false) := by
  proveConstValid using select_into_ashr'

@[combine_valid]
theorem combine_select_into_ashr_swapped_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_ashr true) := by
  proveConstValid using select_into_ashr_swapped'

@[combine_valid]
theorem combine_select_one_zero_valid :
    Puddle.CTree.Pattern.Valid (select_one_zero_pattern) := by
  proveConstValid using soc_one_zero

@[combine_valid]
theorem combine_select_allOnes_zero_valid :
    Puddle.CTree.Pattern.Valid (select_allOnes_zero_pattern) := by
  proveConstValid using soc_allOnes_zero

@[combine_valid]
theorem combine_select_zero_one_valid :
    Puddle.CTree.Pattern.Valid (select_zero_one_pattern) := by
  proveConstValid using soc_zero_one

@[combine_valid]
theorem combine_select_zero_allOnes_valid :
    Puddle.CTree.Pattern.Valid (select_zero_allOnes_pattern) := by
  proveConstValid using soc_zero_allOnes

@[combine_valid]
theorem combine_select_succ_valid :
    Puddle.CTree.Pattern.Valid (select_succ_pattern) := by
  proveConstValid using soc_succ

@[combine_valid]
theorem combine_select_pred_valid :
    Puddle.CTree.Pattern.Valid (select_pred_pattern) := by
  proveConstValid using soc_pred

@[combine_valid]
theorem combine_select_pow2_zero_valid :
    Puddle.CTree.Pattern.Valid (select_pow2_zero_pattern) := by
  proveConstValid using soc_pow2_zero

@[combine_valid]
theorem combine_select_zero_pow2_valid :
    Puddle.CTree.Pattern.Valid (select_zero_pow2_pattern) := by
  proveConstValid using soc_zero_pow2

@[combine_valid]
theorem combine_select_allOnes_const_valid :
    Puddle.CTree.Pattern.Valid (select_allOnes_const_pattern) := by
  proveConstValid using soc_allOnes_const

@[combine_valid]
theorem combine_select_const_allOnes_valid :
    Puddle.CTree.Pattern.Valid (select_const_allOnes_pattern) := by
  proveConstValid using soc_const_allOnes

set_option maxHeartbeats 4000000 in
@[combine_valid]
theorem combine_funnel_shift_right_zero_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_zero_pattern .g_fshr true) := by
  normalizeTypedConstants
  all_goals closeConstWith fshr_zero

set_option maxHeartbeats 4000000 in
@[combine_valid]
theorem combine_funnel_shift_left_zero_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_zero_pattern .g_fshl false) := by
  normalizeTypedConstants
  all_goals closeConstWith fshl_zero

set_option maxHeartbeats 4000000 in
@[combine_valid]
theorem combine_funnel_shift_overshift_l_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_overshift_pattern .g_fshl) := by
  normalizeTypedConstants
  all_goals (obtain ⟨t, rfl⟩ := overshiftAmount?_isSome ‹_›)
  all_goals (simp only [RuntimeValue.Conforms] at *)
  all_goals subst_vars
  all_goals (simp only [overshiftAmount?_integerType] at *)
  all_goals split
  all_goals (try simp_all [funnelShiftAmount_overshift', RuntimeValue.isRefinedBy, isRefinedBy_refl])
  all_goals (rename_i heq; subst heq)
  all_goals (simp only [funnelShiftAmount_overshift']; exact isRefinedBy_refl _)

set_option maxHeartbeats 4000000 in
@[combine_valid]
theorem combine_funnel_shift_overshift_r_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_overshift_pattern .g_fshr) := by
  normalizeTypedConstants
  all_goals (obtain ⟨t, rfl⟩ := overshiftAmount?_isSome ‹_›)
  all_goals (simp only [RuntimeValue.Conforms] at *)
  all_goals subst_vars
  all_goals (simp only [overshiftAmount?_integerType] at *)
  all_goals split
  all_goals (try simp_all [funnelShiftAmount_overshift', RuntimeValue.isRefinedBy, isRefinedBy_refl])
  all_goals (rename_i heq; subst heq)
  all_goals (simp only [funnelShiftAmount_overshift']; exact isRefinedBy_refl _)

/-! ## Status of every combine that matches a constant -/

@[legalization_status]
theorem combine_right_identity_zero_sub_status :
    Status Unproven (right_identity_zero_pattern .g_sub) :=
  .proven (combine_right_identity_zero_sub_valid)

@[legalization_status]
theorem combine_right_identity_zero_add_status :
    Status Unproven (right_identity_zero_pattern .g_add) :=
  .proven (combine_right_identity_zero_add_valid)

@[legalization_status]
theorem combine_right_identity_zero_or_status :
    Status Unproven (right_identity_zero_pattern .g_or) :=
  .proven (combine_right_identity_zero_or_valid)

@[legalization_status]
theorem combine_right_identity_zero_xor_status :
    Status Unproven (right_identity_zero_pattern .g_xor) :=
  .proven (combine_right_identity_zero_xor_valid)

@[legalization_status]
theorem combine_right_identity_zero_shl_status :
    Status Unproven (right_identity_zero_pattern .g_shl) :=
  .proven (combine_right_identity_zero_shl_valid)

@[legalization_status]
theorem combine_right_identity_zero_ashr_status :
    Status Unproven (right_identity_zero_pattern .g_ashr) :=
  .proven (combine_right_identity_zero_ashr_valid)

@[legalization_status]
theorem combine_right_identity_zero_lshr_status :
    Status Unproven (right_identity_zero_pattern .g_lshr) :=
  .proven (combine_right_identity_zero_lshr_valid)

@[legalization_status]
theorem combine_right_identity_one_int_status :
    Status Unproven (right_identity_one_int_pattern) :=
  .proven (combine_right_identity_one_int_valid)

@[legalization_status]
theorem combine_binop_right_to_zero_status :
    Status Unproven (binop_right_to_zero_pattern) :=
  .proven (combine_binop_right_to_zero_valid)

@[legalization_status]
theorem combine_binop_left_to_zero_shl_status :
    Status Unproven (binop_left_to_zero_pattern .g_shl) :=
  .proven (combine_binop_left_to_zero_shl_valid)

@[legalization_status]
theorem combine_binop_left_to_zero_lshr_status :
    Status Unproven (binop_left_to_zero_pattern .g_lshr) :=
  .proven (combine_binop_left_to_zero_lshr_valid)

@[legalization_status]
theorem combine_binop_left_to_zero_ashr_status :
    Status Unproven (binop_left_to_zero_pattern .g_ashr) :=
  .proven (combine_binop_left_to_zero_ashr_valid)

@[legalization_status]
theorem combine_binop_left_to_zero_mul_status :
    Status Unproven (binop_left_to_zero_pattern .g_mul) :=
  .proven (combine_binop_left_to_zero_mul_valid)

@[legalization_status]
theorem combine_sub_minus_one_status :
    Status Unproven (sub_minus_one_pattern) :=
  .proven (combine_sub_minus_one_valid)

@[legalization_status]
theorem combine_ZeroMinusAPlusB_status :
    Status Unproven (ZeroMinusAPlusB_pattern) :=
  .proven (combine_ZeroMinusAPlusB_valid)

@[legalization_status]
theorem combine_APlusZeroMinusB_status :
    Status Unproven (APlusZeroMinusB_pattern) :=
  .proven (combine_APlusZeroMinusB_valid)

@[legalization_status]
theorem combine_AMinusZeroMinusB_status :
    Status Unproven (AMinusZeroMinusB_pattern) :=
  .proven (combine_AMinusZeroMinusB_valid)

@[legalization_status]
theorem combine_sub_one_from_sub_status :
    Status Unproven (sub_one_from_sub_pattern) :=
  .proven (combine_sub_one_from_sub_valid)

@[legalization_status]
theorem combine_APlusC1MinusC2_status :
    Status Unproven (APlusC1MinusC2_pattern) :=
  .proven (combine_APlusC1MinusC2_valid)

@[legalization_status]
theorem combine_C2MinusAPlusC1_status :
    Status Unproven (C2MinusAPlusC1_pattern) :=
  .proven (combine_C2MinusAPlusC1_valid)

@[legalization_status]
theorem combine_AMinusC1MinusC2_status :
    Status Unproven (AMinusC1MinusC2_pattern) :=
  .proven (combine_AMinusC1MinusC2_valid)

@[legalization_status]
theorem combine_C1MinusAMinusC2_status :
    Status Unproven (C1MinusAMinusC2_pattern) :=
  .proven (combine_C1MinusAMinusC2_valid)

@[legalization_status]
theorem combine_AMinusC1PlusC2_status :
    Status Unproven (AMinusC1PlusC2_pattern) :=
  .proven (combine_AMinusC1PlusC2_valid)

@[legalization_status]
theorem combine_sub_of_mul_const_status :
    Status Unproven (sub_of_mul_const_pattern) :=
  .proven (combine_sub_of_mul_const_valid)

@[legalization_status]
theorem combine_mul_by_neg_one_status :
    Status Unproven (mul_by_neg_one_pattern) :=
  .proven (combine_mul_by_neg_one_valid)

@[legalization_status]
theorem combine_mulo_by_2_status :
    Status Unproven (mulo_by_2_pattern) :=
  .proven (combine_mulo_by_2_valid)

@[legalization_status]
theorem combine_NotAPlusNegOne_status :
    Status Unproven (NotAPlusNegOne_pattern) :=
  .proven (combine_NotAPlusNegOne_valid)

@[legalization_status]
theorem combine_add_shift_status :
    Status Unproven (add_shift_pattern false) :=
  .proven (combine_add_shift_valid)

@[legalization_status]
theorem combine_add_shift_swapped_status :
    Status Unproven (add_shift_pattern true) :=
  .proven (combine_add_shift_swapped_valid)

@[legalization_status]
theorem combine_or_and_xor_to_or_or_and_status :
    Status Unproven (or_and_xor_to_or_pattern .g_or .g_and) :=
  .proven (combine_or_and_xor_to_or_or_and_valid)

@[legalization_status]
theorem combine_or_and_xor_to_or_and_or_status :
    Status Unproven (or_and_xor_to_or_pattern .g_and .g_or) :=
  .proven (combine_or_and_xor_to_or_and_or_valid)

@[legalization_status]
theorem combine_or_and_xor_to_xor_or_or_and_status :
    Status Unproven (or_and_xor_to_xor_or_pattern .g_or .g_and) :=
  .proven (combine_or_and_xor_to_xor_or_or_and_valid)

@[legalization_status]
theorem combine_or_and_xor_to_xor_or_and_or_status :
    Status Unproven (or_and_xor_to_xor_or_pattern .g_and .g_or) :=
  .proven (combine_or_and_xor_to_xor_or_and_or_valid)

@[legalization_status]
theorem combine_simplify_neg_smax_status :
    Status Unproven (simplify_neg_minmax_pattern .g_smax .g_smin) :=
  .proven (combine_simplify_neg_smax_valid)

@[legalization_status]
theorem combine_simplify_neg_umax_status :
    Status Unproven (simplify_neg_minmax_pattern .g_umax .g_umin) :=
  .proven (combine_simplify_neg_umax_valid)

@[legalization_status]
theorem combine_simplify_neg_smin_status :
    Status Unproven (simplify_neg_minmax_pattern .g_smin .g_smax) :=
  .proven (combine_simplify_neg_smin_valid)

@[legalization_status]
theorem combine_simplify_neg_umin_status :
    Status Unproven (simplify_neg_minmax_pattern .g_umin .g_umax) :=
  .proven (combine_simplify_neg_umin_valid)

@[legalization_status]
theorem combine_not_cmp_fold_eq_status :
    Status Unproven (not_cmp_fold_pattern .eq .ne) :=
  .proven (combine_not_cmp_fold_eq_valid)

@[legalization_status]
theorem combine_not_cmp_fold_ne_status :
    Status Unproven (not_cmp_fold_pattern .ne .eq) :=
  .proven (combine_not_cmp_fold_ne_valid)

@[legalization_status]
theorem combine_not_cmp_fold_ugt_status :
    Status Unproven (not_cmp_fold_pattern .ugt .ule) :=
  .proven (combine_not_cmp_fold_ugt_valid)

@[legalization_status]
theorem combine_not_cmp_fold_uge_status :
    Status Unproven (not_cmp_fold_pattern .uge .ult) :=
  .proven (combine_not_cmp_fold_uge_valid)

@[legalization_status]
theorem combine_not_cmp_fold_ult_status :
    Status Unproven (not_cmp_fold_pattern .ult .uge) :=
  .proven (combine_not_cmp_fold_ult_valid)

@[legalization_status]
theorem combine_not_cmp_fold_ule_status :
    Status Unproven (not_cmp_fold_pattern .ule .ugt) :=
  .proven (combine_not_cmp_fold_ule_valid)

@[legalization_status]
theorem combine_not_cmp_fold_sgt_status :
    Status Unproven (not_cmp_fold_pattern .sgt .sle) :=
  .proven (combine_not_cmp_fold_sgt_valid)

@[legalization_status]
theorem combine_not_cmp_fold_sge_status :
    Status Unproven (not_cmp_fold_pattern .sge .slt) :=
  .proven (combine_not_cmp_fold_sge_valid)

@[legalization_status]
theorem combine_not_cmp_fold_slt_status :
    Status Unproven (not_cmp_fold_pattern .slt .sge) :=
  .proven (combine_not_cmp_fold_slt_valid)

@[legalization_status]
theorem combine_not_cmp_fold_sle_status :
    Status Unproven (not_cmp_fold_pattern .sle .sgt) :=
  .proven (combine_not_cmp_fold_sle_valid)

@[legalization_status]
theorem combine_double_icmp_zero_and_status :
    Status Unproven (double_icmp_zero_pattern .g_and .eq) :=
  .proven (combine_double_icmp_zero_and_valid)

@[legalization_status]
theorem combine_double_icmp_zero_or_status :
    Status Unproven (double_icmp_zero_pattern .g_or .ne) :=
  .proven (combine_double_icmp_zero_or_valid)

@[legalization_status]
theorem combine_udiv_by_pow2_status :
    Status Unproven (udiv_by_pow2_pattern) :=
  .proven (combine_udiv_by_pow2_valid)

@[legalization_status]
theorem combine_sdiv_exact_by_pow2_pos_status :
    Status Unproven (sdiv_exact_by_pow2_pattern false) :=
  .proven (combine_sdiv_exact_by_pow2_pos_valid)

@[legalization_status]
theorem combine_sdiv_exact_by_pow2_neg_status :
    Status Unproven (sdiv_exact_by_pow2_pattern true) :=
  .proven (combine_sdiv_exact_by_pow2_neg_valid)

@[legalization_status]
theorem combine_sdiv_by_pow2_pos_status :
    Status Unproven (sdiv_by_pow2_pattern false) :=
  .proven (combine_sdiv_by_pow2_pos_valid)

@[legalization_status]
theorem combine_sdiv_by_pow2_neg_status :
    Status Unproven (sdiv_by_pow2_pattern true) :=
  .proven (combine_sdiv_by_pow2_neg_valid)

@[legalization_status]
theorem combine_mul_to_shl_status :
    Status Unproven (mul_to_shl_pattern) :=
  .proven (combine_mul_to_shl_valid)

@[legalization_status]
theorem combine_urem_pow2_to_mask_status :
    Status Unproven (urem_pow2_to_mask_pattern) :=
  .proven (combine_urem_pow2_to_mask_valid)

@[legalization_status]
theorem combine_constant_fold_add_status :
    Status Unproven (constant_fold_binop_pattern .g_add (fun a b => a + b)) :=
  .proven (combine_constant_fold_add_valid)

@[legalization_status]
theorem combine_constant_fold_sub_status :
    Status Unproven (constant_fold_binop_pattern .g_sub ((· - ·))) :=
  .proven (combine_constant_fold_sub_valid)

@[legalization_status]
theorem combine_constant_fold_mul_status :
    Status Unproven (constant_fold_binop_pattern .g_mul ((· * ·))) :=
  .proven (combine_constant_fold_mul_valid)

@[legalization_status]
theorem combine_constant_fold_smin_status :
    Status Unproven (constant_fold_binop_pattern .g_smin (min)) :=
  .proven (combine_constant_fold_smin_valid)

@[legalization_status]
theorem combine_constant_fold_smax_status :
    Status Unproven (constant_fold_binop_pattern .g_smax (max)) :=
  .proven (combine_constant_fold_smax_valid)

@[legalization_status]
theorem combine_select_constant_cmp_nonzero_status :
    Status Unproven (select_constant_cmp_pattern true) :=
  .proven (combine_select_constant_cmp_nonzero_valid)

@[legalization_status]
theorem combine_select_constant_cmp_zero_status :
    Status Unproven (select_constant_cmp_pattern false) :=
  .proven (combine_select_constant_cmp_zero_valid)

@[legalization_status]
theorem combine_sub_to_add_status (info : LegalizerInfo) :
    Status Unproven (sub_to_add_pattern info) :=
  .proven (combine_sub_to_add_valid info)

@[legalization_status]
theorem combine_redundant_and_select_icmp_constant_status :
    Status Unproven (redundant_and_select_pattern .icmp .constant) :=
  .proven (combine_redundant_and_select_icmp_constant_valid)

@[legalization_status]
theorem combine_redundant_and_select_constant_icmp_status :
    Status Unproven (redundant_and_select_pattern .constant .icmp) :=
  .proven (combine_redundant_and_select_constant_icmp_valid)

@[legalization_status]
theorem combine_redundant_and_select_constant_constant_status :
    Status Unproven (redundant_and_select_pattern .constant .constant) :=
  .proven (combine_redundant_and_select_constant_constant_valid)

@[legalization_status]
theorem combine_select_into_shl_status :
    Status Unproven (select_into_binop_pattern .g_shl false) :=
  .proven (combine_select_into_shl_valid)

@[legalization_status]
theorem combine_select_into_shl_swapped_status :
    Status Unproven (select_into_binop_pattern .g_shl true) :=
  .proven (combine_select_into_shl_swapped_valid)

@[legalization_status]
theorem combine_select_into_lshr_status :
    Status Unproven (select_into_binop_pattern .g_lshr false) :=
  .proven (combine_select_into_lshr_valid)

@[legalization_status]
theorem combine_select_into_lshr_swapped_status :
    Status Unproven (select_into_binop_pattern .g_lshr true) :=
  .proven (combine_select_into_lshr_swapped_valid)

@[legalization_status]
theorem combine_select_into_ashr_status :
    Status Unproven (select_into_binop_pattern .g_ashr false) :=
  .proven (combine_select_into_ashr_valid)

@[legalization_status]
theorem combine_select_into_ashr_swapped_status :
    Status Unproven (select_into_binop_pattern .g_ashr true) :=
  .proven (combine_select_into_ashr_swapped_valid)

@[legalization_status]
theorem combine_select_one_zero_status :
    Status Unproven (select_one_zero_pattern) :=
  .proven (combine_select_one_zero_valid)

@[legalization_status]
theorem combine_select_allOnes_zero_status :
    Status Unproven (select_allOnes_zero_pattern) :=
  .proven (combine_select_allOnes_zero_valid)

@[legalization_status]
theorem combine_select_zero_one_status :
    Status Unproven (select_zero_one_pattern) :=
  .proven (combine_select_zero_one_valid)

@[legalization_status]
theorem combine_select_zero_allOnes_status :
    Status Unproven (select_zero_allOnes_pattern) :=
  .proven (combine_select_zero_allOnes_valid)

@[legalization_status]
theorem combine_select_succ_status :
    Status Unproven (select_succ_pattern) :=
  .proven (combine_select_succ_valid)

@[legalization_status]
theorem combine_select_pred_status :
    Status Unproven (select_pred_pattern) :=
  .proven (combine_select_pred_valid)

@[legalization_status]
theorem combine_select_pow2_zero_status :
    Status Unproven (select_pow2_zero_pattern) :=
  .proven (combine_select_pow2_zero_valid)

@[legalization_status]
theorem combine_select_zero_pow2_status :
    Status Unproven (select_zero_pow2_pattern) :=
  .proven (combine_select_zero_pow2_valid)

@[legalization_status]
theorem combine_select_allOnes_const_status :
    Status Unproven (select_allOnes_const_pattern) :=
  .proven (combine_select_allOnes_const_valid)

@[legalization_status]
theorem combine_select_const_allOnes_status :
    Status Unproven (select_const_allOnes_pattern) :=
  .proven (combine_select_const_allOnes_valid)

@[legalization_status]
theorem combine_funnel_shift_right_zero_status :
    Status Unproven (funnel_shift_zero_pattern .g_fshr true) :=
  .proven (combine_funnel_shift_right_zero_valid)

@[legalization_status]
theorem combine_funnel_shift_left_zero_status :
    Status Unproven (funnel_shift_zero_pattern .g_fshl false) :=
  .proven (combine_funnel_shift_left_zero_valid)

@[legalization_status]
theorem combine_funnel_shift_overshift_l_status :
    Status Unproven (funnel_shift_overshift_pattern .g_fshl) :=
  .proven (combine_funnel_shift_overshift_l_valid)

@[legalization_status]
theorem combine_funnel_shift_overshift_r_status :
    Status Unproven (funnel_shift_overshift_pattern .g_fshr) :=
  .proven (combine_funnel_shift_overshift_r_valid)

end Veir.Legalization.CTreeProofs
