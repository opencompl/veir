module

import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR.Semantics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Int.Bitblast
import Veir.Passes.Legalization.Proofs
import all Veir.Passes.Legalization.LegalizerHelper

/-!
# Bitblasting the gMIR interpreter's helpers

`veir_bv_normalize` rewrites for the helpers of the gMIR interpreter (`shiftAmount`,
`resizeCount`, `funnelShiftAmount`, `uaddWithCarry`, `usubWithBorrow`, the division UB checks,
the default properties of created operations, and a few constants and bit extractions), stated with
widths built from `+` so that `pbv_decide` can mask them. Several helpers are private to
`Veir.Dialects.GMIR.OpInfo`, so these lemmas are too: import this module with `import all`.
-/

namespace Veir.Legalization.CTreeProofs.PBV

set_option linter.unusedSimpArgs false

section Normalize

open Data.LLVM

/-- `x.toNat < w` as a comparison at a width that holds both `x` and `w`. -/
theorem toNat_lt_iff_setWidth_lt {v : Nat} (w : Nat) (x : BitVec v) :
    x.toNat < w ↔ x.setWidth (v + w) < BitVec.ofNat (v + w) w := by
  have hx : x.toNat < 2 ^ (v + w) :=
    Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega))
  have hw : w < 2 ^ (v + w) :=
    Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide) (by omega))
  simp [BitVec.lt_def, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hw]

@[veir_bv_normalize]
theorem isPoison_shiftAmount {v : Nat} (w : Nat) (a : Int v) :
    (shiftAmount w a).isPoison = a.isPoison := by
  cases a <;> rfl

@[veir_bv_normalize]
theorem getValue_shiftAmount {v : Nat} (w : Nat) (a : Int v) (h : (shiftAmount w a).isPoison = false) :
    (shiftAmount w a).getValue h =
      if (a.getValue (by rwa [isPoison_shiftAmount] at h)).setWidth (v + w) < BitVec.ofNat (v + w) w then
        (a.getValue (by rwa [isPoison_shiftAmount] at h)).setWidth w
      else BitVec.allOnes w := by
  cases a with
  | poison => simp [shiftAmount, Int.isPoison] at h
  | val a => simp [shiftAmount, Int.getValue, ← toNat_lt_iff_setWidth_lt]

@[veir_bv_normalize]
theorem isPoison_resizeCount {v : Nat} (w : Nat) (a : Int v) :
    (resizeCount w a).isPoison = a.isPoison := by
  cases a <;> rfl

@[veir_bv_normalize]
theorem getValue_resizeCount {v : Nat} (w : Nat) (a : Int v) (h : (resizeCount w a).isPoison = false) :
    (resizeCount w a).getValue h = (a.getValue (by rwa [isPoison_resizeCount] at h)).setWidth w := by
  cases a with
  | poison => simp [resizeCount, Int.isPoison] at h
  | val a => simp [resizeCount, Int.getValue]

/-! The UB checks of the divisions, as propositions on the values: `proveLegalValid` leaves them as
guards `… = true` or `… = false`, which then normalize to bit-vector equalities rather than to
Boolean comparisons, which `pbv_decide` does not translate. -/

@[veir_bv_normalize]
theorem isUnsignedDivisionUB_eq_true_iff {w : Nat} (y : Int w) :
    y.isUnsignedDivisionUB = true ↔ y.isPoison = true ∨ y.getValueD = 0 := by
  cases y <;> simp [Int.isUnsignedDivisionUB, Int.isPoison, Int.getValueD]

@[veir_bv_normalize]
theorem isUnsignedDivisionUB_eq_false_iff {w : Nat} (y : Int w) :
    y.isUnsignedDivisionUB = false ↔ y.isPoison = false ∧ ¬y.getValueD = 0 := by
  cases y <;> simp [Int.isUnsignedDivisionUB, Int.isPoison, Int.getValueD]

@[veir_bv_normalize]
theorem isSignedDivisionUB_eq_true_iff {w : Nat} (x y : Int w) :
    x.isSignedDivisionUB y = true ↔
      y.isPoison = true ∨ y.getValueD = 0 ∨
        (y.getValueD = -1 ∧ (x.isPoison = true ∨ x.getValueD = BitVec.intMin w)) := by
  cases x <;> cases y <;> simp [Int.isSignedDivisionUB, Int.isPoison, Int.getValueD]

@[veir_bv_normalize]
theorem isSignedDivisionUB_eq_false_iff {w : Nat} (x y : Int w) :
    x.isSignedDivisionUB y = false ↔
      ¬(y.isPoison = true ∨ y.getValueD = 0 ∨
        (y.getValueD = -1 ∧ (x.isPoison = true ∨ x.getValueD = BitVec.intMin w))) := by
  rw [← isSignedDivisionUB_eq_true_iff, Bool.not_eq_true]

/-- The carry out of `x + y + c` is the top bit of the sum one bit wider. -/
theorem ofBool_carry_eq_msb {w : Nat} (x y : BitVec w) (c : BitVec 1) :
    BitVec.ofBool (BitVec.carry w x y (c.getLsbD 0)) =
      BitVec.ofBool (x.setWidth (w + 1) + y.setWidth (w + 1) + c.setWidth (w + 1)).msb := by
  have hc : c.toNat < 2 := c.isLt
  have hx := x.isLt
  have hy := y.isLt
  have h2 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ]; omega
  have hb : (c.getLsbD 0).toNat = c.toNat := by
    rcases c.exists_eq_ofBool with ⟨b, rfl⟩; cases b <;> rfl
  congr 1
  simp only [BitVec.carry, BitVec.msb_eq_decide, BitVec.toNat_add, BitVec.toNat_setWidth,
    Nat.add_sub_cancel, hb, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    Nat.mod_eq_of_lt (by omega : c.toNat < 2 ^ (w + 1)), Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ (w + 1)),
    Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ (w + 1))]
  rw [Nat.mod_eq_of_lt (by omega : x.toNat + y.toNat < 2 ^ (w + 1)),
    Nat.mod_eq_of_lt (by omega : x.toNat + y.toNat + c.toNat < 2 ^ (w + 1))]

@[veir_bv_normalize]
theorem isPoison_uaddWithCarry_fst {w : Nat} (x y : Int w) (c : Int 1) :
    (uaddWithCarry x y c).1.isPoison = (x.isPoison || y.isPoison || c.isPoison) := by
  cases x <;> cases y <;> cases c <;> rfl

@[veir_bv_normalize]
theorem isPoison_uaddWithCarry_snd {w : Nat} (x y : Int w) (c : Int 1) :
    (uaddWithCarry x y c).2.isPoison = (x.isPoison || y.isPoison || c.isPoison) := by
  cases x <;> cases y <;> cases c <;> rfl

@[veir_bv_normalize]
theorem getValue_uaddWithCarry_fst {w : Nat} (x y : Int w) (c : Int 1) (h) :
    (uaddWithCarry x y c).1.getValue h = x.getValueD + y.getValueD + c.getValueD.setWidth w := by
  cases x <;> cases y <;> cases c
  all_goals (try (exfalso; have h' := h; rw [isPoison_uaddWithCarry_fst] at h'; simp [Int.isPoison] at h'; done))
  all_goals (try simp only [uaddWithCarry] at h ⊢)
  all_goals (try simp_all [Int.isPoison, Int.getValue, Int.getValueD])
  all_goals first | rfl | (congr 1; exact decide_eq_decide.mpr Iff.rfl)

@[veir_bv_normalize]
theorem getValue_uaddWithCarry_snd {w : Nat} (x y : Int w) (c : Int 1) (h) :
    (uaddWithCarry x y c).2.getValue h =
      BitVec.ofBool (x.getValueD.setWidth (w + 1) + y.getValueD.setWidth (w + 1) +
        c.getValueD.setWidth (w + 1)).msb := by
  cases x <;> cases y <;> cases c
  all_goals (try (exfalso; have h' := h; rw [isPoison_uaddWithCarry_snd] at h'; simp [Int.isPoison] at h'; done))
  all_goals (try simp only [uaddWithCarry, ofBool_carry_eq_msb] at h ⊢)
  all_goals (try simp_all [Int.isPoison, Int.getValue, Int.getValueD])
  all_goals first | rfl | (congr 1; exact decide_eq_decide.mpr Iff.rfl)

@[veir_bv_normalize]
theorem isPoison_usubWithBorrow_fst {w : Nat} (x y : Int w) (b : Int 1) :
    (usubWithBorrow x y b).1.isPoison = (x.isPoison || y.isPoison || b.isPoison) := by
  cases x <;> cases y <;> cases b <;> rfl

@[veir_bv_normalize]
theorem isPoison_usubWithBorrow_snd {w : Nat} (x y : Int w) (b : Int 1) :
    (usubWithBorrow x y b).2.isPoison = (x.isPoison || y.isPoison || b.isPoison) := by
  cases x <;> cases y <;> cases b <;> rfl

@[veir_bv_normalize]
theorem getValue_usubWithBorrow_fst {w : Nat} (x y : Int w) (b : Int 1) (h) :
    (usubWithBorrow x y b).1.getValue h = x.getValueD - y.getValueD - b.getValueD.setWidth w := by
  cases x <;> cases y <;> cases b
  all_goals (try (exfalso; have h' := h; rw [isPoison_usubWithBorrow_fst] at h'; simp [Int.isPoison] at h'; done))
  all_goals (try simp only [usubWithBorrow] at h ⊢)
  all_goals (try simp_all [Int.isPoison, Int.getValue, Int.getValueD])
  all_goals first | rfl | (congr 1; exact decide_eq_decide.mpr Iff.rfl)

@[veir_bv_normalize]
theorem getValue_usubWithBorrow_snd {w : Nat} (x y : Int w) (b : Int 1) (h) :
    (usubWithBorrow x y b).2.getValue h =
      BitVec.ofBool (decide (x.getValueD.setWidth (w + 1) <
        y.getValueD.setWidth (w + 1) + b.getValueD.setWidth (w + 1))) := by
  cases x <;> cases y <;> cases b
  all_goals (try (exfalso; have h' := h; rw [isPoison_usubWithBorrow_snd] at h'; simp [Int.isPoison] at h'; done))
  all_goals (try simp only [usubWithBorrow] at h ⊢)
  all_goals (try simp_all [Int.isPoison, Int.getValue, Int.getValueD, BitVec.ult_eq_decide_lt])
  all_goals first | rfl | (congr 1; exact decide_eq_decide.mpr Iff.rfl)

/-! ### Funnel shift amounts, bits and flags -/

@[veir_bv_normalize]
theorem isPoison_funnelShiftAmount {v : Nat} (w : Nat) (z : Int v) :
    (GMIR.funnelShiftAmount w z).isPoison = z.isPoison := by
  cases z <;> rfl

@[veir_bv_normalize]
theorem getValue_funnelShiftAmount {v : Nat} (w : Nat) (z : Int v) (h) :
    (GMIR.funnelShiftAmount w z).getValue h =
      ((z.getValueD.setWidth (v + w)).umod (BitVec.ofNat (v + w) w)).setWidth w := by
  cases z with
  | poison => simp [GMIR.funnelShiftAmount, Int.isPoison] at h
  | val z =>
    have hz : z.toNat < 2 ^ (v + w) :=
      Nat.lt_of_lt_of_le z.isLt (Nat.pow_le_pow_right (by decide) (by omega))
    have hw : w < 2 ^ (v + w) :=
      Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide) (by omega))
    apply BitVec.eq_of_toNat_eq
    simp [GMIR.funnelShiftAmount, Int.getValue, Int.getValueD, BitVec.toNat_umod,
      Nat.mod_eq_of_lt hz, Nat.mod_eq_of_lt hw]

/-- The top bit as a one-bit vector. -/
@[veir_bv_normalize]
theorem extractLsb'_sub_one_one {n : Nat} (x : BitVec n) :
    BitVec.extractLsb' (n - 1) 1 x = BitVec.ofBool x.msb := by
  ext i hi
  obtain rfl : i = 0 := by omega
  simp [BitVec.msb_eq_getLsbD_last]

@[veir_bv_normalize]
theorem ult_eq_decide_lt' {w : Nat} (x y : BitVec w) : x.ult y = decide (x < y) := rfl

@[veir_bv_normalize] theorem default_nsw : (default : NswNuwProperties).nsw = false := rfl
@[veir_bv_normalize] theorem default_nuw : (default : NswNuwProperties).nuw = false := rfl
@[veir_bv_normalize] theorem default_exact : (default : ExactProperties).exact = false := rfl
@[veir_bv_normalize] theorem default_disjoint : (default : DisjointProperties).disjoint = false := rfl
@[veir_bv_normalize] theorem default_nneg : (default : NnegProperties).nneg = false := rfl

@[veir_bv_normalize]
theorem ofInt_neg_two_pow_sub_one {w : Nat} : BitVec.ofInt w (-2 ^ (w - 1)) = BitVec.intMin w := by
  rw [BitVec.intMin_eq_neg_two_pow]

@[veir_bv_normalize]
theorem ofInt_two_pow_sub_one_sub_one {w : Nat} : BitVec.ofInt w (2 ^ (w - 1) - 1) = BitVec.intMax w := by
  rw [Data.LLVM.intMax_eq_ofInt]

/-- A difference of two widths, as `widthConstant` builds it, as a difference of bit-vectors. -/
@[veir_bv_normalize]
theorem ofInt_natCast_sub_natCast (n a b : Nat) :
    BitVec.ofInt n ((a : _root_.Int) - (b : _root_.Int)) = BitVec.ofNat n a - BitVec.ofNat n b := by
  rw [_root_.Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.ofInt_natCast,
    BitVec.ofInt_natCast, BitVec.sub_eq_add_neg]

/-! ### Properties the widenings clear -/

@[veir_bv_normalize] theorem clearNswNuwProperties_nsw (p : NswNuwProperties) :
    (clearNswNuwProperties p).nsw = false := rfl
@[veir_bv_normalize] theorem clearNswNuwProperties_nuw (p : NswNuwProperties) :
    (clearNswNuwProperties p).nuw = false := rfl
@[veir_bv_normalize] theorem clearDisjointProperties_disjoint (p : DisjointProperties) :
    (clearDisjointProperties p).disjoint = false := rfl

/-- Zero extension without `nneg` is injective on values and keeps poison, so it can be cancelled on
both sides of a refinement. This removes the width `W` from the goal, which matters when `W` is
unbounded, as the result type of a `g_icmp` whose operands are widened. With `nneg` this does not
hold: the extension of a value with its top bit set is poison. -/
@[veir_bv_normalize high]
theorem zext_isRefinedBy_zext {w W : Nat} (x y : Int w) (h : w < W) :
    (x.zext W false h ⊒ y.zext W false h) ↔ x ⊒ y := by
  have hinj : ∀ a b : BitVec w, a.setWidth W = b.setWidth W ↔ a = b := by
    intro a b
    constructor
    · intro hab
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat hab
      have ha : a.toNat < 2 ^ W :=
        Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt h))
      have hb : b.toNat < 2 ^ W :=
        Nat.lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt h))
      simpa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
    · rintro rfl; rfl
  cases x <;> cases y <;> simp [Int.zext, Id.run, isRefinedBy, hinj]

end Normalize

end Veir.Legalization.CTreeProofs.PBV
