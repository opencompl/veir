module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Casting
public import Veir.Dialects.GMIR.Semantics

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect

import Veir.ForLean
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Veir.Dialects.GMIR.Semantics

public section

namespace Veir.Data.LLVM

/--
Prove the correctness of `llvm.add` widening with anyext.
-/
theorem add_widening_32_64 (i i' : LLVM.Int 32) (ext ext' : BitVec 32) (nuw nsw : Bool) :
    LLVM.Int.add i i' nuw nsw ⊒
      LLVM.Int.trunc (LLVM.Int.add
        (LLVM.Int.ext i 64 ext (by grind))
        (LLVM.Int.ext i' 64 ext' (by grind))
        false false
      ) 32 false false (by grind) := by
  veir_bv_decide

/--
Prove the correctness of combining `g_anyext (g_trunc x)` to `x`, at every width and whatever the
`nsw` and `nuw` flags of the `g_trunc`.
-/
theorem anyext_trunc_same (w n : Nat) (h : n < w) (x : LLVM.Int w) (nsw nuw : Bool) :
    ∃ ext : BitVec (w - n), LLVM.Int.ext (LLVM.Int.trunc x n nsw nuw h) w ext h ⊒ x :=
  ⟨x.getValueD.extractLsb' n (w - n), by
    veir_bv_normalize
    simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_append]
    grind⟩

/--
Prove the correctness of combining `g_anyext (g_trunc x)` to a narrower `g_trunc x`, at every
width.
-/
theorem anyext_trunc_narrower (w n m : Nat) (hn : n < m) (hm : m < w) (x : LLVM.Int w)
    (nsw nuw : Bool) :
    ∃ ext : BitVec (m - n),
      LLVM.Int.ext (LLVM.Int.trunc x n nsw nuw (by omega)) m ext hn ⊒
        LLVM.Int.trunc x m false false hm :=
  ⟨x.getValueD.extractLsb' n (m - n), by
    veir_bv_normalize
    simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_append]
    grind⟩

/--
Prove the correctness of combining `g_anyext (g_trunc x)` to a wider `g_anyext x`, at every width
and whatever the high bits `ext'` of the new `g_anyext` are.
-/
theorem anyext_trunc_wider (w n m : Nat) (hn : n < w) (hw : w < m) (x : LLVM.Int w)
    (ext' : BitVec (m - w)) (nsw nuw : Bool) :
    ∃ ext : BitVec (m - n),
      LLVM.Int.ext (LLVM.Int.trunc x n nsw nuw hn) m ext (by omega) ⊒
        LLVM.Int.ext x m ext' hw :=
  ⟨(ext' ++ x.getValueD.extractLsb' n (w - n)).cast (by omega), by
    veir_bv_normalize
    simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_append]
    grind⟩

/--
Prove the correctness of combining `g_anyext (g_anyext x)` to `g_anyext x`, at every width.
-/
theorem anyext_anyext (w n m : Nat) (hn : w < n) (hm : n < m) (x : LLVM.Int w)
    (ext : BitVec (m - w)) :
    ∃ ext₁ : BitVec (n - w), ∃ ext₂ : BitVec (m - n),
      LLVM.Int.ext (LLVM.Int.ext x n ext₁ hn) m ext₂ hm ⊒ LLVM.Int.ext x m ext (by omega) :=
  ⟨ext.extractLsb' 0 (n - w), ext.extractLsb' (n - w) (m - n), by
    veir_bv_normalize
    simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_append]
    grind⟩

/--
Prove the correctness of combining `g_trunc (g_trunc x)` to `g_trunc x`, at every width and whatever
the flags of both `g_trunc`s.
-/
theorem trunc_trunc (w n m : Nat) (hn : n < m) (hm : m < w) (x : LLVM.Int w)
    (nsw nuw nsw' nuw' : Bool) :
    LLVM.Int.trunc (LLVM.Int.trunc x m nsw nuw hm) n nsw' nuw' hn ⊒
      LLVM.Int.trunc x n false false (by omega) := by
  veir_bv_normalize
  simp [BitVec.setWidth_setWidth_of_le _ (Nat.le_of_lt hn)]

/-- Bit `i` of the mask `2 ^ n - 1` is set exactly when `i < n`. -/
private theorem getElem_ofInt_two_pow_sub_one {m n i : Nat} (hi : i < m) :
    (BitVec.ofInt m (2 ^ n - 1))[i] = decide (i < n) := by
  rw [show (2 ^ n - 1 : _root_.Int) = ((2 ^ n - 1 : Nat) : _root_.Int) by
    simp [Int.natCast_sub Nat.one_le_two_pow]]
  simp [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, hi]

/--
Prove the correctness of lowering `g_zext` to a `g_and` of a `g_anyext` with the mask of the source
width, at every width.
-/
theorem zext_and_anyext (n m : Nat) (h : n < m) (x : LLVM.Int n) (nneg : Bool)
    (ext : BitVec (m - n)) :
    LLVM.Int.zext x m nneg h ⊒
      LLVM.Int.and (LLVM.Int.ext x m ext h) (LLVM.Int.constant m (2 ^ n - 1)) := by
  veir_bv_normalize
  simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_append, getElem_ofInt_two_pow_sub_one]
  grind

/-- `x` is refined by its low bits after any extension. -/
private theorem trunc_ext_self {n m : Nat} (h : n < m) (x : LLVM.Int n) (ext : BitVec (m - n)) :
    x ⊒ LLVM.Int.trunc (LLVM.Int.ext x m ext h) n false false h := by
  veir_bv_normalize
  simp [BitVec.eq_of_getElem_eq_iff]
  grind

/--
Prove the correctness of widening the values of `g_select` with `g_anyext`, at every width and
whatever the high bits of the extended values are: the selected value is truncated back.
-/
theorem select_widen_values (n m wc : Nat) (h : n < m) (c : LLVM.Int wc) (x y : LLVM.Int n)
    (ext ext' : BitVec (m - n)) :
    GMIR.selectNonzero c x y ⊒
      LLVM.Int.trunc
        (GMIR.selectNonzero c (LLVM.Int.ext x m ext h) (LLVM.Int.ext y m ext' h))
        n false false h := by
  cases c with
  | poison => simp [GMIR.selectNonzero, LLVM.Int.trunc, Id.run, isRefinedBy]
  | val c =>
    simp only [GMIR.selectNonzero, Id.run]
    split
    · exact trunc_ext_self h x ext
    · exact trunc_ext_self h y ext'

/--
Prove the correctness of widening the condition of `g_select` with `g_zext`, at every width: the
zero-extended condition is nonzero exactly when the condition is.
-/
theorem select_widen_cond (n m w : Nat) (h : n < m) (c : LLVM.Int n) (x y : LLVM.Int w) :
    GMIR.selectNonzero c x y ⊒ GMIR.selectNonzero (LLVM.Int.zext c m false h) x y := by
  cases c with
  | poison => simp [GMIR.selectNonzero, LLVM.Int.zext, Id.run, isRefinedBy]
  | val c =>
    have hz : c.setWidth m = 0#m ↔ c = 0#n := by
      constructor
      · intro hz
        apply BitVec.eq_of_getElem_eq
        intro i hi
        have := congrArg (fun b => b[i]'(by omega)) hz
        simpa [BitVec.getElem_setWidth, hi] using this
      · rintro rfl
        simp
    simp [GMIR.selectNonzero, LLVM.Int.zext, Id.run, hz]

/--
Prove the correctness of combining `g_and (g_icmp p x y), 1` to `g_icmp p x y`, at every width: a
`g_icmp` wider than `i1` is its `i1` comparison zero-extended.
-/
theorem and_icmp_one (m : Nat) (h : 1 < m) (c : LLVM.Int 1) :
    LLVM.Int.zext c m false h ⊒
      LLVM.Int.and (LLVM.Int.zext c m false h) (LLVM.Int.constant m 1) := by
  veir_bv_normalize
  simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_and]
  grind

/-!
## Funnel shifts and rotates

`llvm.intr.fshl`/`llvm.intr.fshr` translate to `g_fshl`/`g_fshr`, or to `g_rotl`/`g_rotr` when both
data operands are the same value. Legalization lowers the funnel shifts, and the rotates other than
the `i64` and `i32` ones, to shifts, as LLVM's `LegalizerHelper::lowerFunnelShiftAsShifts` and
`lowerRotate`. The amount of these operations is read as an unsigned integer modulo the width `w`
(`GMIR.funnelShiftAmount`), and may have another width `k`, which legalization first widens to at
least `w`. The lowerings compute the shift amounts in that width and convert them to `w` bits for
the shifts (`GMIR.shiftAmount`).

The lowerings are proved at every width, from the bits of the results.
-/

/-- `fshl` with an amount `s < w` is `(a << s) | ((b >> 1) >> (w - 1 - s))`. -/
private theorem fshl_bits {w : Nat} (a b : BitVec w) (s : Nat) (hs : s < w) :
    ((a ++ b) <<< s).extractLsb' w w = (a <<< s) ||| ((b >>> 1) >>> (w - 1 - s)) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [BitVec.getLsbD_append, BitVec.getElem_shiftLeft, BitVec.getElem_or,
    BitVec.getElem_ushiftRight, BitVec.getLsbD_ushiftRight]
  by_cases h : i < s
  · simp [h, show w + i - s < w by omega, show 1 + (w - 1 - s + i) = w + i - s by omega,
      show ¬ w + i < s by omega, hi]
  · have e3 : b.getLsbD (1 + (w - 1 - s + i)) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    simp [h, e3, show ¬ (w + i - s < w) by omega, show w + i - s - w = i - s by omega,
      show ¬ w + i < s by omega, BitVec.getLsbD_eq_getElem, show i - s < w by omega, hi]

/-- `fshr` with an amount `s < w` is `((a << 1) << (w - 1 - s)) | (b >> s)`. -/
private theorem fshr_bits {w : Nat} (a b : BitVec w) (s : Nat) (hs : s < w) :
    ((a ++ b) >>> s).truncate w = ((a <<< 1) <<< (w - 1 - s)) ||| (b >>> s) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [BitVec.getLsbD_append, BitVec.getElem_shiftLeft, BitVec.getElem_or,
    BitVec.getElem_ushiftRight, BitVec.getLsbD_ushiftRight, BitVec.getElem_setWidth]
  by_cases h : s + i < w
  · simp [h]; intro _ _; omega
  · have e3 : b.getLsbD (s + i) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    simp [h, e3, show ¬ i < w - 1 - s by omega, show i - (w - 1 - s) ≠ 0 by omega,
      show i - (w - 1 - s) - 1 = s + i - w by omega, BitVec.getLsbD_eq_getElem,
      show s + i - w < w by omega]

/-- The two halves of the `fshl` expansion have no bits in common. -/
private theorem shl_and_lshr_disjoint {w : Nat} (a b : BitVec w) (s : Nat) (hs : s < w) :
    (a <<< s) &&& ((b >>> 1) >>> (w - 1 - s)) = 0 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp [BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight, BitVec.getLsbD_ushiftRight]
  intro _ _; exact BitVec.getLsbD_of_ge _ _ (by omega)

/-- The two halves of the `fshr` expansion have no bits in common. -/
private theorem shl_shl_and_lshr_disjoint {w : Nat} (a b : BitVec w) (s : Nat) (hs : s < w) :
    ((a <<< 1) <<< (w - 1 - s)) &&& (b >>> s) = 0 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp [BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight]
  intro _ _ _; exact BitVec.getLsbD_of_ge _ _ (by omega)

/-- The extra shift by one and the shift by `w - 1 - s` together shift by `w - s`. -/
private theorem shiftLeft_one_shiftLeft {w : Nat} (a : BitVec w) (s : Nat) (hs : s < w) :
    (a <<< 1) <<< (w - 1 - s) = a <<< (w - s) := by
  rw [← BitVec.shiftLeft_add]; congr 1; omega

/-- The extra shift by one and the shift by `w - 1 - s` together shift by `w - s`. -/
private theorem ushiftRight_one_ushiftRight {w : Nat} (a : BitVec w) (s : Nat) (hs : s < w) :
    (a >>> 1) >>> (w - 1 - s) = a >>> (w - s) := by
  rw [← BitVec.shiftRight_add]; congr 1; omega

/-! ### Amounts -/

/-- The constant `-1` is all ones. -/
private theorem ofInt_neg_one (k : Nat) : BitVec.ofInt k (-1) = BitVec.allOnes k := by
  show BitVec.ofInt k (Int.negSucc 0) = _
  rw [BitVec.ofInt_negSucc_eq_not_ofNat]; simp

/-- A nonnegative constant that fits in `k` bits keeps its value. -/
private theorem ofInt_natCast_toNat {k : Nat} (m : Nat) (h : m < 2 ^ k) :
    (BitVec.ofInt k (m : _root_.Int)).toNat = m := by
  rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The `k`-bit mask `2^n - 1`, for `n ≤ k`, keeps the amount modulo `2^n`. -/
private theorem toNat_and_mask {n k : Nat} (hk : n ≤ k) (z : BitVec k) :
    (z &&& BitVec.ofInt k (((2 ^ n : Nat) : _root_.Int) - 1)).toNat = z.toNat % 2 ^ n := by
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hle : 2 ^ n ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  have : BitVec.ofInt k (((2 ^ n : Nat) : _root_.Int) - 1) = BitVec.ofNat k (2 ^ n - 1) := by
    rw [show (((2 ^ n : Nat) : _root_.Int) - 1) = ((2 ^ n - 1 : Nat) : _root_.Int) by omega]
    exact BitVec.ofInt_natCast ..
  rw [this, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.and_two_pow_sub_one_eq_mod]

/-- `~z & (2^n - 1)` is `2^n - 1 - z % 2^n`. -/
private theorem toNat_not_and_mask {n k : Nat} (hk : n ≤ k) (z : BitVec k) :
    ((z ^^^ BitVec.ofInt k (-1)) &&& BitVec.ofInt k (((2 ^ n : Nat) : _root_.Int) - 1)).toNat =
      2 ^ n - 1 - z.toNat % 2 ^ n := by
  rw [ofInt_neg_one, BitVec.xor_allOnes, toNat_and_mask hk, ← BitVec.toNat_setWidth,
    BitVec.setWidth_not hk, BitVec.toNat_not, BitVec.toNat_setWidth]

/-- `-z & (2^n - 1)` is `(2^n - z % 2^n) % 2^n`. -/
private theorem toNat_neg_and_mask {n k : Nat} (hk : n ≤ k) (z : BitVec k) :
    ((BitVec.ofInt k 0 - z) &&& BitVec.ofInt k (((2 ^ n : Nat) : _root_.Int) - 1)).toNat =
      (2 ^ n - z.toNat % 2 ^ n) % 2 ^ n := by
  rw [show BitVec.ofInt k 0 - z = -z by simp, toNat_and_mask hk, ← BitVec.toNat_setWidth,
    BitVec.setWidth_neg_of_le hk, BitVec.toNat_neg, BitVec.toNat_setWidth]

/-! ### Operations -/

/-- A `g_shl` by an amount below the width shifts by its value. -/
private theorem shl_shiftAmount {w k : Nat} (x : BitVec w) (v : BitVec k) (h : v.toNat < w) :
    Int.shl (.val x) (GMIR.shiftAmount w (.val v)) = .val (x <<< v.toNat) := by
  have h2 : v.toNat < 2 ^ w := Nat.lt_trans h Nat.lt_two_pow_self
  have h3 : w < 2 ^ w := Nat.lt_two_pow_self
  simp [GMIR.shiftAmount, h, Int.shl, Id.run, BitVec.le_def, Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt h3]

/-- A `g_lshr` by an amount below the width shifts by its value. -/
private theorem lshr_shiftAmount {w k : Nat} (x : BitVec w) (v : BitVec k) (h : v.toNat < w) :
    Int.lshr (.val x) (GMIR.shiftAmount w (.val v)) = .val (x >>> v.toNat) := by
  have h2 : v.toNat < 2 ^ w := Nat.lt_trans h Nat.lt_two_pow_self
  have h3 : w < 2 ^ w := Nat.lt_two_pow_self
  simp [GMIR.shiftAmount, h, Int.lshr, Id.run, BitVec.le_def, Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt h3]

/-- A disjoint `g_or` of values without common bits is their `or`. -/
private theorem or_disjoint_val {w : Nat} (a b : BitVec w) (h : a &&& b = 0) :
    Int.or (.val a) (.val b) true = .val (a ||| b) := by
  simp [Int.or, Id.run, h]

/-- A `g_fshl` shifts by its amount modulo the width. -/
private theorem fshl_funnelShiftAmount {w k : Nat} (a b : BitVec w) (c : BitVec k) :
    Int.fshl (.val a) (.val b) (GMIR.funnelShiftAmount w (.val c)) =
      .val (((a ++ b) <<< (c.toNat % w)).extractLsb' w w) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [Int.fshl, GMIR.funnelShiftAmount, Id.run]
  · have : c.toNat % w < 2 ^ w := Nat.lt_trans (Nat.mod_lt _ hw) Nat.lt_two_pow_self
    simp [Int.fshl, GMIR.funnelShiftAmount, Id.run, Nat.mod_eq_of_lt this]

/-- A `g_fshr` shifts by its amount modulo the width. -/
private theorem fshr_funnelShiftAmount {w k : Nat} (a b : BitVec w) (c : BitVec k) :
    Int.fshr (.val a) (.val b) (GMIR.funnelShiftAmount w (.val c)) =
      .val (((a ++ b) >>> (c.toNat % w)).truncate w) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [Int.fshr, GMIR.funnelShiftAmount, Id.run]; exact Subsingleton.elim _ _
  · have : c.toNat % w < 2 ^ w := Nat.lt_trans (Nat.mod_lt _ hw) Nat.lt_two_pow_self
    simp [Int.fshr, GMIR.funnelShiftAmount, Id.run, Nat.mod_eq_of_lt this]

/-! ### Lowerings -/

/--
Prove the correctness of lowering `g_fshl x, y, z` of a power-of-two width `w = 2^n ≥ 2` to
`(x << (z & (w-1))) | ((y >> 1) >> (~z & (w-1)))` (`lowerFunnelShiftGeneral true true`), for any
amount width `k ≥ n`. The `g_or` is disjoint.
-/
theorem fshl_lower_pow2 {n k : Nat} (hn : 1 ≤ n) (hk : n ≤ k) (x y : Int (2 ^ n)) (z : Int k) :
    Int.fshl x y (GMIR.funnelShiftAmount (2 ^ n) z) ⊒
      Int.or
        (Int.shl x (GMIR.shiftAmount _
          (Int.and z (Int.constant k (((2 ^ n : Nat) : _root_.Int) - 1)))))
        (Int.lshr (Int.lshr y (GMIR.shiftAmount _ (Int.constant k 1)))
          (GMIR.shiftAmount _ (Int.and (Int.xor z (Int.constant k (-1)))
            (Int.constant k (((2 ^ n : Nat) : _root_.Int) - 1)))))
        true := by
  cases x with
  | poison => exact poison_isRefinedBy _
  | val a =>
  cases y with
  | poison => exact poison_isRefinedBy _
  | val b =>
  cases z with
  | poison => exact poison_isRefinedBy _
  | val c =>
  have hs : c.toNat % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
  have h2n : 2 ≤ 2 ^ n := by
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) hn; simpa using this
  have h2k : 2 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) (Nat.le_trans hn hk); simpa using this
  have h1 : (BitVec.ofInt k 1).toNat = 1 := ofInt_natCast_toNat 1 (by omega)
  simp only [Int.constant, Int.and, Int.xor, Id.run]
  rw [fshl_funnelShiftAmount, shl_shiftAmount _ _ (by rw [toNat_and_mask hk]; exact hs),
    lshr_shiftAmount _ _ (by rw [h1]; omega),
    lshr_shiftAmount _ _ (by rw [toNat_not_and_mask hk]; omega),
    toNat_and_mask hk, toNat_not_and_mask hk, h1,
    or_disjoint_val _ _ (shl_and_lshr_disjoint _ _ _ hs), fshl_bits _ _ _ hs]
  exact isRefinedBy_refl _

/--
Prove the correctness of lowering `g_fshr x, y, z` of a power-of-two width `w = 2^n ≥ 2` to
`((x << 1) << (~z & (w-1))) | (y >> (z & (w-1)))` (`lowerFunnelShiftGeneral false true`), for any
amount width `k ≥ n`. The `g_or` is disjoint.
-/
theorem fshr_lower_pow2 {n k : Nat} (hn : 1 ≤ n) (hk : n ≤ k) (x y : Int (2 ^ n)) (z : Int k) :
    Int.fshr x y (GMIR.funnelShiftAmount (2 ^ n) z) ⊒
      Int.or
        (Int.shl (Int.shl x (GMIR.shiftAmount _ (Int.constant k 1)))
          (GMIR.shiftAmount _ (Int.and (Int.xor z (Int.constant k (-1)))
            (Int.constant k (((2 ^ n : Nat) : _root_.Int) - 1)))))
        (Int.lshr y (GMIR.shiftAmount _
          (Int.and z (Int.constant k (((2 ^ n : Nat) : _root_.Int) - 1)))))
        true := by
  cases x with
  | poison => exact poison_isRefinedBy _
  | val a =>
  cases y with
  | poison => exact poison_isRefinedBy _
  | val b =>
  cases z with
  | poison => exact poison_isRefinedBy _
  | val c =>
  have hs : c.toNat % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
  have h2n : 2 ≤ 2 ^ n := by
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) hn; simpa using this
  have h2k : 2 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) (Nat.le_trans hn hk); simpa using this
  have h1 : (BitVec.ofInt k 1).toNat = 1 := ofInt_natCast_toNat 1 (by omega)
  simp only [Int.constant, Int.and, Int.xor, Id.run]
  rw [fshr_funnelShiftAmount, shl_shiftAmount _ _ (by rw [h1]; omega),
    shl_shiftAmount _ _ (by rw [toNat_not_and_mask hk]; omega),
    lshr_shiftAmount _ _ (by rw [toNat_and_mask hk]; exact hs),
    toNat_not_and_mask hk, toNat_and_mask hk, h1,
    or_disjoint_val _ _ (shl_shl_and_lshr_disjoint _ _ _ hs), fshr_bits _ _ _ hs]
  exact isRefinedBy_refl _

/-! Non-power-of-two widths: `z % w` with an unsigned remainder. -/

/-- The `g_urem` of an amount by the width `w` is the amount modulo `w`. -/
private theorem urem_width {w k : Nat} (hw : 0 < w) (hk : w ≤ k) (c : BitVec k) :
    Int.urem (.val c) (Int.constant k (w : _root_.Int)) = .val (c % BitVec.ofInt k w) ∧
      (c % BitVec.ofInt k (w : _root_.Int)).toNat = c.toNat % w := by
  have hlt : w < 2 ^ k := Nat.lt_of_le_of_lt hk Nat.lt_two_pow_self
  have hc : (BitVec.ofInt k (w : _root_.Int)).toNat = w := ofInt_natCast_toNat w hlt
  have hne : BitVec.ofNat k w ≠ 0#k := by
    intro h; have := congrArg BitVec.toNat h; simp [Nat.mod_eq_of_lt hlt] at this; omega
  refine ⟨?_, ?_⟩
  · simp [Int.urem, Int.constant, Id.run, hne]
  · rw [BitVec.toNat_umod, hc]

/-- The `g_sub` of an amount below `w` from `w - 1` does not wrap. -/
private theorem sub_width {w k : Nat} (hw : 0 < w) (hk : w ≤ k) (u : BitVec k) (hu : u.toNat < w) :
    Data.LLVM.Int.sub (Int.constant k ((w : _root_.Int) - 1)) (.val u) =
        .val (BitVec.ofInt k ((w : _root_.Int) - 1) - u) ∧
      (BitVec.ofInt k ((w : _root_.Int) - 1) - u).toNat = w - 1 - u.toNat := by
  have hlt : w < 2 ^ k := Nat.lt_of_le_of_lt hk Nat.lt_two_pow_self
  have hc : (BitVec.ofInt k ((w : _root_.Int) - 1)).toNat = w - 1 := by
    rw [show (w : _root_.Int) - 1 = ((w - 1 : Nat) : _root_.Int) by omega]
    exact ofInt_natCast_toNat _ (by omega)
  refine ⟨by simp [Data.LLVM.Int.sub, Int.constant, Id.run], ?_⟩
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hc]; omega), hc]

/--
Prove the correctness of lowering `g_fshl x, y, z` of any width `w ≥ 2` to
`(x << (z % w)) | ((y >> 1) >> ((w-1) - (z % w)))` (`lowerFunnelShiftGeneral true false`, which
the legalizer uses for widths that are not powers of two), for any amount width `k ≥ w`.
-/
theorem fshl_lower_general {w k : Nat} (hw : 2 ≤ w) (hk : w ≤ k) (x y : Int w) (z : Int k) :
    Int.fshl x y (GMIR.funnelShiftAmount w z) ⊒
      Int.or
        (Int.shl x (GMIR.shiftAmount _ (Int.urem z (Int.constant k (w : _root_.Int)))))
        (Int.lshr (Int.lshr y (GMIR.shiftAmount _ (Int.constant k 1)))
          (GMIR.shiftAmount _ (Data.LLVM.Int.sub (Int.constant k ((w : _root_.Int) - 1))
            (Int.urem z (Int.constant k (w : _root_.Int))))))
        true := by
  cases x with
  | poison => exact poison_isRefinedBy _
  | val a =>
  cases y with
  | poison => exact poison_isRefinedBy _
  | val b =>
  cases z with
  | poison => exact poison_isRefinedBy _
  | val c =>
  have hs : c.toNat % w < w := Nat.mod_lt _ (by omega)
  have h1 : (BitVec.ofInt k 1).toNat = 1 :=
    ofInt_natCast_toNat 1 (by have := @Nat.lt_two_pow_self k; omega)
  obtain ⟨hu, hut⟩ := urem_width (by omega) hk c
  obtain ⟨hsub, hsubt⟩ := sub_width (by omega) hk _ (by rw [hut]; exact hs)
  rw [hu, hsub]
  simp only [Int.constant]
  rw [fshl_funnelShiftAmount, shl_shiftAmount _ _ (by rw [hut]; exact hs),
    lshr_shiftAmount _ _ (by rw [h1]; omega),
    lshr_shiftAmount _ _ (by rw [hsubt]; omega),
    hsubt, hut, h1,
    or_disjoint_val _ _ (shl_and_lshr_disjoint _ _ _ hs), fshl_bits _ _ _ hs]
  exact isRefinedBy_refl _

/--
Prove the correctness of lowering `g_fshr x, y, z` of any width `w ≥ 2` to
`((x << 1) << ((w-1) - (z % w))) | (y >> (z % w))` (`lowerFunnelShiftGeneral false false`), for
any amount width `k ≥ w`.
-/
theorem fshr_lower_general {w k : Nat} (hw : 2 ≤ w) (hk : w ≤ k) (x y : Int w) (z : Int k) :
    Int.fshr x y (GMIR.funnelShiftAmount w z) ⊒
      Int.or
        (Int.shl (Int.shl x (GMIR.shiftAmount _ (Int.constant k 1)))
          (GMIR.shiftAmount _ (Data.LLVM.Int.sub (Int.constant k ((w : _root_.Int) - 1))
            (Int.urem z (Int.constant k (w : _root_.Int))))))
        (Int.lshr y (GMIR.shiftAmount _ (Int.urem z (Int.constant k (w : _root_.Int)))))
        true := by
  cases x with
  | poison => exact poison_isRefinedBy _
  | val a =>
  cases y with
  | poison => exact poison_isRefinedBy _
  | val b =>
  cases z with
  | poison => exact poison_isRefinedBy _
  | val c =>
  have hs : c.toNat % w < w := Nat.mod_lt _ (by omega)
  have h1 : (BitVec.ofInt k 1).toNat = 1 :=
    ofInt_natCast_toNat 1 (by have := @Nat.lt_two_pow_self k; omega)
  obtain ⟨hu, hut⟩ := urem_width (by omega) hk c
  obtain ⟨hsub, hsubt⟩ := sub_width (by omega) hk _ (by rw [hut]; exact hs)
  rw [hu, hsub]
  simp only [Int.constant]
  rw [fshr_funnelShiftAmount, shl_shiftAmount _ _ (by rw [h1]; omega),
    shl_shiftAmount _ _ (by rw [hsubt]; omega),
    lshr_shiftAmount _ _ (by rw [hut]; exact hs),
    hsubt, hut, h1,
    or_disjoint_val _ _ (shl_shl_and_lshr_disjoint _ _ _ hs), fshr_bits _ _ _ hs]
  exact isRefinedBy_refl _

/-! Constant amounts. -/

/--
Prove the correctness of lowering `g_fshl x, y, C` by a constant whose value `s = C % w` is not
zero to `(x << s) | (y >> (w - s))` (`lowerFunnelShiftConstant true`), for any amount width `k ≥ w`.
-/
theorem fshl_lower_constant {w k : Nat} (hw : 0 < w) (hk : w ≤ k) (x y : Int w) (c : BitVec k)
    (hc : c.toNat % w ≠ 0) :
    Int.fshl x y (GMIR.funnelShiftAmount w (.val c)) ⊒
      Int.or
        (Int.shl x (GMIR.shiftAmount _ (Int.constant k ((c.toNat % w : Nat) : _root_.Int))))
        (Int.lshr y (GMIR.shiftAmount _ (Int.constant k ((w - c.toNat % w : Nat) : _root_.Int))))
        true := by
  cases x with
  | poison => exact poison_isRefinedBy _
  | val a =>
  cases y with
  | poison => exact poison_isRefinedBy _
  | val b =>
  have hs : c.toNat % w < w := Nat.mod_lt _ hw
  have hlt : w < 2 ^ k := Nat.lt_of_le_of_lt hk Nat.lt_two_pow_self
  have hdis := shl_and_lshr_disjoint a b _ hs
  rw [ushiftRight_one_ushiftRight _ _ hs] at hdis
  simp only [Int.constant]
  rw [fshl_funnelShiftAmount,
    shl_shiftAmount _ _ (by rw [ofInt_natCast_toNat _ (by omega)]; exact hs),
    lshr_shiftAmount _ _ (by rw [ofInt_natCast_toNat _ (by omega)]; omega),
    ofInt_natCast_toNat _ (by omega), ofInt_natCast_toNat _ (by omega),
    fshl_bits _ _ _ hs, ushiftRight_one_ushiftRight _ _ hs,
    or_disjoint_val _ _ hdis]
  exact isRefinedBy_refl _

/--
Prove the correctness of lowering `g_fshr x, y, C` by a constant whose value `s = C % w` is not
zero to `(x << (w - s)) | (y >> s)` (`lowerFunnelShiftConstant false`), for any amount width `k ≥ w`.
-/
theorem fshr_lower_constant {w k : Nat} (hw : 0 < w) (hk : w ≤ k) (x y : Int w) (c : BitVec k)
    (hc : c.toNat % w ≠ 0) :
    Int.fshr x y (GMIR.funnelShiftAmount w (.val c)) ⊒
      Int.or
        (Int.shl x (GMIR.shiftAmount _ (Int.constant k ((w - c.toNat % w : Nat) : _root_.Int))))
        (Int.lshr y (GMIR.shiftAmount _ (Int.constant k ((c.toNat % w : Nat) : _root_.Int))))
        true := by
  cases x with
  | poison => exact poison_isRefinedBy _
  | val a =>
  cases y with
  | poison => exact poison_isRefinedBy _
  | val b =>
  have hs : c.toNat % w < w := Nat.mod_lt _ hw
  have hlt : w < 2 ^ k := Nat.lt_of_le_of_lt hk Nat.lt_two_pow_self
  have hdis := shl_shl_and_lshr_disjoint a b _ hs
  rw [shiftLeft_one_shiftLeft _ _ hs] at hdis
  simp only [Int.constant]
  rw [fshr_funnelShiftAmount,
    shl_shiftAmount _ _ (by rw [ofInt_natCast_toNat _ (by omega)]; omega),
    lshr_shiftAmount _ _ (by rw [ofInt_natCast_toNat _ (by omega)]; exact hs),
    ofInt_natCast_toNat _ (by omega), ofInt_natCast_toNat _ (by omega),
    fshr_bits _ _ _ hs, shiftLeft_one_shiftLeft _ _ hs,
    or_disjoint_val _ _ hdis]
  exact isRefinedBy_refl _

/-! Width one. -/

/-- Prove the correctness of lowering the `i1` `g_fshl x, y, z` to `x`
(`lowerFunnelShiftWidthOne true`). -/
theorem fshl_lower_width_one {k : Nat} (x y : Int 1) (z : Int k) :
    Int.fshl x y (GMIR.funnelShiftAmount 1 z) ⊒ x := by
  cases x with
  | poison => exact poison_isRefinedBy _
  | val a =>
  cases y with
  | poison => exact poison_isRefinedBy _
  | val b =>
  cases z with
  | poison => exact poison_isRefinedBy _
  | val c =>
  rw [fshl_funnelShiftAmount, Nat.mod_one, BitVec.shiftLeft_zero]
  rw [BitVec.extractLsb'_append_eq_left]; exact isRefinedBy_refl _

/-- Prove the correctness of lowering the `i1` `g_fshr x, y, z` to `y`
(`lowerFunnelShiftWidthOne false`). -/
theorem fshr_lower_width_one {k : Nat} (x y : Int 1) (z : Int k) :
    Int.fshr x y (GMIR.funnelShiftAmount 1 z) ⊒ y := by
  cases x with
  | poison => exact poison_isRefinedBy _
  | val a =>
  cases y with
  | poison => exact poison_isRefinedBy _
  | val b =>
  cases z with
  | poison => exact poison_isRefinedBy _
  | val c =>
  rw [fshr_funnelShiftAmount, Nat.mod_one, BitVec.ushiftRight_zero]
  rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_append]; simp [isRefinedBy_refl]

/-! Rotates. -/

/-- A rotate left by `s < w` is `(a << s) | (a >> ((w - s) % w))`. -/
private theorem rotl_bits {w : Nat} (a : BitVec w) (s : Nat) (hs : s < w) :
    ((a ++ a) <<< s).extractLsb' w w = (a <<< s) ||| (a >>> ((w - s) % w)) := by
  rw [fshl_bits _ _ _ hs]
  rcases Nat.eq_zero_or_pos s with rfl | h0
  · rw [← BitVec.shiftRight_add, BitVec.ushiftRight_eq_zero (by omega)]; simp
  · rw [ushiftRight_one_ushiftRight _ _ hs, Nat.mod_eq_of_lt (by omega)]

/-- A rotate right by `s < w` is `(a >> s) | (a << ((w - s) % w))`. -/
private theorem rotr_bits {w : Nat} (a : BitVec w) (s : Nat) (hs : s < w) :
    ((a ++ a) >>> s).truncate w = (a >>> s) ||| (a <<< ((w - s) % w)) := by
  rw [fshr_bits _ _ _ hs, BitVec.or_comm]
  rcases Nat.eq_zero_or_pos s with rfl | h0
  · rw [← BitVec.shiftLeft_add, BitVec.shiftLeft_eq_zero (by omega)]; simp
  · rw [shiftLeft_one_shiftLeft _ _ hs, Nat.mod_eq_of_lt (by omega)]

/-- A `g_or` of values is their `or`. -/
private theorem or_val {w : Nat} (a b : BitVec w) : Int.or (.val a) (.val b) = .val (a ||| b) := by
  simp [Int.or, Id.run]

/-- `g_or` is commutative, whether it is disjoint or not. -/
private theorem or_comm' {w : Nat} (x y : Int w) (d : Bool) : Int.or x y d = Int.or y x d := by
  cases x <;> cases y <;> simp [Int.or, Id.run, BitVec.or_comm, BitVec.and_comm]

/--
Prove the correctness of lowering `g_rotl x, z` of a power-of-two width `w = 2^n` to
`(x << (z & (w-1))) | (x >> (-z & (w-1)))` (`lowerRotateGeneral true true`), for any amount width
`k ≥ n`. The `g_or` is not disjoint: both shifts are by zero when `z % w` is.
-/
theorem rotl_lower_pow2 {n k : Nat} (hk : n ≤ k) (x : Int (2 ^ n)) (z : Int k) :
    GMIR.rotl x z ⊒
      Int.or
        (Int.shl x (GMIR.shiftAmount _
          (Int.and z (Int.constant k (((2 ^ n : Nat) : _root_.Int) - 1)))))
        (Int.lshr x (GMIR.shiftAmount _
          (Int.and (Data.LLVM.Int.sub (Int.constant k 0) z)
            (Int.constant k (((2 ^ n : Nat) : _root_.Int) - 1))))) := by
  cases x with
  | poison => exact poison_isRefinedBy _
  | val a =>
  cases z with
  | poison => exact poison_isRefinedBy _
  | val c =>
  have hs : c.toNat % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
  have hr : (2 ^ n - c.toNat % 2 ^ n) % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
  have hsub : Data.LLVM.Int.sub (Int.constant k 0) (.val c) = .val (BitVec.ofInt k 0 - c) := by
    simp [Data.LLVM.Int.sub, Int.constant, Id.run]
  rw [hsub]
  simp only [GMIR.rotl, Int.constant, Int.and, Id.run]
  rw [fshl_funnelShiftAmount, shl_shiftAmount _ _ (by rw [toNat_and_mask hk]; exact hs),
    lshr_shiftAmount _ _ (by rw [toNat_neg_and_mask hk]; exact hr),
    toNat_neg_and_mask hk, toNat_and_mask hk, or_val, rotl_bits _ _ hs]
  exact isRefinedBy_refl _

/--
Prove the correctness of lowering `g_rotr x, z` of a power-of-two width `w = 2^n` to
`(x >> (z & (w-1))) | (x << (-z & (w-1)))` (`lowerRotateGeneral false true`), for any amount width
`k ≥ n`.
-/
theorem rotr_lower_pow2 {n k : Nat} (hk : n ≤ k) (x : Int (2 ^ n)) (z : Int k) :
    GMIR.rotr x z ⊒
      Int.or
        (Int.lshr x (GMIR.shiftAmount _
          (Int.and z (Int.constant k (((2 ^ n : Nat) : _root_.Int) - 1)))))
        (Int.shl x (GMIR.shiftAmount _
          (Int.and (Data.LLVM.Int.sub (Int.constant k 0) z)
            (Int.constant k (((2 ^ n : Nat) : _root_.Int) - 1))))) := by
  cases x with
  | poison => exact poison_isRefinedBy _
  | val a =>
  cases z with
  | poison => exact poison_isRefinedBy _
  | val c =>
  have hs : c.toNat % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
  have hr : (2 ^ n - c.toNat % 2 ^ n) % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
  have hsub : Data.LLVM.Int.sub (Int.constant k 0) (.val c) = .val (BitVec.ofInt k 0 - c) := by
    simp [Data.LLVM.Int.sub, Int.constant, Id.run]
  rw [hsub]
  simp only [GMIR.rotr, Int.constant, Int.and, Id.run]
  rw [fshr_funnelShiftAmount, lshr_shiftAmount _ _ (by rw [toNat_and_mask hk]; exact hs),
    shl_shiftAmount _ _ (by rw [toNat_neg_and_mask hk]; exact hr),
    toNat_neg_and_mask hk, toNat_and_mask hk, or_val, rotr_bits _ _ hs]
  exact isRefinedBy_refl _

/--
Prove the correctness of lowering `g_rotl x, z` of any width `w ≥ 2` to
`(x << (z % w)) | ((x >> 1) >> ((w-1) - (z % w)))` (`lowerRotateGeneral true false`): the general
`g_fshl` lowering with both data operands `x`.
-/
theorem rotl_lower_general {w k : Nat} (hw : 2 ≤ w) (hk : w ≤ k) (x : Int w) (z : Int k) :
    GMIR.rotl x z ⊒
      Int.or
        (Int.shl x (GMIR.shiftAmount _ (Int.urem z (Int.constant k (w : _root_.Int)))))
        (Int.lshr (Int.lshr x (GMIR.shiftAmount _ (Int.constant k 1)))
          (GMIR.shiftAmount _ (Data.LLVM.Int.sub (Int.constant k ((w : _root_.Int) - 1))
            (Int.urem z (Int.constant k (w : _root_.Int))))))
        true :=
  fshl_lower_general hw hk x x z

/--
Prove the correctness of lowering `g_rotr x, z` of any width `w ≥ 2` to
`(x >> (z % w)) | ((x << 1) << ((w-1) - (z % w)))` (`lowerRotateGeneral false false`).
-/
theorem rotr_lower_general {w k : Nat} (hw : 2 ≤ w) (hk : w ≤ k) (x : Int w) (z : Int k) :
    GMIR.rotr x z ⊒
      Int.or
        (Int.lshr x (GMIR.shiftAmount _ (Int.urem z (Int.constant k (w : _root_.Int)))))
        (Int.shl (Int.shl x (GMIR.shiftAmount _ (Int.constant k 1)))
          (GMIR.shiftAmount _ (Data.LLVM.Int.sub (Int.constant k ((w : _root_.Int) - 1))
            (Int.urem z (Int.constant k (w : _root_.Int))))))
        true := by
  rw [or_comm']; exact fshr_lower_general hw hk x x z

/-! Widening the amount, and translating from LLVM. -/

/--
Prove the correctness of widening the amount of a funnel shift or rotate with `g_zext`
(`widenScalar?` on type group 1): the amount is unsigned, so its value does not change.
-/
theorem funnelShiftAmount_zext {w k m : Nat} (h : k < m) (z : Int k) :
    GMIR.funnelShiftAmount w (Data.LLVM.Int.zext z m false h) = GMIR.funnelShiftAmount w z := by
  cases z with
  | poison => rfl
  | val c =>
    have : c.toNat < 2 ^ m := Nat.lt_of_lt_of_le c.isLt (Nat.pow_le_pow_right (by omega) (by omega))
    simp [Data.LLVM.Int.zext, GMIR.funnelShiftAmount, Id.run, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt this]

/-- Prove the correctness of translating `llvm.intr.fshl` to `g_fshl`. -/
theorem fshl_translate {w : Nat} (x y z : Int w) :
    Int.fshl x y z ⊒ Int.fshl x y (GMIR.funnelShiftAmount w z) := by
  rw [GMIR.fshl_funnelShiftAmount_self]; exact isRefinedBy_refl _

/-- Prove the correctness of translating `llvm.intr.fshr` to `g_fshr`. -/
theorem fshr_translate {w : Nat} (x y z : Int w) :
    Int.fshr x y z ⊒ Int.fshr x y (GMIR.funnelShiftAmount w z) := by
  rw [GMIR.fshr_funnelShiftAmount_self]; exact isRefinedBy_refl _

/-- Prove the correctness of translating `llvm.intr.fshl x, x, z` to `g_rotl x, z`. -/
theorem rotl_translate {w : Nat} (x z : Int w) : Int.fshl x x z ⊒ GMIR.rotl x z := by
  rw [GMIR.rotl_eq_fshl]; exact isRefinedBy_refl _

/-- Prove the correctness of translating `llvm.intr.fshr x, x, z` to `g_rotr x, z`. -/
theorem rotr_translate {w : Nat} (x z : Int w) : Int.fshr x x z ⊒ GMIR.rotr x z := by
  rw [GMIR.rotr_eq_fshr]; exact isRefinedBy_refl _

end Veir.Data.LLVM

end
