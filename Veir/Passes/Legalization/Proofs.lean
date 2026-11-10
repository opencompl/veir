module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Casting
public import Veir.Dialects.GMIR.Semantics
public import Veir.Dialects.GMIR_RISCV.Semantics

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect

import Veir.ForLean
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Veir.Dialects.GMIR.Semantics
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR_RISCV.Semantics

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

/--
Prove the correctness of widening `g_poison`: truncating a wide poison, whatever the `nsw` and
`nuw` flags, refines the narrow poison.
-/
theorem poison_widening {w n : Nat} (h : n < w) (nsw nuw : Bool) :
    (LLVM.Int.poison : LLVM.Int n) ⊒ LLVM.Int.trunc (LLVM.Int.poison : LLVM.Int w) n nsw nuw h :=
  poison_isRefinedBy _

/--
Prove `combineExtOfTruncOfConstant true` at every width: truncating a constant that fits in the
narrow signed range and sign-extending it back refines to the original constant, whatever the
`nsw` and `nuw` flags of the truncation.
-/
theorem sext_trunc_constant {w n : Nat} (h : n < w) (hn : 0 < n)
    (c : BitVec w) (hlo : -2 ^ (n - 1) ≤ c.toInt) (hhi : c.toInt < 2 ^ (n - 1))
    (nsw nuw : Bool) :
    LLVM.Int.sext (LLVM.Int.trunc (.val c) n nsw nuw h) w h ⊒ .val c := by
  veir_bv_normalize
  intros
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (Nat.le_of_lt h),
    ← BitVec.signExtend_eq_setWidth_of_le c (Nat.le_of_lt h)]
  exact BitVec.toInt_ofInt_eq_self hn hlo hhi

/--
Prove `combineExtOfTruncOfConstant false` at every width: truncating a constant that fits in the
narrow unsigned range and zero-extending it back refines to the original constant, whatever the
truncation flags and the extension's `nneg` flag.
-/
theorem zext_trunc_constant {w n : Nat} (h : n < w)
    (c : BitVec w) (hfit : c.toNat < 2 ^ n) (nsw nuw nneg : Bool) :
    LLVM.Int.zext (LLVM.Int.trunc (.val c) n nsw nuw h) w nneg h ⊒ .val c := by
  veir_bv_normalize
  intros
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth_of_le (Nat.le_of_lt h), Nat.mod_eq_of_lt hfit]

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
Prove the correctness of widening a block argument (`widenBlockArguments`): whatever high bits the
`g_anyext` on each branch chooses, the `g_trunc` at the start of the block recovers the value.
-/
theorem block_argument_widening (n m : Nat) (h : n < m) (x : LLVM.Int n) (ext : BitVec (m - n)) :
    x ⊒ LLVM.Int.trunc (LLVM.Int.ext x m ext h) n false false h :=
  trunc_ext_self h x ext

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

/--
A widened `g_icmp` result is poison, zero or one: apply this to `LLVM.Int.icmp x y pred`.
These are the nonconstant arms matched by `matchBoolArm`; the constant arms are zero or one
directly.
-/
theorem zext_i1_eq_poison_or_zero_or_one {w : Nat} (h : 1 < w) (c : LLVM.Int 1) :
    LLVM.Int.zext c w false h = .poison ∨
    LLVM.Int.zext c w false h = .val 0#w ∨
    LLVM.Int.zext c w false h = .val 1#w := by
  cases c with
  | poison => simp [LLVM.Int.zext, Id.run]
  | val c =>
    rcases BitVec.eq_zero_or_eq_one c with rfl | rfl <;>
      simp [LLVM.Int.zext, Id.run,
        BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide : 0 < 1)]

/--
Prove all four `redundant_and_select_pattern` arm combinations at every width, for any mask with
its low bit set. The hypotheses admit poison from a comparison, including on an unselected arm;
`zext_i1_eq_poison_or_zero_or_one` supplies them for widened comparisons.
-/
theorem and_select_bool {w wc : Nat} (c : LLVM.Int wc) (t f : LLVM.Int w)
    (mask : BitVec w) (hmask : mask.toNat % 2 = 1)
    (ht : t = .poison ∨ t = .val 0#w ∨ t = .val 1#w)
    (hf : f = .poison ∨ f = .val 0#w ∨ f = .val 1#w) :
    LLVM.Int.and (GMIR.selectNonzero c t f) (.val mask) = GMIR.selectNonzero c t f := by
  have hone : 1#w &&& mask = 1#w := by
    apply BitVec.eq_of_toNat_eq
    cases w <;> simp_all
  cases c with
  | poison => simp [GMIR.selectNonzero, LLVM.Int.and, Id.run]
  | val c =>
    rcases ht with rfl | rfl | rfl <;> rcases hf with rfl | rfl | rfl <;>
      by_cases hc : c = 0#wc <;> simp [GMIR.selectNonzero, LLVM.Int.and, Id.run, hone, hc]

/-! ### Power-of-two division combines

The combines are proved for every width `w`. The divisor is the constant `±2^k`, and the created
shift amounts are the constants `k`, `w - 1` and `w - k`.
-/

/-- Prove the correctness of `udiv_by_pow2_pattern`, whatever the `exact` flag. -/
theorem udiv_by_pow2 {w : Nat} (x : LLVM.Int w) (k : Nat) (hk : k < w) (exact : Bool) :
    LLVM.Int.udiv x (LLVM.Int.val (BitVec.twoPow w k)) exact ⊒
      LLVM.Int.lshr x (LLVM.Int.constant w k) := by
  veir_bv_normalize
  grind [BitVec.lt_ofInt_natCast_ofNat_of_lt, BitVec.toNat_ofInt_natCast_of_lt,
    BitVec.udiv_twoPow_eq_of_lt]

/-- Prove the correctness of `sdiv_exact_by_pow2_pattern` for a positive divisor. -/
theorem sdiv_exact_by_pow2_pos {w : Nat} (x : LLVM.Int w) (k : Nat) (hk : k + 1 < w) :
    LLVM.Int.sdiv x (LLVM.Int.val (BitVec.twoPow w k)) true ⊒
      LLVM.Int.ashr x (LLVM.Int.constant w k) := by
  veir_bv_normalize
  grind [BitVec.twoPow_eq_shiftLeft_one_ofInt_natCast, BitVec.lt_ofInt_natCast_ofNat_of_lt,
    BitVec.toNat_ofInt_natCast_of_lt, BitVec.sdiv_one_shl_of_smod_eq_zero]

/-- Prove the correctness of `sdiv_exact_by_pow2_pattern` for a negative divisor, including
    `-2^(w-1)`. -/
theorem sdiv_exact_by_pow2_neg {w : Nat} (x : LLVM.Int w) (k : Nat) (hk : k < w) :
    LLVM.Int.sdiv x (LLVM.Int.val (-BitVec.twoPow w k)) true ⊒
      LLVM.Int.sub (LLVM.Int.constant w 0) (LLVM.Int.ashr x (LLVM.Int.constant w k)) := by
  veir_bv_normalize
  grind [BitVec.twoPow_eq_shiftLeft_one_ofInt_natCast, BitVec.lt_ofInt_natCast_ofNat_of_lt,
    BitVec.toNat_ofInt_natCast_of_lt, BitVec.sdiv_neg_one_shl_of_smod_eq_zero]

/-- The quotient that `sdiv_by_pow2_pattern` builds for `sdiv x, 2^k`. -/
def sdivPow2Shift {w : Nat} (x : LLVM.Int w) (k : Nat) : LLVM.Int w :=
  LLVM.Int.ashr
    (LLVM.Int.add x
      (LLVM.Int.lshr (LLVM.Int.ashr x (LLVM.Int.constant w (w - 1 : Nat)))
        (LLVM.Int.constant w (w - k : Nat))))
    (LLVM.Int.constant w k)

/-- Prove the correctness of `sdiv_by_pow2_pattern` for a positive divisor. -/
theorem sdiv_by_pow2_pos {w : Nat} (x : LLVM.Int w) (k : Nat) (hk0 : 0 < k) (hk : k + 1 < w) :
    LLVM.Int.sdiv x (LLVM.Int.val (BitVec.twoPow w k)) ⊒ sdivPow2Shift x k := by
  simp only [sdivPow2Shift]
  veir_bv_normalize
  grind [BitVec.twoPow_eq_shiftLeft_one_ofInt_natCast, BitVec.lt_ofInt_natCast_ofNat_of_lt,
    BitVec.toNat_ofInt_natCast_of_lt, BitVec.sdiv_one_shl_eq_biased_sshiftRight]

/-- Prove the correctness of `sdiv_by_pow2_pattern` for a negative divisor, including
    `-2^(w-1)`. -/
theorem sdiv_by_pow2_neg {w : Nat} (x : LLVM.Int w) (k : Nat) (hk0 : 0 < k) (hk : k < w) :
    LLVM.Int.sdiv x (LLVM.Int.val (-BitVec.twoPow w k)) ⊒
      LLVM.Int.sub (LLVM.Int.constant w 0) (sdivPow2Shift x k) := by
  simp only [sdivPow2Shift]
  veir_bv_normalize
  grind [BitVec.twoPow_eq_shiftLeft_one_ofInt_natCast, BitVec.lt_ofInt_natCast_ofNat_of_lt,
    BitVec.toNat_ofInt_natCast_of_lt, BitVec.sdiv_neg_one_shl_eq_neg_biased_sshiftRight]

/-! ### `tryFoldSelectOfConstants`

The combines are proved for every width `w` wider than the `i1` condition.
-/

/-- A property of `GMIR.selectNonzero` on an `i1` condition follows from its three cases. -/
private theorem selectNonzero_refines {w : Nat} (c : LLVM.Int 1) (x y : LLVM.Int w)
    (r : LLVM.Int w)
    (hp : c = .poison → r = .poison)
    (h1 : c = .val 1#1 → x ⊒ r) (h0 : c = .val 0#1 → y ⊒ r) :
    GMIR.selectNonzero c x y ⊒ r := by
  cases c with
  | poison => simp [GMIR.selectNonzero, Id.run, hp, isRefinedBy]
  | val c =>
    rcases BitVec.eq_zero_or_eq_one c with rfl | rfl
    · simpa [GMIR.selectNonzero, Id.run] using h0 rfl
    · simpa [GMIR.selectNonzero, Id.run] using h1 rfl

/-- The `i1` negation that `createNot` builds. -/
def notI1 (c : LLVM.Int 1) : LLVM.Int 1 := LLVM.Int.xor c (LLVM.Int.constant 1 (-1))

/-- Closes one case of a `tryFoldSelectOfConstants` proof, where the condition is known. -/
local macro "select_const_tac" : tactic =>
  `(tactic| (simp_all [notI1, Nat.not_le_of_gt, Nat.mod_eq_of_lt,
      BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt, BitVec.signExtend, BitVec.ofInt_neg,
      BitVec.twoPow_eq, BitVec.add_comm, BitVec.sub_eq_add_neg, BitVec.neg_one_eq_allOnes,
      LLVM.Int.xor, LLVM.Int.zext, LLVM.Int.sext, LLVM.Int.add, LLVM.Int.shl, LLVM.Int.or,
      LLVM.Int.constant, Id.run, isRefinedBy]))

/-- Prove the correctness of combining `c ? 1 : 0` to `zext c`. -/
theorem select_one_zero {w : Nat} (h : 1 < w) (c : LLVM.Int 1) :
    GMIR.selectNonzero c (LLVM.Int.constant w 1) (LLVM.Int.constant w 0) ⊒
      LLVM.Int.zext c w false h := by
  apply selectNonzero_refines <;> rintro rfl <;> select_const_tac

/-- Prove the correctness of combining `c ? -1 : 0` to `sext c`. -/
theorem select_allOnes_zero {w : Nat} (h : 1 < w) (c : LLVM.Int 1) :
    GMIR.selectNonzero c (LLVM.Int.constant w (-1)) (LLVM.Int.constant w 0) ⊒
      LLVM.Int.sext c w h := by
  apply selectNonzero_refines <;> rintro rfl <;> select_const_tac

/-- Prove the correctness of combining `c ? 0 : 1` to `zext (not c)`. -/
theorem select_zero_one {w : Nat} (h : 1 < w) (c : LLVM.Int 1) :
    GMIR.selectNonzero c (LLVM.Int.constant w 0) (LLVM.Int.constant w 1) ⊒
      LLVM.Int.zext (notI1 c) w false h := by
  apply selectNonzero_refines <;> rintro rfl <;> select_const_tac

/-- Prove the correctness of combining `c ? 0 : -1` to `sext (not c)`. -/
theorem select_zero_allOnes {w : Nat} (h : 1 < w) (c : LLVM.Int 1) :
    GMIR.selectNonzero c (LLVM.Int.constant w 0) (LLVM.Int.constant w (-1)) ⊒
      LLVM.Int.sext (notI1 c) w h := by
  apply selectNonzero_refines <;> rintro rfl <;> select_const_tac

/-- Prove the correctness of combining `c ? F + 1 : F` to `add (zext c), F`. -/
theorem select_succ {w : Nat} (h : 1 < w) (c : LLVM.Int 1) (f : BitVec w) :
    GMIR.selectNonzero c (LLVM.Int.val (f + 1)) (LLVM.Int.val f) ⊒
      LLVM.Int.add (LLVM.Int.zext c w false h) (LLVM.Int.val f) := by
  apply selectNonzero_refines <;> rintro rfl <;> select_const_tac

/-- Prove the correctness of combining `c ? F - 1 : F` to `add (sext c), F`. -/
theorem select_pred {w : Nat} (h : 1 < w) (c : LLVM.Int 1) (f : BitVec w) :
    GMIR.selectNonzero c (LLVM.Int.val (f - 1)) (LLVM.Int.val f) ⊒
      LLVM.Int.add (LLVM.Int.sext c w h) (LLVM.Int.val f) := by
  apply selectNonzero_refines <;> rintro rfl <;> select_const_tac

/-- Prove the correctness of combining `c ? 2^k : 0` to `shl (zext c), k`. -/
theorem select_pow2_zero {w : Nat} (h : 1 < w) (c : LLVM.Int 1) (k : Nat) (hk : k < w) :
    GMIR.selectNonzero c (LLVM.Int.val (BitVec.twoPow w k)) (LLVM.Int.constant w 0) ⊒
      LLVM.Int.shl (LLVM.Int.zext c w false h) (LLVM.Int.constant w k) := by
  have hkpow := Nat.lt_trans hk Nat.lt_two_pow_self
  apply selectNonzero_refines <;> rintro rfl <;> select_const_tac

/-- Prove the correctness of combining `c ? 0 : 2^k` to `shl (zext (not c)), k`. -/
theorem select_zero_pow2 {w : Nat} (h : 1 < w) (c : LLVM.Int 1) (k : Nat) (hk : k < w) :
    GMIR.selectNonzero c (LLVM.Int.constant w 0) (LLVM.Int.val (BitVec.twoPow w k)) ⊒
      LLVM.Int.shl (LLVM.Int.zext (notI1 c) w false h) (LLVM.Int.constant w k) := by
  have hkpow := Nat.lt_trans hk Nat.lt_two_pow_self
  apply selectNonzero_refines <;> rintro rfl <;> select_const_tac

/-- Prove the correctness of combining `c ? -1 : F` to `or (sext c), F`. -/
theorem select_allOnes_const {w : Nat} (h : 1 < w) (c : LLVM.Int 1) (f : BitVec w) :
    GMIR.selectNonzero c (LLVM.Int.constant w (-1)) (LLVM.Int.val f) ⊒
      LLVM.Int.or (LLVM.Int.sext c w h) (LLVM.Int.val f) := by
  apply selectNonzero_refines <;> rintro rfl <;> select_const_tac

/-- Prove the correctness of combining `c ? T : -1` to `or (sext (not c)), T`. -/
theorem select_const_allOnes {w : Nat} (h : 1 < w) (c : LLVM.Int 1) (t : BitVec w) :
    GMIR.selectNonzero c (LLVM.Int.val t) (LLVM.Int.constant w (-1)) ⊒
      LLVM.Int.or (LLVM.Int.sext (notI1 c) w h) (LLVM.Int.val t) := by
  apply selectNonzero_refines <;> rintro rfl <;> select_const_tac

/-! ### `select_into_binop_pattern`

The combines are proved for every width `w`, whatever the flags of the folded operation: `f` is the
operation with its flags and `g` the one without them. `g` must be strict in its right operand, must
refine `f`, and must leave `x` unchanged when the right operand is `0`.
-/

/-- Prove the correctness of combining `c ? (f x k) : x` to `g x (c ? k : 0)`. -/
theorem select_into_binop {w : Nat} (f g : LLVM.Int w → LLVM.Int w → LLVM.Int w)
    (c : LLVM.Int 1) (x k : LLVM.Int w)
    (hp : g x .poison = .poison) (hf : f x k ⊒ g x k) (h0 : x ⊒ g x (LLVM.Int.constant w 0)) :
    GMIR.selectNonzero c (f x k) x ⊒ g x (GMIR.selectNonzero c k (LLVM.Int.constant w 0)) := by
  apply selectNonzero_refines <;> rintro rfl <;> simpa [GMIR.selectNonzero, Id.run]

/-- Prove the correctness of combining `c ? x : (f x k)` to `g x (c ? 0 : k)`. -/
theorem select_into_binop_swapped {w : Nat} (f g : LLVM.Int w → LLVM.Int w → LLVM.Int w)
    (c : LLVM.Int 1) (x k : LLVM.Int w)
    (hp : g x .poison = .poison) (hf : f x k ⊒ g x k) (h0 : x ⊒ g x (LLVM.Int.constant w 0)) :
    GMIR.selectNonzero c x (f x k) ⊒ g x (GMIR.selectNonzero c (LLVM.Int.constant w 0) k) := by
  apply selectNonzero_refines <;> rintro rfl <;> simpa [GMIR.selectNonzero, Id.run]

/-- A shift by `0` is in range at any positive width. -/
private theorem zero_shift_in_range {w : Nat} (hw : 0 < w) :
    ¬ (w : BitVec w) ≤ BitVec.ofInt w 0 :=
  BitVec.not_le.mpr (BitVec.lt_ofInt_natCast_ofNat_of_lt hw)

/-- Closes a side condition of `select_into_binop`. -/
local macro "select_binop_tac" : tactic =>
  `(tactic| (cases ‹LLVM.Int _› <;> try cases ‹LLVM.Int _›) <;>
    grind [LLVM.Int.shl, LLVM.Int.lshr, LLVM.Int.ashr, LLVM.Int.sub, LLVM.Int.add, LLVM.Int.or,
      LLVM.Int.xor, LLVM.Int.constant, Id.run, pure, isRefinedBy])

/-- Closes a side condition of `select_into_binop` for a shift, given `0 < w`. -/
local macro "select_shift_tac" hw:term : tactic =>
  `(tactic| (have hrange := zero_shift_in_range $hw; select_binop_tac))

theorem select_into_shl {w : Nat} (hw : 0 < w) (c : LLVM.Int 1) (x k : LLVM.Int w)
    (nsw nuw : Bool) :
    GMIR.selectNonzero c (LLVM.Int.shl x k nsw nuw) x ⊒
      LLVM.Int.shl x (GMIR.selectNonzero c k (LLVM.Int.constant w 0)) :=
  select_into_binop (LLVM.Int.shl · · nsw nuw) (LLVM.Int.shl · ·) c x k
    (by select_shift_tac hw) (by select_shift_tac hw) (by select_shift_tac hw)

theorem select_into_lshr {w : Nat} (hw : 0 < w) (c : LLVM.Int 1) (x k : LLVM.Int w)
    (exact : Bool) :
    GMIR.selectNonzero c (LLVM.Int.lshr x k exact) x ⊒
      LLVM.Int.lshr x (GMIR.selectNonzero c k (LLVM.Int.constant w 0)) :=
  select_into_binop (LLVM.Int.lshr · · exact) (LLVM.Int.lshr · ·) c x k
    (by select_shift_tac hw) (by select_shift_tac hw) (by select_shift_tac hw)

theorem select_into_ashr {w : Nat} (hw : 0 < w) (c : LLVM.Int 1) (x k : LLVM.Int w)
    (exact : Bool) :
    GMIR.selectNonzero c (LLVM.Int.ashr x k exact) x ⊒
      LLVM.Int.ashr x (GMIR.selectNonzero c k (LLVM.Int.constant w 0)) :=
  select_into_binop (LLVM.Int.ashr · · exact) (LLVM.Int.ashr · ·) c x k
    (by select_shift_tac hw) (by select_shift_tac hw) (by select_shift_tac hw)

theorem select_into_sub {w : Nat} (c : LLVM.Int 1) (x k : LLVM.Int w) (nsw nuw : Bool) :
    GMIR.selectNonzero c (LLVM.Int.sub x k nsw nuw) x ⊒
      LLVM.Int.sub x (GMIR.selectNonzero c k (LLVM.Int.constant w 0)) :=
  select_into_binop (LLVM.Int.sub · · nsw nuw) (LLVM.Int.sub · ·) c x k
    (by select_binop_tac) (by select_binop_tac) (by select_binop_tac)

theorem select_into_add {w : Nat} (c : LLVM.Int 1) (x k : LLVM.Int w) (nsw nuw : Bool) :
    GMIR.selectNonzero c (LLVM.Int.add x k nsw nuw) x ⊒
      LLVM.Int.add x (GMIR.selectNonzero c k (LLVM.Int.constant w 0)) :=
  select_into_binop (LLVM.Int.add · · nsw nuw) (LLVM.Int.add · ·) c x k
    (by select_binop_tac) (by select_binop_tac) (by select_binop_tac)

theorem select_into_or {w : Nat} (c : LLVM.Int 1) (x k : LLVM.Int w) (disjoint : Bool) :
    GMIR.selectNonzero c (LLVM.Int.or x k disjoint) x ⊒
      LLVM.Int.or x (GMIR.selectNonzero c k (LLVM.Int.constant w 0)) :=
  select_into_binop (LLVM.Int.or · · disjoint) (LLVM.Int.or · ·) c x k
    (by select_binop_tac) (by select_binop_tac) (by select_binop_tac)

theorem select_into_xor {w : Nat} (c : LLVM.Int 1) (x k : LLVM.Int w) :
    GMIR.selectNonzero c (LLVM.Int.xor x k) x ⊒
      LLVM.Int.xor x (GMIR.selectNonzero c k (LLVM.Int.constant w 0)) :=
  select_into_binop LLVM.Int.xor LLVM.Int.xor c x k
    (by select_binop_tac) (by select_binop_tac)
    (by cases x <;> simp [LLVM.Int.xor, LLVM.Int.constant, Id.run, isRefinedBy])

/-! ### Word operations -/

/-- `x` is its low bits after any extension. -/
theorem trunc_ext {n m : Nat} (h : n < m) (x : LLVM.Int n) (ext : BitVec (m - n)) :
    LLVM.Int.trunc (LLVM.Int.ext x m ext h) n false false h = x := by
  cases x <;> simp [LLVM.Int.ext, LLVM.Int.trunc, LLVM.Int.cast, Id.run,
    BitVec.eq_of_getElem_eq_iff]
  grind

/-- `x` is its low bits after a sign extension. -/
theorem trunc_sext {n m : Nat} (h : n < m) (x : LLVM.Int n) :
    LLVM.Int.trunc (LLVM.Int.sext x m h) n false false h = x := by
  cases x <;> simp [LLVM.Int.sext, LLVM.Int.trunc, Id.run, BitVec.eq_of_getElem_eq_iff]
  grind

/--
Prove that legalizing an `i32` operation `f` into the word operation `word g` on any-extended
operands is correct when `g` refines `f` (see the lemmas below).
-/
theorem word_legalization (f g : LLVM.Int 32 → LLVM.Int 32 → LLVM.Int 32)
    (hfg : ∀ x y, f x y ⊒ g x y) (x y : LLVM.Int 32) (ext ext' : BitVec 32) :
    f x y ⊒
      LLVM.Int.trunc
        (GMIR_RISCV.word g (LLVM.Int.ext x 64 ext (by decide))
          (LLVM.Int.ext y 64 ext' (by decide)))
        32 false false (by decide) := by
  rw [GMIR_RISCV.word, trunc_ext, trunc_ext, trunc_sext]
  exact hfg x y

/--
Prove that legalizing an `i32` unary operation `f` into the word operation `wordUnary g` on an
any-extended operand is correct when `g` refines `f` (for `g_clzw` and `g_ctzw`, `g` is `f`).
-/
theorem word_unary_legalization (f g : LLVM.Int 32 → LLVM.Int 32) (hfg : ∀ x, f x ⊒ g x)
    (x : LLVM.Int 32) (ext : BitVec 32) :
    f x ⊒
      LLVM.Int.trunc (GMIR_RISCV.wordUnary g (LLVM.Int.ext x 64 ext (by decide))) 32 false false
        (by decide) := by
  rw [GMIR_RISCV.wordUnary, trunc_ext, trunc_sext]
  exact hfg x

/--
Prove that `g_addw`, `g_subw` and `g_mulw` may drop the no-wrap flags.
-/
theorem add_drop_flags (x y : LLVM.Int 32) (nsw nuw : Bool) :
    LLVM.Int.add x y nsw nuw ⊒ LLVM.Int.add x y := by
  veir_bv_decide

theorem sub_drop_flags (x y : LLVM.Int 32) (nsw nuw : Bool) :
    LLVM.Int.sub x y nsw nuw ⊒ LLVM.Int.sub x y := by
  veir_bv_decide

theorem mul_drop_flags (x y : LLVM.Int 32) (nsw nuw : Bool) :
    LLVM.Int.mul x y nsw nuw ⊒ LLVM.Int.mul x y := by
  veir_bv_decide

/--
Prove that `g_divw` and `g_divuw` may drop the `exact` flag.
-/
theorem sdiv_drop_exact (x y : LLVM.Int 32) (exact : Bool) :
    LLVM.Int.sdiv x y exact ⊒ LLVM.Int.sdiv x y := by
  veir_bv_decide

theorem udiv_drop_exact (x y : LLVM.Int 32) (exact : Bool) :
    LLVM.Int.udiv x y exact ⊒ LLVM.Int.udiv x y := by
  veir_bv_decide

/-- Prove that the word shifts may drop the flags and read only the low 5 bits of the amount. -/
theorem shl_wordShiftAmount (x y : LLVM.Int 32) (nsw nuw : Bool) :
    LLVM.Int.shl x y nsw nuw ⊒ LLVM.Int.shl x (GMIR_RISCV.wordShiftAmount y) := by
  unfold GMIR_RISCV.wordShiftAmount
  veir_bv_decide

theorem lshr_wordShiftAmount (x y : LLVM.Int 32) (exact : Bool) :
    LLVM.Int.lshr x y exact ⊒ LLVM.Int.lshr x (GMIR_RISCV.wordShiftAmount y) := by
  unfold GMIR_RISCV.wordShiftAmount
  veir_bv_decide

theorem ashr_wordShiftAmount (x y : LLVM.Int 32) (exact : Bool) :
    LLVM.Int.ashr x y exact ⊒ LLVM.Int.ashr x (GMIR_RISCV.wordShiftAmount y) := by
  unfold GMIR_RISCV.wordShiftAmount
  veir_bv_decide

/--
Prove the correctness of lowering `g_uaddo` to a `g_add`, at every width.

The add carries exactly when its sum is less than an operand.
-/
theorem uaddo_lowering {w : Nat} (x y : LLVM.Int w) :
    (LLVM.Int.add x y, LLVM.Int.uaddOverflowFlag x y) =
      let sum := LLVM.Int.add x y
      (sum, LLVM.Int.icmp sum y .ult) := by
  cases x <;> cases y <;>
    simp [LLVM.Int.uaddOverflowFlag, LLVM.Int.add, LLVM.Int.icmp, Id.run, IntPred.eval,
      BitVec.uaddOverflow_eq_ult]

/--
Prove the correctness of lowering `g_uadde`, at every width wider than `i1`.

The lowering adds the operands, then adds the carry-in. It carries if either add carries. The
second add carries only if its sum is zero.
-/
private theorem uadde_lowering {w : Nat} (h : 1 < w) (x y : LLVM.Int w) (c : LLVM.Int 1) :
    uaddWithCarry x y c =
      let tmp := LLVM.Int.add x y
      let carry := LLVM.Int.icmp tmp x .ult
      let sum := LLVM.Int.add tmp (LLVM.Int.zext c w false h)
      let carry2 := LLVM.Int.and (LLVM.Int.icmp sum (LLVM.Int.constant w 0) .eq) c
      (sum, LLVM.Int.or carry carry2) := by
  cases x <;> cases y <;> cases c
  case val.val.val x y c =>
    obtain ⟨b, rfl⟩ := c.exists_eq_ofBool
    -- It carries if either `g_add` carries.
    simp [uaddWithCarry, LLVM.Int.add, LLVM.Int.icmp, LLVM.Int.zext, LLVM.Int.and, LLVM.Int.or,
      LLVM.Int.constant, Id.run, IntPred.eval, BitVec.ofBool_or_ofBool, BitVec.ofBool_and_ofBool,
      BitVec.carry_eq_uaddOverflow_or (by omega : 0 < w), BitVec.uaddOverflow_eq_ult_left x y,
      BitVec.uaddOverflow_setWidth_ofBool (by omega : 0 < w)]
  -- The other seven cases have a poison operand, so both sides reduce to poison.
  all_goals rfl

/--
Prove the correctness of lowering `g_usubo` to a `g_sub`, at every width.

The sub borrows exactly when the left operand is less than the right one.
-/
theorem usubo_lowering {w : Nat} (x y : LLVM.Int w) :
    (LLVM.Int.sub x y, LLVM.Int.usubOverflowFlag x y) =
      (LLVM.Int.sub x y, LLVM.Int.icmp x y .ult) := by
  cases x <;> cases y <;>
    simp [LLVM.Int.usubOverflowFlag, LLVM.Int.icmp, Id.run, IntPred.eval,
      BitVec.usubOverflow_eq, BitVec.ult_eq_decide, BitVec.lt_def]

/--
Prove the correctness of lowering `g_usube`, at every width wider than `i1`.

The lowering subtracts the operands, then subtracts the borrow-in. It borrows if either sub borrows.
The second sub borrows only if the first difference is zero.
-/
private theorem usube_lowering {w : Nat} (h : 1 < w) (x y : LLVM.Int w) (b : LLVM.Int 1) :
    usubWithBorrow x y b =
      let tmp := LLVM.Int.sub x y
      let borrow := LLVM.Int.icmp tmp x .ugt
      let diff := LLVM.Int.sub tmp (LLVM.Int.zext b w false h)
      let borrow2 := LLVM.Int.and (LLVM.Int.icmp tmp (LLVM.Int.constant w 0) .eq) b
      (diff, LLVM.Int.or borrow borrow2) := by
  cases x <;> cases y <;> cases b
  case val.val.val x y b =>
    obtain ⟨b, rfl⟩ := b.exists_eq_ofBool
    -- It borrows if either `g_sub` borrows.
    simp [usubWithBorrow, LLVM.Int.sub, LLVM.Int.icmp, LLVM.Int.zext, LLVM.Int.and, LLVM.Int.or,
      LLVM.Int.constant, Id.run, IntPred.eval, BitVec.ofBool_or_ofBool, BitVec.ofBool_and_ofBool,
      BitVec.ult_setWidth_add_ofBool (by omega : 0 < w), BitVec.usubOverflow_eq_ult_sub x y,
      BitVec.usubOverflow_setWidth_ofBool (by omega : 0 < w)]
  -- The other seven cases have a poison operand, so both sides reduce to poison.
  all_goals rfl

/-- Dropping the no-wrap flags of `g_add` can only remove poison. -/
private theorem add_isRefinedBy_add {w : Nat} (x y : LLVM.Int w) (nsw nuw : Bool) :
    LLVM.Int.add x y nsw nuw ⊒ LLVM.Int.add x y := by
  grind

/-- Dropping the no-wrap flags of `g_sub` can only remove poison. -/
private theorem sub_isRefinedBy_sub {w : Nat} (x y : LLVM.Int w) (nsw nuw : Bool) :
    LLVM.Int.sub x y nsw nuw ⊒ LLVM.Int.sub x y := by
  grind

/--
Prove the correctness of narrowing `g_add` to a `g_uaddo` of the low halves of its operands, and a
`g_uadde` of their high halves, at every width.
-/
private theorem add_narrowing {w : Nat} (x y : LLVM.Int (w + w)) (nsw nuw : Bool) :
    LLVM.Int.add x y nsw nuw ⊒
      let (xLo, xHi) := unmergeValues x
      let (yLo, yHi) := unmergeValues y
      let (hi, _) := uaddWithCarry xHi yHi (LLVM.Int.uaddOverflowFlag xLo yLo)
      mergeValues (LLVM.Int.add xLo yLo) hi := by
  -- Without its flags, the `g_add` is equal to its narrowing.
  refine isRefinedBy_trans (add_isRefinedBy_add x y nsw nuw) ?_
  cases x <;> cases y
  case val.val x y =>
    simp [LLVM.Int.add, LLVM.Int.uaddOverflowFlag, unmergeValues, uaddWithCarry, mergeValues,
      Id.run, BitVec.add_eq_append]
  -- A poison operand makes both sides poison.
  all_goals exact poison_isRefinedBy _

/--
Prove the correctness of narrowing `g_sub` to a `g_usubo` of the low halves of its operands, and a
`g_usube` of their high halves, at every width.
-/
private theorem sub_narrowing {w : Nat} (x y : LLVM.Int (w + w)) (nsw nuw : Bool) :
    LLVM.Int.sub x y nsw nuw ⊒
      let (xLo, xHi) := unmergeValues x
      let (yLo, yHi) := unmergeValues y
      let (hi, _) := usubWithBorrow xHi yHi (LLVM.Int.usubOverflowFlag xLo yLo)
      mergeValues (LLVM.Int.sub xLo yLo) hi := by
  -- Without its flags, the `g_sub` is equal to its narrowing.
  refine isRefinedBy_trans (sub_isRefinedBy_sub x y nsw nuw) ?_
  cases x <;> cases y
  case val.val x y =>
    simp [LLVM.Int.sub, LLVM.Int.usubOverflowFlag, unmergeValues, usubWithBorrow, mergeValues,
      Id.run, BitVec.sub_eq_append]
  -- A poison operand makes both sides poison.
  all_goals exact poison_isRefinedBy _

/--
Prove the correctness of combining `g_unmerge_values (g_merge_values lo hi)` to `lo` and `hi`, at
every width.
-/
private theorem unmerge_merge {w : Nat} (lo hi : LLVM.Int w) :
    (unmergeValues (mergeValues lo hi)).1 ⊒ lo ∧ (unmergeValues (mergeValues lo hi)).2 ⊒ hi := by
  cases lo <;> cases hi <;>
    simp [mergeValues, unmergeValues, BitVec.setWidth_append_eq_right,
      BitVec.extractLsb'_append_eq_left]

/-! ## Widening at every width

The widening rules match any source width `w` below the target width `W`, so their local
correctness lemmas hold at symbolic widths. They are stated as the CTree validity proofs of
`Veir.Passes.Legalization.Validity` see the rules. -/

section Widening

variable {w W : Nat}

/-- Sign extension preserves the unsigned order: it adds the same amount to two values whose
sign bits agree, and keeps a negative value above a non-negative one. -/
theorem signExtend_ult_signExtend (h : w ≤ W) (x y : BitVec w) :
    (x.signExtend W).ult (y.signExtend W) = x.ult y := by
  have hpow : 2 ^ w ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) h
  have hx := x.isLt
  have hy := y.isLt
  simp only [BitVec.ult, BitVec.toNat_signExtend, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx hpow), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy hpow),
    BitVec.msb_eq_decide, decide_eq_decide]
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · have : x.toNat = 0 := by omega
    have : y.toNat = 0 := by omega
    simp_all
  · have hhalf : 2 ^ w = 2 * 2 ^ (w - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    split <;> split <;> simp_all <;> omega

/-- Sign extension preserves the unsigned non-strict order. -/
theorem signExtend_ule_signExtend (h : w ≤ W) (x y : BitVec w) :
    (x.signExtend W).ule (y.signExtend W) = x.ule y := by
  have := signExtend_ult_signExtend h y x
  simp only [BitVec.ule, BitVec.ult, decide_eq_decide] at this ⊢
  omega

/-- Sign extension preserves equality. -/
theorem signExtend_beq_signExtend (h : w ≤ W) (x y : BitVec w) :
    (x.signExtend W == y.signExtend W) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toInt_inj, BitVec.toInt_signExtend_of_le h,
    BitVec.toInt_signExtend_of_le h, BitVec.toInt_inj]

/-- Sign extension preserves the signed order. -/
theorem signExtend_slt_signExtend (h : w ≤ W) (x y : BitVec w) :
    (x.signExtend W).slt (y.signExtend W) = x.slt y := by
  simp only [BitVec.slt, BitVec.toInt_signExtend_of_le h]

/-- Sign extension preserves the signed non-strict order. -/
theorem signExtend_sle_signExtend (h : w ≤ W) (x y : BitVec w) :
    (x.signExtend W).sle (y.signExtend W) = x.sle y := by
  simp only [BitVec.sle, BitVec.toInt_signExtend_of_le h]

/-- Sign extension preserves every integer comparison. -/
theorem IntPred.eval_signExtend (h : w ≤ W) (p : IntPred) (x y : BitVec w) :
    p.eval (x.signExtend W) (y.signExtend W) = p.eval x y := by
  cases p <;> simp only [IntPred.eval, signExtend_ult_signExtend h, signExtend_ule_signExtend h,
    signExtend_slt_signExtend h, signExtend_sle_signExtend h, bne, signExtend_beq_signExtend h]

/-- Zero extension preserves the value of a bit-vector as a natural number. -/
theorem toNat_setWidth_of_le (h : w ≤ W) (x : BitVec w) : (x.setWidth W).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h))]

/-- `widenScalar` of the condition of `g_select` (type group 1) with `g_zext`: a zero-extended
condition is nonzero exactly when the condition is. -/
theorem selectNonzero_zext {v : Nat} (h : w < W) (c : LLVM.Int w) (x y : LLVM.Int v) :
    GMIR.selectNonzero (c.zext W false h) x y = GMIR.selectNonzero c x y := by
  cases c with
  | poison => simp [Int.zext, GMIR.selectNonzero, Id.run]
  | val c =>
    have : (c.setWidth W = 0#W) = (c = 0#w) := by
      rw [eq_iff_iff, ← BitVec.toNat_inj, ← BitVec.toNat_inj, toNat_setWidth_of_le (Nat.le_of_lt h)]
      simp
    simp [Int.zext, GMIR.selectNonzero, Id.run, this]

/-- `widenScalar` of the amount of `g_fshl` and `g_fshr` (type group 1) with `g_zext`: a
zero-extended amount is the same amount. -/
theorem funnelShiftAmount_zext {v : Nat} (h : w < W) (z : LLVM.Int w) :
    GMIR.funnelShiftAmount v (z.zext W false h) = GMIR.funnelShiftAmount v z := by
  cases z <;> simp [Int.zext, GMIR.funnelShiftAmount, Id.run, toNat_setWidth_of_le (Nat.le_of_lt h)]

/-- `widenScalar` of the operands of `g_icmp` (type group 1) with `g_sext`. -/
theorem icmp_sext (h : w < W) (x y : LLVM.Int w) (p : IntPred) :
    (x.sext W h).icmp (y.sext W h) p = x.icmp y p := by
  cases x <;> cases y <;>
    simp [Int.sext, Int.icmp, Id.run, IntPred.eval_signExtend (Nat.le_of_lt h)]

end Widening

/-! ## Counting bits at every width

The count rules widen the operand of `g_ctlz` and `g_cttz` to any width `W` above its width `w`.
These facts relate the counts of the wide and the narrow operand. -/

section Counting

variable {w W : Nat}

/-- The leading zeros of a nonzero bit-vector are fewer than its width. -/
theorem clz_lt_of_ne_zero {x : BitVec w} (hx : x ≠ 0#w) : (BitVec.clz x).toNat < w := by
  have := BitVec.clz_lt_iff_ne_zero.mpr hx
  rw [BitVec.lt_def] at this
  simpa [Nat.mod_eq_of_lt Nat.lt_two_pow_self] using this

theorem toNat_clz_zero : (BitVec.clz (0#w)).toNat = w := by
  rw [BitVec.clz_eq_iff_eq_zero.mpr rfl]
  simp [Nat.mod_eq_of_lt Nat.lt_two_pow_self]

/-- Zero-extending a bit-vector by `W - w` bits adds `W - w` leading zeros. The count is pinned
down by the bounds `2 ^ (w - 1 - clz x) ≤ x < 2 ^ (w - clz x)` of a nonzero `x`. -/
theorem toNat_clz_setWidth (h : w ≤ W) (x : BitVec w) :
    (BitVec.clz (x.setWidth W)).toNat = (BitVec.clz x).toNat + (W - w) := by
  by_cases hx : x = 0#w
  · subst hx
    simp only [BitVec.setWidth_zero, toNat_clz_zero]
    omega
  · have hX : x.setWidth W ≠ 0#W := by
      intro h'
      apply hx
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h'
      simpa [toNat_setWidth_of_le h] using this
    have hw : 0 < w := by
      rcases w with _ | w
      · exact absurd (BitVec.eq_nil x) hx
      · omega
    have a1 := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero hw hx
    have a2 := BitVec.toNat_lt_two_pow_sub_clz (x := x)
    have b1 := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (by omega) hX
    have b2 := BitVec.toNat_lt_two_pow_sub_clz (x := x.setWidth W)
    rw [toNat_setWidth_of_le h] at b1 b2
    have c1 := clz_lt_of_ne_zero hx
    have c2 := clz_lt_of_ne_zero hX
    have e1 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt a1 b2)
    have e2 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt b1 a2)
    omega

/-- The trailing zeros of `x` are `k` if bit `k` is its lowest set bit. -/
theorem toNat_ctz_eq {x : BitVec w} {k : Nat} (hk : x.getLsbD k = true)
    (hlt : ∀ i < k, x.getLsbD i = false) : (BitVec.ctz x).toNat = k := by
  have hx : x ≠ 0#w := by intro h; simp [h] at hk
  have h1 := BitVec.getLsbD_true_ctz_of_ne_zero hx
  rcases Nat.lt_trichotomy (BitVec.ctz x).toNat k with h | h | h
  · simp [hlt _ h] at h1
  · exact h
  · simp [BitVec.getLsbD_false_of_lt_ctz h] at hk

theorem toNat_ctz_zero : (BitVec.ctz (0#w)).toNat = w := by
  rw [BitVec.ctz_eq_reverse_clz, show (0#w).reverse = 0#w from BitVec.reverse_eq_zero_iff.mpr rfl,
    toNat_clz_zero]

theorem getLsbD_ofInt_two_pow {i : Nat} :
    (BitVec.ofInt W (2 ^ w)).getLsbD i = (decide (i < W) && decide (w = i)) := by
  rw [show (2 ^ w : _root_.Int) = ((2 ^ w : Nat) : _root_.Int) by simp, BitVec.ofInt_natCast,
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow]

/-- Setting bit `w` of any extension of the `w`-bit `x` keeps the trailing zeros of `x`, and makes
those of a zero `x` its width. -/
theorem toNat_ctz_or_two_pow (h : w < W) (m : BitVec (W - w)) (x : BitVec w) :
    (BitVec.ctz (((m ++ x).cast (by omega) : BitVec W) ||| BitVec.ofInt W (2 ^ w))).toNat =
      (BitVec.ctz x).toNat := by
  have hbit : ∀ i < w, (((m ++ x).cast (by omega) : BitVec W) ||| BitVec.ofInt W (2 ^ w)).getLsbD i =
      x.getLsbD i := by
    intro i hi
    simp [BitVec.getLsbD_append, hi, getLsbD_ofInt_two_pow, Nat.ne_of_gt hi]
  have htop : (((m ++ x).cast (by omega) : BitVec W) ||| BitVec.ofInt W (2 ^ w)).getLsbD w = true := by
    simp [getLsbD_ofInt_two_pow, h]
  by_cases hx : x = 0#w
  · subst hx
    rw [toNat_ctz_zero]
    exact toNat_ctz_eq htop fun i hi => by simp [hbit i hi]
  · have hk := BitVec.getLsbD_true_ctz_of_ne_zero hx
    have hlt : (BitVec.ctz x).toNat < w := by
      have := BitVec.ctz_lt_iff_ne_zero.mpr hx
      rw [BitVec.lt_def] at this
      simpa [Nat.mod_eq_of_lt Nat.lt_two_pow_self] using this
    apply toNat_ctz_eq
    · rw [hbit _ hlt, hk]
    · intro i hi
      rw [hbit _ (by omega)]
      exact BitVec.getLsbD_false_of_lt_ctz hi

/-- The wide operand of a `g_cttz` widened by `widenCttzSrc` is never zero. -/
theorem ext_or_two_pow_ne_zero (h : w < W) (m : BitVec (W - w)) (x : BitVec w) :
    ((m ++ x).cast (by omega) : BitVec W) ||| BitVec.ofInt W (2 ^ w) ≠ 0#W := by
  intro h0
  have htop : (((m ++ x).cast (by omega) : BitVec W) ||| BitVec.ofInt W (2 ^ w)).getLsbD w = true := by
    simp [getLsbD_ofInt_two_pow, h]
  simp [h0] at htop

end Counting

/-! ## Saturating arithmetic at every width

The lowerings of the saturating operations clamp with min and max, or select on an overflow flag.
They are proved on the signed values (`toInt`), where none of the clamped operations wraps, so
`omega` decides them once the min and max are exposed. -/

section Saturating

variable {w : Nat}

/- The case splits of the saturation proofs share one simp set, each case using part of it. -/
set_option linter.unusedSimpArgs false

theorem ofInt_neg_one : BitVec.ofInt w (-1) = BitVec.allOnes w := by
  rw [show (-1 : _root_.Int) = _root_.Int.negSucc 0 from rfl, BitVec.ofInt_negSucc_eq_not_ofNat]
  simp

theorem toInt_smin_ite (a b : BitVec w) :
    (if a.sle b = true then a else b).toInt = min a.toInt b.toInt := by
  split <;> simp_all [BitVec.sle_iff_toInt_le] <;> omega

theorem toInt_smax_ite (a b : BitVec w) :
    (if a.sle b = true then b else a).toInt = max a.toInt b.toInt := by
  split <;> simp_all [BitVec.sle_iff_toInt_le] <;> omega

/-- A signed value in range does not wrap. -/
theorem bmod_two_pow_of_range (hw : 0 < w) {s : _root_.Int} (h1 : -2 ^ (w - 1) ≤ s)
    (h2 : s < 2 ^ (w - 1)) : s.bmod (2 ^ w) = s := by
  rw [← BitVec.toInt_ofInt]
  exact BitVec.toInt_ofInt_eq_self hw h1 h2

/-- An arithmetic shift right by `w - 1` spreads the sign bit. -/
theorem sshiftRight_width_sub_one (x : BitVec w) :
    x.sshiftRight (w - 1) = if x.msb then BitVec.allOnes w else 0#w := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_sshiftRight hi]
  split
  · have : i = 0 := by omega
    subst this
    simp only [Nat.add_zero, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_eq_getElem (by omega : w - 1 < w)]
    split <;> simp_all
  · split <;> simp_all

theorem allOnes_add_intMin : BitVec.allOnes w + BitVec.intMin w = BitVec.intMax w := by
  rw [← BitVec.neg_one_eq_allOnes, BitVec.add_comm, ← BitVec.sub_eq_add_neg]
  exact (BitVec.eq_sub_iff_add_eq.mpr BitVec.intMax_add_one).symm

theorem intMax_eq_ofInt : BitVec.intMax w = BitVec.ofInt w (2 ^ (w - 1) - 1) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · exact BitVec.of_length_zero.trans BitVec.of_length_zero.symm
  apply BitVec.eq_of_toInt_eq
  have : (1 : _root_.Int) ≤ 2 ^ (w - 1) := by
    have := Nat.one_le_two_pow (n := w - 1)
    exact_mod_cast this
  rw [BitVec.toInt_intMax, BitVec.toInt_ofInt_eq_self hw (by omega) (by omega)]

/-- Lowering `g_uaddsat` with `g_umin`: `uadd.sat a b = a + umin (~a) b`. -/
theorem uaddSat_minmax (x y : LLVM.Int w) :
    x.uaddSat y ⊒ x.add ((x.xor (.val (BitVec.ofInt w (-1)))).umin y) := by
  cases x <;> cases y <;>
    simp [Int.uaddSat, Int.add, Int.xor, Int.umin, Id.run, isRefinedBy_eq, pure, ofInt_neg_one,
      BitVec.xor_allOnes]
  rename_i x y
  have := x.isLt
  have := y.isLt
  by_cases h1 : x.uaddOverflow y <;> by_cases h2 : (~~~x).ule y <;>
    simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true] <;>
    simp only [BitVec.uaddOverflow, BitVec.ule_eq_decide, BitVec.toNat_not, decide_eq_true_eq,
      Bool.not_eq_true, decide_eq_false_iff_not] at h1 h2
  · exact (BitVec.add_not_self x).symm
  · omega
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_not]
    omega

/-- Lowering `g_usubsat` with `g_umin`: `usub.sat a b = a - umin a b`. -/
theorem usubSat_minmax (x y : LLVM.Int w) : x.usubSat y ⊒ x.sub (x.umin y) := by
  cases x <;> cases y <;> simp [Int.usubSat, Int.sub, Int.umin, Id.run, isRefinedBy_eq, pure]
  rename_i x y
  by_cases h1 : x.usubOverflow y <;> by_cases h2 : x.ule y <;>
    simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true] <;>
    simp only [BitVec.usubOverflow, BitVec.ule_eq_decide, decide_eq_true_eq,
      Bool.not_eq_true, decide_eq_false_iff_not] at h1 h2
  · simp
  · omega
  · have : x = y := BitVec.eq_of_toNat_eq (by omega)
    simp [this]

/-- Lowering `g_saddsat` with `g_smin` and `g_smax`:
`sadd.sat a b = a + smin (smax (INT_MIN - smin a 0) b) (INT_MAX - smax a 0)`. -/
theorem saddSat_minmax (x y : LLVM.Int w) :
    x.saddSat y ⊒ x.add ((((LLVM.Int.val (BitVec.ofInt w (-2 ^ (w - 1)))).sub
        (x.smin (.val 0#w))).smax y).smin
        ((LLVM.Int.val (BitVec.ofInt w (2 ^ (w - 1) - 1))).sub (x.smax (.val 0#w)))) := by
  cases x <;> cases y <;> simp [Int.saddSat, Int.add, Int.sub, Int.smin, Int.smax, Id.run, isRefinedBy_eq,
    pure]
  rename_i x y
  by_cases h : x.saddOverflow y <;> simp only [h, ite_true, ite_false, Bool.false_eq_true]
  all_goals rcases Nat.eq_zero_or_pos w with rfl | hw
  all_goals try exact BitVec.of_length_zero.trans BitVec.of_length_zero.symm
  all_goals
    have := BitVec.le_toInt x
    have := BitVec.toInt_lt (x := x)
    have := BitVec.le_toInt y
    have := BitVec.toInt_lt (x := y)
    have : (1 : _root_.Int) ≤ 2 ^ (w - 1) := by
      have := Nat.one_le_two_pow (n := w - 1)
      exact_mod_cast this
    simp only [BitVec.saddOverflow, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true,
      Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    apply BitVec.eq_of_toInt_eq
    simp (disch := omega) only [BitVec.toInt_add, BitVec.toInt_sub, BitVec.toInt_ofInt, toInt_smin_ite,
      toInt_smax_ite, BitVec.toInt_zero, bmod_two_pow_of_range hw]
  · split <;> simp_all [BitVec.msb_eq_toInt, BitVec.toInt_intMin_of_pos hw] <;> omega
  · omega

/-- Lowering `g_ssubsat` with `g_smin` and `g_smax`:
`ssub.sat a b = a - smin (smax (smax a (-1) - INT_MAX) b) (smin a (-1) - INT_MIN)`. -/
theorem ssubSat_minmax (x y : LLVM.Int w) :
    x.ssubSat y ⊒ x.sub ((((x.smax (.val (BitVec.ofInt w (-1)))).sub
        (.val (BitVec.ofInt w (2 ^ (w - 1) - 1)))).smax y).smin
        ((x.smin (.val (BitVec.ofInt w (-1)))).sub (.val (BitVec.ofInt w (-2 ^ (w - 1)))))) := by
  cases x <;> cases y <;> simp [Int.ssubSat, Int.sub, Int.smin, Int.smax, Id.run, isRefinedBy_eq, pure]
  rename_i x y
  by_cases h : x.ssubOverflow y <;> simp only [h, ite_true, ite_false, Bool.false_eq_true]
  all_goals rcases Nat.eq_zero_or_pos w with rfl | hw
  all_goals try exact BitVec.of_length_zero.trans BitVec.of_length_zero.symm
  all_goals
    have := BitVec.le_toInt x
    have := BitVec.toInt_lt (x := x)
    have := BitVec.le_toInt y
    have := BitVec.toInt_lt (x := y)
    have : (1 : _root_.Int) ≤ 2 ^ (w - 1) := by
      have := Nat.one_le_two_pow (n := w - 1)
      exact_mod_cast this
    simp only [BitVec.ssubOverflow, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true,
      Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    apply BitVec.eq_of_toInt_eq
    simp (disch := omega) only [BitVec.toInt_add, BitVec.toInt_sub, BitVec.toInt_ofInt, toInt_smin_ite,
      toInt_smax_ite, BitVec.toInt_zero, bmod_two_pow_of_range hw]
  · split <;> simp_all [BitVec.msb_eq_toInt, BitVec.toInt_intMin_of_pos hw] <;> omega
  · omega

/-- Lowering `g_uaddsat` with `g_uaddo`: `uadd.sat a b = let (r, ov) := uaddo a b; ov ? -1 : r`. -/
theorem uaddSat_addo (x y : LLVM.Int w) :
    x.uaddSat y ⊒ GMIR.selectNonzero (x.uaddOverflowFlag y) (.val (BitVec.ofInt w (-1))) (x.add y) := by
  cases x <;> cases y <;>
    simp [Int.uaddSat, Int.add, Int.uaddOverflowFlag, GMIR.selectNonzero, Id.run, isRefinedBy_eq, pure,
      ofInt_neg_one]
  rename_i x y
  by_cases h1 : x.uaddOverflow y <;> simp [h1]

/-- Lowering `g_usubsat` with `g_usubo`: `usub.sat a b = let (r, ov) := usubo a b; ov ? 0 : r`. -/
theorem usubSat_subo (x y : LLVM.Int w) :
    x.usubSat y ⊒ GMIR.selectNonzero (x.usubOverflowFlag y) (.val (BitVec.ofInt w 0)) (x.sub y) := by
  cases x <;> cases y <;>
    simp [Int.usubSat, Int.sub, Int.usubOverflowFlag, GMIR.selectNonzero, Id.run, isRefinedBy_eq, pure]
  rename_i x y
  by_cases h1 : x.usubOverflow y <;> simp [h1]

end Saturating

end Veir.Data.LLVM

end
