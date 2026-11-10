module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Casting
public import Veir.Dialects.GMIR.Semantics
public import Veir.Dialects.GMIR_RISCV.Semantics

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect
meta import Lean

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
@[expose] def sdivPow2Shift {w : Nat} (x : LLVM.Int w) (k : Nat) : LLVM.Int w :=
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
@[expose] def notI1 (c : LLVM.Int 1) : LLVM.Int 1 := LLVM.Int.xor c (LLVM.Int.constant 1 (-1))

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

theorem select_into_shl_swapped {w : Nat} (hw : 0 < w) (c : LLVM.Int 1) (x k : LLVM.Int w)
    (nsw nuw : Bool) :
    GMIR.selectNonzero c x (LLVM.Int.shl x k nsw nuw) ⊒
      LLVM.Int.shl x (GMIR.selectNonzero c (LLVM.Int.constant w 0) k) :=
  select_into_binop_swapped (LLVM.Int.shl · · nsw nuw) (LLVM.Int.shl · ·) c x k
    (by select_shift_tac hw) (by select_shift_tac hw) (by select_shift_tac hw)

theorem select_into_lshr_swapped {w : Nat} (hw : 0 < w) (c : LLVM.Int 1) (x k : LLVM.Int w)
    (exact : Bool) :
    GMIR.selectNonzero c x (LLVM.Int.lshr x k exact) ⊒
      LLVM.Int.lshr x (GMIR.selectNonzero c (LLVM.Int.constant w 0) k) :=
  select_into_binop_swapped (LLVM.Int.lshr · · exact) (LLVM.Int.lshr · ·) c x k
    (by select_shift_tac hw) (by select_shift_tac hw) (by select_shift_tac hw)

theorem select_into_ashr_swapped {w : Nat} (hw : 0 < w) (c : LLVM.Int 1) (x k : LLVM.Int w)
    (exact : Bool) :
    GMIR.selectNonzero c x (LLVM.Int.ashr x k exact) ⊒
      LLVM.Int.ashr x (GMIR.selectNonzero c (LLVM.Int.constant w 0) k) :=
  select_into_binop_swapped (LLVM.Int.ashr · · exact) (LLVM.Int.ashr · ·) c x k
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

/-! ### Widening at every width: the type-group rules

`widenTypeGroup` extends the operands of an operation to `W` bits, computes it there, and truncates
the result back to `w` bits. These lemmas state that for each operation, in the form the CTree
validity proofs see. An any-extended operand is `x.ext W m`, whatever the high bits `m` the
`g_anyext` chooses. -/

set_option linter.unusedSimpArgs false

/-- A signed value in range does not wrap. -/
theorem bmod_two_pow_of_range (hw : 0 < w) {s : _root_.Int} (h1 : -2 ^ (w - 1) ≤ s)
    (h2 : s < 2 ^ (w - 1)) : s.bmod (2 ^ w) = s := by
  rw [← BitVec.toInt_ofInt]
  exact BitVec.toInt_ofInt_eq_self hw h1 h2

/-- The signed value of a bit-vector is in the range of its width. -/
theorem bmod_toInt (x : BitVec w) : x.toInt.bmod (2 ^ w) = x.toInt := by
  rw [← BitVec.toInt_ofInt, BitVec.ofInt_toInt]


/-- The signed value of a truncation is the signed value modulo the narrow width. -/
theorem toInt_setWidth_of_le (h : w ≤ W) (z : BitVec W) :
    (z.setWidth w).toInt = z.toInt.bmod (2 ^ w) := by
  rw [BitVec.toInt_setWidth, BitVec.toInt_eq_toNat_bmod, Int.bmod_bmod_of_dvd]
  exact_mod_cast Nat.pow_dvd_pow 2 h


/-- A sign extension truncated back is the value. -/
theorem setWidth_signExtend_of_le (h : w ≤ W) (x : BitVec w) : (x.signExtend W).setWidth w = x := by
  apply BitVec.eq_of_toInt_eq
  rw [toInt_setWidth_of_le h, BitVec.toInt_signExtend_of_le h, bmod_toInt]


/-- The low bits of a sum are the sum of the low bits, and likewise for the other operations that
truncation commutes with. -/
theorem trunc_add (h : w < W) (a b : LLVM.Int W) :
    LLVM.Int.trunc (LLVM.Int.add a b) w false false h =
      LLVM.Int.add (LLVM.Int.trunc a w false false h) (LLVM.Int.trunc b w false false h) := by
  cases a <;> cases b <;> simp [LLVM.Int.add, LLVM.Int.trunc, Id.run, BitVec.setWidth_add _ _ (Nat.le_of_lt h)]


theorem trunc_sub (h : w < W) (a b : LLVM.Int W) :
    LLVM.Int.trunc (LLVM.Int.sub a b) w false false h =
      LLVM.Int.sub (LLVM.Int.trunc a w false false h) (LLVM.Int.trunc b w false false h) := by
  cases a <;> cases b <;> simp [LLVM.Int.sub, LLVM.Int.trunc, Id.run, BitVec.sub_eq_add_neg,
    BitVec.setWidth_add _ _ (Nat.le_of_lt h), BitVec.setWidth_neg_of_le (Nat.le_of_lt h)]


theorem trunc_mul (h : w < W) (a b : LLVM.Int W) :
    LLVM.Int.trunc (LLVM.Int.mul a b) w false false h =
      LLVM.Int.mul (LLVM.Int.trunc a w false false h) (LLVM.Int.trunc b w false false h) := by
  cases a <;> cases b <;> simp [LLVM.Int.mul, LLVM.Int.trunc, Id.run, BitVec.setWidth_mul _ _ (Nat.le_of_lt h)]


theorem trunc_and (h : w < W) (a b : LLVM.Int W) :
    LLVM.Int.trunc (LLVM.Int.and a b) w false false h =
      LLVM.Int.and (LLVM.Int.trunc a w false false h) (LLVM.Int.trunc b w false false h) := by
  cases a <;> cases b <;> simp [LLVM.Int.and, LLVM.Int.trunc, Id.run]


theorem trunc_or (h : w < W) (a b : LLVM.Int W) :
    LLVM.Int.trunc (LLVM.Int.or a b) w false false h =
      LLVM.Int.or (LLVM.Int.trunc a w false false h) (LLVM.Int.trunc b w false false h) := by
  cases a <;> cases b <;> simp [LLVM.Int.or, LLVM.Int.trunc, Id.run]


theorem trunc_xor (h : w < W) (a b : LLVM.Int W) :
    LLVM.Int.trunc (LLVM.Int.xor a b) w false false h =
      LLVM.Int.xor (LLVM.Int.trunc a w false false h) (LLVM.Int.trunc b w false false h) := by
  cases a <;> cases b <;> simp [LLVM.Int.xor, LLVM.Int.trunc, Id.run]



/-- `widenTypeGroup .g_add (.type 0) .g_anyext`: the sum of the any-extended operands, without the
no-wrap flags, truncated back; and likewise for the operations below. -/
theorem add_widening (h : w < W) (x y : LLVM.Int w) (m m' : BitVec (W - w)) (nsw nuw : Bool) :
    LLVM.Int.add x y nsw nuw ⊒
      LLVM.Int.trunc (LLVM.Int.add (LLVM.Int.ext x W m h) (LLVM.Int.ext y W m' h)) w false false h := by
  rw [trunc_add, trunc_ext, trunc_ext]
  exact add_isRefinedBy_add x y nsw nuw


theorem sub_widening (h : w < W) (x y : LLVM.Int w) (m m' : BitVec (W - w)) (nsw nuw : Bool) :
    LLVM.Int.sub x y nsw nuw ⊒
      LLVM.Int.trunc (LLVM.Int.sub (LLVM.Int.ext x W m h) (LLVM.Int.ext y W m' h)) w false false h := by
  rw [trunc_sub, trunc_ext, trunc_ext]
  grind


theorem mul_widening (h : w < W) (x y : LLVM.Int w) (m m' : BitVec (W - w)) (nsw nuw : Bool) :
    LLVM.Int.mul x y nsw nuw ⊒
      LLVM.Int.trunc (LLVM.Int.mul (LLVM.Int.ext x W m h) (LLVM.Int.ext y W m' h)) w false false h := by
  rw [trunc_mul, trunc_ext, trunc_ext]
  grind


theorem and_widening (h : w < W) (x y : LLVM.Int w) (m m' : BitVec (W - w)) :
    LLVM.Int.and x y ⊒
      LLVM.Int.trunc (LLVM.Int.and (LLVM.Int.ext x W m h) (LLVM.Int.ext y W m' h)) w false false h := by
  rw [trunc_and, trunc_ext, trunc_ext]
  exact isRefinedBy_refl _


theorem or_widening (h : w < W) (x y : LLVM.Int w) (m m' : BitVec (W - w)) (disjoint : Bool) :
    LLVM.Int.or x y disjoint ⊒
      LLVM.Int.trunc (LLVM.Int.or (LLVM.Int.ext x W m h) (LLVM.Int.ext y W m' h)) w false false h := by
  rw [trunc_or, trunc_ext, trunc_ext]
  grind


theorem xor_widening (h : w < W) (x y : LLVM.Int w) (m m' : BitVec (W - w)) :
    LLVM.Int.xor x y ⊒
      LLVM.Int.trunc (LLVM.Int.xor (LLVM.Int.ext x W m h) (LLVM.Int.ext y W m' h)) w false false h := by
  rw [trunc_xor, trunc_ext, trunc_ext]
  exact isRefinedBy_refl _


/-- The shift amount, when it is below the width, as a bit vector of that width. -/

theorem setWidth_signExtend_signExtend {n : Nat} (h1 : n ≤ w) (h2 : w ≤ W) (c : BitVec n) :
    (c.signExtend W).setWidth w = c.signExtend w := by
  apply BitVec.eq_of_toInt_eq
  rw [toInt_setWidth_of_le h2, BitVec.toInt_signExtend_of_le (Nat.le_trans h1 h2),
    BitVec.toInt_signExtend_of_le h1, ← BitVec.toInt_signExtend_of_le h1 (x := c), bmod_toInt]


/-- `widenTypeGroup .g_smin (.type 0) .g_sext`: sign extension preserves the signed order, and
likewise for the other minimum and maximum operations. -/
theorem smin_widening (h : w < W) (x y : LLVM.Int w) :
    LLVM.Int.smin x y ⊒
      LLVM.Int.trunc (LLVM.Int.smin (LLVM.Int.sext x W h) (LLVM.Int.sext y W h)) w false false h := by
  cases x <;> cases y <;> simp [LLVM.Int.smin, LLVM.Int.sext, LLVM.Int.trunc, Id.run,
    signExtend_sle_signExtend (Nat.le_of_lt h)]
  split <;> simp [setWidth_signExtend_of_le (Nat.le_of_lt h)]


theorem smax_widening (h : w < W) (x y : LLVM.Int w) :
    LLVM.Int.smax x y ⊒
      LLVM.Int.trunc (LLVM.Int.smax (LLVM.Int.sext x W h) (LLVM.Int.sext y W h)) w false false h := by
  cases x <;> cases y <;> simp [LLVM.Int.smax, LLVM.Int.sext, LLVM.Int.trunc, Id.run,
    signExtend_sle_signExtend (Nat.le_of_lt h)]
  split <;> simp [setWidth_signExtend_of_le (Nat.le_of_lt h)]


theorem umin_widening (h : w < W) (x y : LLVM.Int w) :
    LLVM.Int.umin x y ⊒
      LLVM.Int.trunc (LLVM.Int.umin (LLVM.Int.sext x W h) (LLVM.Int.sext y W h)) w false false h := by
  cases x <;> cases y <;> simp [LLVM.Int.umin, LLVM.Int.sext, LLVM.Int.trunc, Id.run,
    signExtend_ule_signExtend (Nat.le_of_lt h)]
  split <;> simp [setWidth_signExtend_of_le (Nat.le_of_lt h)]


theorem umax_widening (h : w < W) (x y : LLVM.Int w) :
    LLVM.Int.umax x y ⊒
      LLVM.Int.trunc (LLVM.Int.umax (LLVM.Int.sext x W h) (LLVM.Int.sext y W h)) w false false h := by
  cases x <;> cases y <;> simp [LLVM.Int.umax, LLVM.Int.sext, LLVM.Int.trunc, Id.run,
    signExtend_ule_signExtend (Nat.le_of_lt h)]
  split <;> simp [setWidth_signExtend_of_le (Nat.le_of_lt h)]


/-- Sign extension to a wider width keeps the sign bit. -/
theorem msb_signExtend_of_lt (h : w < W) (x : BitVec w) : (x.signExtend W).msb = x.msb := by
  simp [BitVec.msb_signExtend, Nat.not_le.mpr h, show 0 < W by omega]


/-- `widenTypeGroup .g_abs (.type 0) .g_sext`: the absolute value of the sign-extended operand
truncated back. -/
theorem abs_widening (h : w < W) (x : LLVM.Int w) :
    LLVM.Int.abs x false ⊒
      LLVM.Int.trunc (LLVM.Int.abs (LLVM.Int.sext x W h) false) w false false h := by
  cases x <;> simp [LLVM.Int.abs, LLVM.Int.sext, LLVM.Int.trunc, Id.run, msb_signExtend_of_lt h]
  split <;> simp [setWidth_signExtend_of_le (Nat.le_of_lt h), BitVec.setWidth_neg_of_le (Nat.le_of_lt h)]


/-- A zero extension is zero exactly when its operand is. -/
theorem setWidth_eq_zero_iff_of_le (h : w ≤ W) (y : BitVec w) : y.setWidth W = 0#W ↔ y = 0#w := by
  rw [BitVec.toNat_eq, BitVec.toNat_eq, BitVec.toNat_setWidth_of_le h]; simp


/-- Unsigned division and remainder of zero-extended operands, truncated back. -/
theorem setWidth_udiv_setWidth (h : w ≤ W) (x y : BitVec w) :
    (x.setWidth W / y.setWidth W).setWidth w = x / y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_udiv, BitVec.toNat_setWidth_of_le h]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)


theorem setWidth_umod_setWidth (h : w ≤ W) (x y : BitVec w) :
    (x.setWidth W % y.setWidth W).setWidth w = x % y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_umod, BitVec.toNat_setWidth_of_le h]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.isLt)


theorem umod_setWidth_eq_zero_iff (h : w ≤ W) (x y : BitVec w) :
    x.setWidth W % y.setWidth W = 0#W ↔ x % y = 0#w := by
  rw [BitVec.toNat_eq, BitVec.toNat_eq, BitVec.toNat_umod, BitVec.toNat_umod,
    BitVec.toNat_setWidth_of_le h, BitVec.toNat_setWidth_of_le h]; simp


/-- `widenTypeGroup .g_udiv (.type 0) .g_zext`: the quotient of the zero-extended operands truncated
back, whatever the `exact` flag, and likewise for `g_urem`. -/
theorem udiv_widening (h : w < W) (x y : LLVM.Int w) (exact : Bool) :
    LLVM.Int.udiv x y exact ⊒
      LLVM.Int.trunc (LLVM.Int.udiv (LLVM.Int.zext x W false h) (LLVM.Int.zext y W false h) exact)
        w false false h := by
  cases x <;> cases y <;> simp [LLVM.Int.udiv, LLVM.Int.zext, LLVM.Int.trunc, Id.run, pure]
  rename_i x y
  have hle := Nat.le_of_lt h
  by_cases hex : exact = true ∧ ¬x % y = 0#w
  · simp [hex, pure]
  by_cases hy : y = 0#w
  · simp [hy, pure]
  simp [hex, hy, pure, umod_setWidth_eq_zero_iff hle, setWidth_eq_zero_iff_of_le hle,
    setWidth_udiv_setWidth hle]


theorem urem_widening (h : w < W) (x y : LLVM.Int w) :
    LLVM.Int.urem x y ⊒
      LLVM.Int.trunc (LLVM.Int.urem (LLVM.Int.zext x W false h) (LLVM.Int.zext y W false h))
        w false false h := by
  cases x <;> cases y <;> simp [LLVM.Int.urem, LLVM.Int.zext, LLVM.Int.trunc, Id.run, pure]
  rename_i x y
  have hle := Nat.le_of_lt h
  by_cases hy : y = 0#w
  · simp [hy, pure]
  simp [hy, pure, setWidth_eq_zero_iff_of_le hle, setWidth_umod_setWidth hle]


/-- A value sign-extended to a wider width is not the minimum of that width, so the only overflowing
signed division is of the narrow operands. -/
theorem signExtend_ne_intMin (h : w < W) (x : BitVec w) : x.signExtend W ≠ BitVec.intMin W := by
  intro heq
  have h1 := congrArg BitVec.toInt heq
  rw [BitVec.toInt_signExtend_of_le (Nat.le_of_lt h), BitVec.toInt_intMin_of_pos (by omega)] at h1
  have h2 := BitVec.le_toInt x
  rcases w with _ | w
  · rw [BitVec.toInt_of_zero_length rfl] at h1
    have : (1 : _root_.Int) ≤ 2 ^ (W - 1) := by exact_mod_cast Nat.one_le_two_pow
    omega
  · have : (2 : _root_.Int) ^ w < 2 ^ (W - 1) := by
      exact_mod_cast Nat.pow_lt_pow_right (by decide) (by omega)
    simp at h2
    omega


/-- Signed division, remainder and modulo of sign-extended operands, through their signed values. -/
theorem smod_signExtend_eq_zero_iff (h : w ≤ W) (x y : BitVec w) :
    (x.signExtend W).smod (y.signExtend W) = 0#W ↔ x.smod y = 0#w := by
  rw [← BitVec.toInt_inj, ← BitVec.toInt_inj, BitVec.toInt_smod, BitVec.toInt_smod,
    BitVec.toInt_signExtend_of_le h, BitVec.toInt_signExtend_of_le h, BitVec.toInt_zero, BitVec.toInt_zero]


theorem setWidth_sdiv_signExtend (h : w ≤ W) (x y : BitVec w) :
    ((x.signExtend W).sdiv (y.signExtend W)).setWidth w = x.sdiv y := by
  apply BitVec.eq_of_toInt_eq
  rw [toInt_setWidth_of_le h, BitVec.toInt_sdiv, BitVec.toInt_sdiv, BitVec.toInt_signExtend_of_le h,
    BitVec.toInt_signExtend_of_le h, Int.bmod_bmod_of_dvd (by exact_mod_cast Nat.pow_dvd_pow 2 h)]


theorem setWidth_srem_signExtend (h : w ≤ W) (x y : BitVec w) :
    ((x.signExtend W).srem (y.signExtend W)).setWidth w = x.srem y := by
  apply BitVec.eq_of_toInt_eq
  rw [toInt_setWidth_of_le h, ← bmod_toInt (x.srem y), BitVec.toInt_srem, BitVec.toInt_srem,
    BitVec.toInt_signExtend_of_le h, BitVec.toInt_signExtend_of_le h]


theorem signExtend_eq_zero_iff_of_le (h : w ≤ W) (y : BitVec w) : y.signExtend W = 0#W ↔ y = 0#w := by
  rw [← BitVec.toInt_inj, ← BitVec.toInt_inj, BitVec.toInt_signExtend_of_le h, BitVec.toInt_zero,
    BitVec.toInt_zero]


/-- `widenTypeGroup .g_sdiv (.type 0) .g_sext`: the quotient of the sign-extended operands truncated
back, whatever the `exact` flag, and likewise for `g_srem`. The narrow division of the minimum by
`-1` is poison, which any wide quotient refines. -/
theorem sdiv_widening (h : w < W) (x y : LLVM.Int w) (exact : Bool) :
    LLVM.Int.sdiv x y exact ⊒
      LLVM.Int.trunc (LLVM.Int.sdiv (LLVM.Int.sext x W h) (LLVM.Int.sext y W h) exact)
        w false false h := by
  cases x <;> cases y <;> simp [LLVM.Int.sdiv, LLVM.Int.sext, LLVM.Int.trunc, Id.run, pure]
  rename_i x y
  have hle := Nat.le_of_lt h
  by_cases hy : y = 0#w
  · simp [hy, pure]
  by_cases hmin : x = BitVec.intMin w ∧ y = -1#w
  · simp [hmin, pure]
  by_cases hex : exact = true ∧ ¬x.smod y = 0#w
  · simp [hy, hmin, hex, pure]
  simp [hy, hmin, hex, pure, signExtend_ne_intMin h, signExtend_eq_zero_iff_of_le hle,
    smod_signExtend_eq_zero_iff hle, setWidth_sdiv_signExtend hle]


theorem srem_widening (h : w < W) (x y : LLVM.Int w) :
    LLVM.Int.srem x y ⊒
      LLVM.Int.trunc (LLVM.Int.srem (LLVM.Int.sext x W h) (LLVM.Int.sext y W h)) w false false h := by
  cases x <;> cases y <;> simp [LLVM.Int.srem, LLVM.Int.sext, LLVM.Int.trunc, Id.run, pure]
  rename_i x y
  have hle := Nat.le_of_lt h
  by_cases hy : y = 0#w
  · simp [hy, pure]
  by_cases hmin : x = BitVec.intMin w ∧ y = -1#w
  · simp [hmin, pure]
  simp [hy, hmin, pure, signExtend_ne_intMin h, signExtend_eq_zero_iff_of_le hle,
    setWidth_srem_signExtend hle]


/-- A sign extension is `-1` only when its operand is. -/
theorem signExtend_eq_neg_one (h : w < W) (y : BitVec w) (hy : y.signExtend W = -1#W) : y = -1#w := by
  have h1 := congrArg BitVec.toInt hy
  rw [BitVec.toInt_signExtend_of_le (Nat.le_of_lt h), BitVec.neg_one_eq_allOnes, BitVec.toInt_allOnes] at h1
  simp only [show 0 < W by omega, ite_true] at h1
  rcases w with _ | w
  · rw [BitVec.toInt_of_zero_length rfl] at h1; omega
  · rw [← BitVec.toInt_inj, h1, BitVec.neg_one_eq_allOnes, BitVec.toInt_allOnes]
    simp


/-- The source of a widened division has undefined behavior whenever the division of the
sign-extended operands has. -/

theorem isSignedDivisionUB_sext (h : w < W) (x y : LLVM.Int w)
    (hub : LLVM.Int.isSignedDivisionUB (LLVM.Int.sext x W h) (LLVM.Int.sext y W h) = true) :
    LLVM.Int.isSignedDivisionUB x y = true := by
  have hn := signExtend_eq_neg_one h
  cases x <;> cases y <;> simp_all [LLVM.Int.isSignedDivisionUB, LLVM.Int.sext, Id.run,
    signExtend_ne_intMin h, signExtend_eq_zero_iff_of_le (Nat.le_of_lt h)]
  exact hub.imp id (hn _)


/-- A widened unsigned division has undefined behavior exactly when the narrow one has. -/
theorem isUnsignedDivisionUB_zext (h : w < W) (y : LLVM.Int w) :
    LLVM.Int.isUnsignedDivisionUB (LLVM.Int.zext y W false h) = LLVM.Int.isUnsignedDivisionUB y := by
  cases y <;> simp [LLVM.Int.isUnsignedDivisionUB, LLVM.Int.zext, Id.run,
    setWidth_eq_zero_iff_of_le (Nat.le_of_lt h)]


/-- The `exact` check of a right shift: the shifted-out bits are zero. -/
theorem ushiftRight_shiftLeft_eq_self_iff {n : Nat} (v : BitVec n) (k : Nat) :
    (v >>> k) <<< k = v ↔ v.toNat % 2 ^ k = 0 := by
  rw [BitVec.toNat_eq, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have h1 := Nat.div_add_mod v.toNat (2 ^ k)
  have h2 : v.toNat / 2 ^ k * 2 ^ k ≤ v.toNat := Nat.div_mul_le_self _ _
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h2 v.isLt)]
  rw [Nat.mul_comm] at h1
  omega


/-- Sign extension keeps the low bits. -/
theorem toNat_signExtend_mod {k : Nat} (h : w ≤ W) (hk : k ≤ w) (x : BitVec w) :
    (x.signExtend W).toNat % 2 ^ k = x.toNat % 2 ^ k := by
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth_of_le h]
  have hd : 2 ^ k ∣ 2 ^ W - 2 ^ w :=
    Nat.dvd_sub (Nat.pow_dvd_pow 2 (Nat.le_trans hk h)) (Nat.pow_dvd_pow 2 hk)
  obtain ⟨t, ht⟩ := hd
  split
  · rw [ht, Nat.add_mul_mod_self_left]
  · simp


/-- `widenTypeGroup .g_sext_inreg (.type 0) .g_anyext`: the sign extension of the low `sz` bits of
the any-extended operand, truncated back. -/
theorem sext_inreg_widening {sz : Nat} (h : w < W) (hs : sz < w) (x : LLVM.Int w) (m : BitVec (W - w)) :
    LLVM.Int.sext (LLVM.Int.trunc x sz false false hs) w hs ⊒
      LLVM.Int.trunc (LLVM.Int.sext (LLVM.Int.trunc (LLVM.Int.ext x W m h) sz false false (by omega)) W
        (by omega)) w false false h := by
  cases x <;> simp [LLVM.Int.sext, LLVM.Int.trunc, LLVM.Int.ext, LLVM.Int.cast, Id.run, pure,
    BitVec.setWidth_append, Nat.le_of_lt hs, setWidth_signExtend_signExtend (Nat.le_of_lt hs) (Nat.le_of_lt h)]


/-- A signed value does not wrap exactly when it is in range. -/
theorem bmod_two_pow_eq_self_iff (hw : 0 < w) (s : _root_.Int) :
    s.bmod (2 ^ w) = s ↔ -2 ^ (w - 1) ≤ s ∧ s < 2 ^ (w - 1) := by
  have h2 : (2 : _root_.Int) ^ w = 2 ^ (w - 1) * 2 := by
    rw [← Int.pow_succ]; congr 1; omega
  constructor
  · intro hs
    have h1 := Int.le_bmod (x := s) (m := 2 ^ w) (Nat.two_pow_pos w)
    have h3 := Int.bmod_lt (x := s) (m := 2 ^ w) (Nat.two_pow_pos w)
    rw [hs] at h1 h3
    push_cast at h1 h3
    omega
  · rintro ⟨h1, h3⟩
    exact bmod_two_pow_of_range hw h1 h3


/-- The low bits of a difference are the difference of the low bits. -/
theorem setWidth_sub_of_le (h : w ≤ W) (a b : BitVec W) :
    (a - b).setWidth w = a.setWidth w - b.setWidth w := by
  rw [BitVec.sub_eq_add_neg, BitVec.setWidth_add _ _ h, BitVec.setWidth_neg_of_le h, ← BitVec.sub_eq_add_neg]


/-- The inequality check of `g_icmp ne`, on the values of the bit-vectors. -/
theorem bne_eq_decide_toNat {n : Nat} (a b : BitVec n) : (a != b) = decide (a.toNat ≠ b.toNat) := by
  by_cases hab : a = b
  · subst hab; simp
  · have hn : a.toNat ≠ b.toNat := fun e => hab (BitVec.eq_of_toNat_eq e)
    simp [bne, hab, hn]


theorem bne_eq_decide_toInt {n : Nat} (a b : BitVec n) : (a != b) = decide (a.toInt ≠ b.toInt) := by
  by_cases hab : a = b
  · subst hab; simp
  · have hn : a.toInt ≠ b.toInt := fun e => hab (BitVec.eq_of_toInt_eq e)
    simp [bne, hab, hn]


/-- The sign extension of zero. -/
theorem signExtend_zero' : (0#w).signExtend W = 0#W := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_signExtend]


/-- `widenScalarAddSubOverflow .g_uaddo`: the sum of the zero-extended operands truncated back, which
overflows exactly when the wide sum does not survive the truncation and zero extension. -/
theorem uaddo_widening (h : w < W) (x y : LLVM.Int w) :
    LLVM.Int.add x y ⊒
      LLVM.Int.trunc (LLVM.Int.add (LLVM.Int.zext x W false h) (LLVM.Int.zext y W false h)) w false false h ∧
    LLVM.Int.uaddOverflowFlag x y ⊒
      LLVM.Int.icmp (LLVM.Int.add (LLVM.Int.zext x W false h) (LLVM.Int.zext y W false h))
        (LLVM.Int.zext (LLVM.Int.trunc (LLVM.Int.add (LLVM.Int.zext x W false h) (LLVM.Int.zext y W false h))
          w false false h) W false h) .ne := by
  cases x <;> cases y <;> simp [LLVM.Int.add, LLVM.Int.zext, LLVM.Int.trunc, LLVM.Int.uaddOverflowFlag,
    LLVM.Int.icmp, Id.run, pure, IntPred.eval]
  rename_i x y
  have hle := Nat.le_of_lt h
  have h2 : 2 ^ w * 2 ≤ 2 ^ W := by rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) h
  have hx := x.isLt
  have hy := y.isLt
  refine ⟨?_, ?_⟩
  · rw [BitVec.setWidth_add _ _ hle, BitVec.setWidth_setWidth_of_le _ hle,
      BitVec.setWidth_setWidth_of_le _ hle, BitVec.setWidth_eq, BitVec.setWidth_eq]
    exact isRefinedBy_refl _
  · have hS : x.toNat + y.toNat < 2 ^ W := by omega
    have hm := Nat.mod_lt (x.toNat + y.toNat) (Nat.two_pow_pos w)
    simp only [isRefinedBy_eq, BitVec.ofBool_eq_iff_eq, bne_eq_decide_toNat, BitVec.uaddOverflow,
      BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth_of_le hle, decide_eq_decide, ne_eq,
      Nat.mod_eq_of_lt hS, Nat.mod_eq_of_lt (show (x.toNat + y.toNat) % 2 ^ w < 2 ^ W by omega)]
    by_cases hs : x.toNat + y.toNat < 2 ^ w
    · rw [Nat.mod_eq_of_lt hs]; omega
    · omega


/-- `widenScalarAddSubOverflow .g_usubo`, as `uaddo_widening`: the wide difference wraps below
`2 ^ W - 2 ^ w` exactly when the narrow one borrows. -/
theorem usubo_widening (h : w < W) (x y : LLVM.Int w) :
    LLVM.Int.sub x y ⊒
      LLVM.Int.trunc (LLVM.Int.sub (LLVM.Int.zext x W false h) (LLVM.Int.zext y W false h)) w false false h ∧
    LLVM.Int.usubOverflowFlag x y ⊒
      LLVM.Int.icmp (LLVM.Int.sub (LLVM.Int.zext x W false h) (LLVM.Int.zext y W false h))
        (LLVM.Int.zext (LLVM.Int.trunc (LLVM.Int.sub (LLVM.Int.zext x W false h) (LLVM.Int.zext y W false h))
          w false false h) W false h) .ne := by
  cases x <;> cases y <;> simp [LLVM.Int.sub, LLVM.Int.zext, LLVM.Int.trunc, LLVM.Int.usubOverflowFlag,
    LLVM.Int.icmp, Id.run, pure, IntPred.eval]
  rename_i x y
  have hle := Nat.le_of_lt h
  have h2 : 2 ^ w * 2 ≤ 2 ^ W := by rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) h
  have hx := x.isLt
  have hy := y.isLt
  refine ⟨?_, ?_⟩
  · rw [setWidth_sub_of_le hle, BitVec.setWidth_setWidth_of_le _ hle,
      BitVec.setWidth_setWidth_of_le _ hle, BitVec.setWidth_eq, BitVec.setWidth_eq]
    exact isRefinedBy_refl _
  · have hm := Nat.mod_lt ((2 ^ W - y.toNat + x.toNat) % 2 ^ W) (Nat.two_pow_pos w)
    simp only [isRefinedBy_eq, BitVec.ofBool_eq_iff_eq, bne_eq_decide_toNat, BitVec.usubOverflow,
      BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_setWidth_of_le hle, decide_eq_decide, ne_eq,
      Nat.mod_eq_of_lt (show (2 ^ W - y.toNat + x.toNat) % 2 ^ W % 2 ^ w < 2 ^ W by omega)]
    by_cases hs : x.toNat < y.toNat
    · rw [Nat.mod_eq_of_lt (show 2 ^ W - y.toNat + x.toNat < 2 ^ W by omega)] at hm ⊢
      omega
    · have heq : (2 ^ W - y.toNat + x.toNat) % 2 ^ W = x.toNat - y.toNat := by
        rw [show 2 ^ W - y.toNat + x.toNat = (x.toNat - y.toNat) + 1 * 2 ^ W by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      rw [heq, Nat.mod_eq_of_lt (by omega : x.toNat - y.toNat < 2 ^ w)]
      omega


private theorem signed_sum_toInt (h : w < W) (hw : 0 < w) (x y : BitVec w) :
    (x.signExtend W + y.signExtend W).toInt = x.toInt + y.toInt ∧
    (x.signExtend W - y.signExtend W).toInt = x.toInt - y.toInt := by
  have hle := Nat.le_of_lt h
  have h1 := BitVec.le_toInt x
  have h2 := BitVec.toInt_lt (x := x)
  have h3 := BitVec.le_toInt y
  have h4 := BitVec.toInt_lt (x := y)
  have h5 : (2 : _root_.Int) ^ w ≤ 2 ^ (W - 1) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide) (by omega)
  have h6 : (2 : _root_.Int) ^ w = 2 ^ (w - 1) * 2 := by
    rw [← Int.pow_succ]; congr 1; omega
  constructor
  · rw [BitVec.toInt_add, BitVec.toInt_signExtend_of_le hle, BitVec.toInt_signExtend_of_le hle]
    exact bmod_two_pow_of_range (by omega) (by omega) (by omega)
  · rw [BitVec.toInt_sub, BitVec.toInt_signExtend_of_le hle, BitVec.toInt_signExtend_of_le hle]
    exact bmod_two_pow_of_range (by omega) (by omega) (by omega)


/-- `widenScalarAddSubOverflow .g_saddo`: the sum of the sign-extended operands does not wrap at the
wide width, so it survives the truncation and sign extension exactly when it is in the narrow
signed range. -/
theorem saddo_widening (h : w < W) (x y : LLVM.Int w) :
    LLVM.Int.add x y ⊒
      LLVM.Int.trunc (LLVM.Int.add (LLVM.Int.sext x W h) (LLVM.Int.sext y W h)) w false false h ∧
    LLVM.Int.saddOverflowFlag x y ⊒
      LLVM.Int.icmp (LLVM.Int.add (LLVM.Int.sext x W h) (LLVM.Int.sext y W h))
        (LLVM.Int.sext (LLVM.Int.trunc (LLVM.Int.add (LLVM.Int.sext x W h) (LLVM.Int.sext y W h))
          w false false h) W h) .ne := by
  cases x <;> cases y <;> simp [LLVM.Int.add, LLVM.Int.sext, LLVM.Int.trunc, LLVM.Int.saddOverflowFlag,
    LLVM.Int.icmp, Id.run, pure, IntPred.eval]
  rename_i x y
  have hle := Nat.le_of_lt h
  refine ⟨?_, ?_⟩
  · rw [BitVec.setWidth_add _ _ hle, setWidth_signExtend_of_le hle, setWidth_signExtend_of_le hle]
    exact isRefinedBy_refl _
  · simp only [isRefinedBy_eq, BitVec.ofBool_eq_iff_eq, bne_eq_decide_toInt]
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · simp [BitVec.of_length_zero (x := x), BitVec.of_length_zero (x := y), BitVec.saddOverflow,
        signExtend_zero']
    have hs := (signed_sum_toInt h hw x y).1
    have key : (x.toInt + y.toInt = (x.toInt + y.toInt).bmod (2 ^ w)) ↔
        (-2 ^ (w - 1) ≤ x.toInt + y.toInt ∧ x.toInt + y.toInt < 2 ^ (w - 1)) :=
      ⟨fun e => (bmod_two_pow_eq_self_iff hw _).mp e.symm,
        fun r => ((bmod_two_pow_eq_self_iff hw _).mpr r).symm⟩
    simp only [BitVec.saddOverflow, hs, BitVec.toInt_signExtend_of_le hle, toInt_setWidth_of_le hle, ne_eq, key]
    by_cases h1 : 2 ^ (w - 1) ≤ x.toInt + y.toInt <;> by_cases h2 : x.toInt + y.toInt < -2 ^ (w - 1) <;>
      simp [h1, h2] <;> omega


/-- `widenScalarAddSubOverflow .g_ssubo`, as `saddo_widening`. -/
theorem ssubo_widening (h : w < W) (x y : LLVM.Int w) :
    LLVM.Int.sub x y ⊒
      LLVM.Int.trunc (LLVM.Int.sub (LLVM.Int.sext x W h) (LLVM.Int.sext y W h)) w false false h ∧
    LLVM.Int.ssubOverflowFlag x y ⊒
      LLVM.Int.icmp (LLVM.Int.sub (LLVM.Int.sext x W h) (LLVM.Int.sext y W h))
        (LLVM.Int.sext (LLVM.Int.trunc (LLVM.Int.sub (LLVM.Int.sext x W h) (LLVM.Int.sext y W h))
          w false false h) W h) .ne := by
  cases x <;> cases y <;> simp [LLVM.Int.sub, LLVM.Int.sext, LLVM.Int.trunc, LLVM.Int.ssubOverflowFlag,
    LLVM.Int.icmp, Id.run, pure, IntPred.eval]
  rename_i x y
  have hle := Nat.le_of_lt h
  refine ⟨?_, ?_⟩
  · rw [setWidth_sub_of_le hle, setWidth_signExtend_of_le hle, setWidth_signExtend_of_le hle]
    exact isRefinedBy_refl _
  · simp only [isRefinedBy_eq, BitVec.ofBool_eq_iff_eq, bne_eq_decide_toInt]
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · simp [BitVec.of_length_zero (x := x), BitVec.of_length_zero (x := y), BitVec.ssubOverflow,
        signExtend_zero']
    have hs := (signed_sum_toInt h hw x y).2
    have key : (x.toInt - y.toInt = (x.toInt - y.toInt).bmod (2 ^ w)) ↔
        (-2 ^ (w - 1) ≤ x.toInt - y.toInt ∧ x.toInt - y.toInt < 2 ^ (w - 1)) :=
      ⟨fun e => (bmod_two_pow_eq_self_iff hw _).mp e.symm,
        fun r => ((bmod_two_pow_eq_self_iff hw _).mpr r).symm⟩
    simp only [BitVec.ssubOverflow, hs, BitVec.toInt_signExtend_of_le hle, toInt_setWidth_of_le hle, ne_eq, key]
    by_cases h1 : 2 ^ (w - 1) ≤ x.toInt - y.toInt <;> by_cases h2 : x.toInt - y.toInt < -2 ^ (w - 1) <;>
      simp [h1, h2] <;> omega


/-- `lowerSAddSubO true`: the sum overflows exactly when it is below `a` and `b` is not negative,
or the converse. -/

theorem saddo_lowering (x y : LLVM.Int w) :
    LLVM.Int.saddOverflowFlag x y ⊒
      LLVM.Int.xor (LLVM.Int.icmp y (.val 0#w) .slt) (LLVM.Int.icmp (LLVM.Int.add x y) x .slt) := by
  cases x <;> cases y <;> simp [LLVM.Int.saddOverflowFlag, LLVM.Int.xor, LLVM.Int.icmp, LLVM.Int.add,
    Id.run, pure, IntPred.eval, isRefinedBy_eq, BitVec.ofBool_xor_ofBool, BitVec.ofBool_eq_iff_eq,
    BitVec.slt_eq_decide, BitVec.toInt_zero, -BitVec.toInt_add]
  rename_i x y
  by_cases hov : BitVec.saddOverflow x y
  · have hmsb := hov
    rw [BitVec.saddOverflow_eq] at hmsb
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne,
      ne_eq, BitVec.msb_eq_toInt] at hmsb
    rw [hov]
    by_cases hx : x.toInt < 0 <;> by_cases hs : (x + y).toInt < 0 <;> by_cases hy : y.toInt < 0 <;>
      by_cases hz : (x + y).toInt < x.toInt <;> simp [hx, hs, hy, hz, -BitVec.toInt_add] at hmsb ⊢ <;> omega
  · simp only [Bool.not_eq_true] at hov
    rw [hov, BitVec.toInt_add_of_not_saddOverflow (by simp [hov])]
    by_cases hy : y.toInt < 0 <;> by_cases hz : x.toInt + y.toInt < x.toInt <;> simp [hy, hz] <;> omega


/-- `lowerSAddSubO false`: the difference overflows exactly when `a <s b` and it is not negative,
or the converse. -/

theorem ssubo_lowering (x y : LLVM.Int w) :
    LLVM.Int.ssubOverflowFlag x y ⊒
      LLVM.Int.xor (LLVM.Int.icmp x y .slt) (LLVM.Int.icmp (LLVM.Int.sub x y) (.val 0#w) .slt) := by
  cases x <;> cases y <;> simp [LLVM.Int.ssubOverflowFlag, LLVM.Int.xor, LLVM.Int.icmp, LLVM.Int.sub,
    Id.run, pure, IntPred.eval, isRefinedBy_eq, BitVec.ofBool_xor_ofBool, BitVec.ofBool_eq_iff_eq,
    BitVec.slt_eq_decide, BitVec.toInt_zero, -BitVec.toInt_sub]
  rename_i x y
  by_cases hov : BitVec.ssubOverflow x y
  · have hmsb := hov
    rw [BitVec.ssubOverflow_eq] at hmsb
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      BitVec.msb_eq_toInt, decide_eq_true_eq, decide_eq_false_iff_not] at hmsb
    rw [hov]
    by_cases hx : x.toInt < 0 <;> by_cases hy : y.toInt < 0 <;> by_cases hd : (x - y).toInt < 0 <;>
      by_cases hxy : x.toInt < y.toInt <;> simp [hx, hy, hd, hxy, -BitVec.toInt_sub] at hmsb ⊢ <;> omega
  · simp only [Bool.not_eq_true] at hov
    rw [hov, BitVec.toInt_sub_of_not_ssubOverflow (by simp [hov])]
    by_cases hxy : x.toInt < y.toInt <;> by_cases hd : x.toInt - y.toInt < 0 <;> simp [hxy, hd] <;> omega

/-- The overflow flag of `lowerUAddSubO true`: the sum carries exactly when it is below `b`. -/
theorem uaddo_flag_lowering (x y : LLVM.Int w) :
    LLVM.Int.uaddOverflowFlag x y ⊒ LLVM.Int.icmp (LLVM.Int.add x y) y .ult := by
  have := congrArg Prod.snd (uaddo_lowering x y)
  simp only at this
  rw [this]
  exact isRefinedBy_refl _

/-- The overflow flag of `lowerUAddSubO false`: the difference borrows exactly when `a <u b`. -/
theorem usubo_flag_lowering (x y : LLVM.Int w) :
    LLVM.Int.usubOverflowFlag x y ⊒ LLVM.Int.icmp x y .ult := by
  have := congrArg Prod.snd (usubo_lowering x y)
  simp only at this
  rw [this]
  exact isRefinedBy_refl _

/-- `widenConstant`: a wide constant truncated back is the narrow constant, whatever the value
it was created with is modulo `2 ^ w`. -/
theorem trunc_ofInt_of_bmod_eq (h : w < W) {v v' : _root_.Int}
    (hv : v'.bmod (2 ^ w) = v.bmod (2 ^ w)) :
    LLVM.Int.trunc (.val (BitVec.ofInt W v')) w false false h = .val (BitVec.ofInt w v) := by
  simp only [LLVM.Int.trunc, Id.run, Bool.false_and, Bool.false_eq_true, ite_false, BitVec.truncate_eq_setWidth]
  congr 1
  apply BitVec.eq_of_toInt_eq
  rw [toInt_setWidth_of_le (Nat.le_of_lt h), BitVec.toInt_ofInt, BitVec.toInt_ofInt,
    Int.bmod_bmod_of_dvd (by exact_mod_cast Nat.pow_dvd_pow 2 (Nat.le_of_lt h)), hv]

/-- The value `widenConstant` creates the wide constant with, as `LLVM::getExtOpcodeForWideningConstant`
chooses it: the value itself for a width that is a multiple of 8, else its bits as an unsigned
integer, is the constant's value modulo `2 ^ w`. -/
theorem widenConstant_value_bmod (w : Nat) (v : _root_.Int) :
    (if w % 8 = 0 then v else ((BitVec.ofInt w v).toNat : _root_.Int)).bmod (2 ^ w) = v.bmod (2 ^ w) := by
  split
  · rfl
  · rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast Nat.ne_of_gt (Nat.two_pow_pos w)))]
    exact Int.emod_bmod v (2 ^ w)

/-- A zero-extended value truncated back is the value. -/
theorem trunc_zext {n m : Nat} (h : n < m) (x : LLVM.Int n) :
    LLVM.Int.trunc (LLVM.Int.zext x m false h) n false false h = x := by
  cases x <;> simp [LLVM.Int.zext, LLVM.Int.trunc, Id.run, BitVec.setWidth_setWidth_of_le _ (Nat.le_of_lt h)]

/-- An any-extended value truncated to an intermediate width is the value any-extended with the
low bits of the chosen high bits. -/
theorem trunc_ext_of_lt {s w W : Nat} (h1 : s < w) (h2 : w < W) (v : LLVM.Int s) (m : BitVec (W - s)) :
    LLVM.Int.trunc (LLVM.Int.ext v W m (by omega)) w false false h2 =
      LLVM.Int.ext v w (m.setWidth (w - s)) h1 := by
  cases v <;> simp [LLVM.Int.ext, LLVM.Int.trunc, LLVM.Int.cast, Id.run, BitVec.setWidth_append,
    Nat.not_le.mpr h1]

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

/-! ## gMIR combines at every width

The local correctness lemmas of the gMIR combines of `Veir.Passes.Legalization.CombinerHelper`, at
every width and whatever the flags of the matched operations, which only add poison to the source.
`combine_tac` unfolds the operations, splits their poison checks, and closes the remaining
bit-vector identity with `simp`, `omega` or `grind`'s ring solver. The interpreters are written in
the `Id` monad, so their poison checks are equations at `Id (LLVM.Int w)`, which the `_id` lemmas
below rewrite. -/

section Combines

/- Each case split of `combine_tac` uses part of its simp set. -/
set_option linter.unusedSimpArgs false

theorem ite_poison_eq_val_id {w : Nat} {c : Prop} [inst : Decidable c] {e : Id (LLVM.Int w)}
    {v : BitVec w} :
    @Eq (Id (LLVM.Int w)) (@ite (Id (LLVM.Int w)) c inst (@LLVM.Int.poison w) e)
      (@LLVM.Int.val w v) ↔ ¬c ∧ @Eq (Id (LLVM.Int w)) e (@LLVM.Int.val w v) := by
  split <;> simp_all

theorem val_eq_val_id {w : Nat} {a b : BitVec w} :
    @Eq (Id (LLVM.Int w)) (@LLVM.Int.val w a) (@LLVM.Int.val w b) ↔ a = b := by
  simp [Id]

theorem poison_eq_val_id {w : Nat} {b : BitVec w} :
    @Eq (Id (LLVM.Int w)) (@LLVM.Int.poison w) (@LLVM.Int.val w b) ↔ False := by
  simp [Id]

theorem reverse_shiftLeft_reverse {w : Nat} (x : BitVec w) (n : Nat) :
    (x.reverse <<< n).reverse = x >>> n := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_reverse, BitVec.getMsbD_eq_getLsbD, BitVec.getElem_ushiftRight]
  simp only [hi, decide_true, Bool.true_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_reverse,
    BitVec.getMsbD_eq_getLsbD]
  by_cases h : w - 1 - i < n
  · simp only [h, decide_true, Bool.not_true, Bool.and_false, Bool.false_and]
    rw [BitVec.getLsbD_of_ge _ _ (by omega)]
  · simp only [h, decide_false, Bool.not_false, Bool.true_and, Bool.and_true,
      show w - 1 - i < w by omega, decide_true, show w - 1 - i - n < w by omega]
    congr 1
    omega

theorem reverse_ushiftRight_reverse {w : Nat} (x : BitVec w) (n : Nat) :
    (x.reverse >>> n).reverse = x <<< n := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_reverse, BitVec.getMsbD_eq_getLsbD, BitVec.getElem_shiftLeft]
  simp only [hi, decide_true, Bool.true_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_reverse,
    BitVec.getMsbD_eq_getLsbD]
  by_cases h : i < n
  · simp only [h, decide_true, Bool.not_true, Bool.false_and, show ¬ n + (w - 1 - i) < w by omega,
      decide_false, Bool.false_and]
  · simp only [h, decide_false, Bool.not_false, Bool.true_and, show n + (w - 1 - i) < w by omega,
      decide_true]
    rw [← BitVec.getLsbD_eq_getElem]
    congr 1
    omega

open Lean Meta in
/-- Split, recursively, each local conjunction, e.g. the poison checks an operation passed. -/
private meta partial def casesAnd (goal : MVarId) : MetaM (List MVarId) :=
  goal.withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      unless (← instantiateMVars decl.type).isAppOfArity ``And 2 do continue
      let subgoals ← goal.cases decl.fvarId
      return (← subgoals.toList.mapM fun subgoal => casesAnd subgoal.mvarId).flatten
    return [goal]

open Lean Elab Tactic in
local elab "casesAnd" : tactic => do
  let goals ← getGoals
  setGoals (← goals.flatMapM fun goal => casesAnd goal)

local macro "llvm_refines" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  (repeat' split) <;>
    try simp_all [poison_isRefinedBy, isRefinedBy_refl, isRefinedBy_eq, ite_poison_eq_val_id, val_eq_val_id,
      poison_eq_val_id, $ls,*]
  all_goals casesAnd
  all_goals (try subst_vars)
  all_goals try simp_all [poison_isRefinedBy, isRefinedBy_refl, isRefinedBy_eq, ite_poison_eq_val_id, val_eq_val_id,
      poison_eq_val_id, $ls,*]
  all_goals try (simp only [BitVec.le_def, BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_two_pow_self,
    BitVec.natCast_eq_ofNat, ge_iff_le] at *; omega)
  all_goals grind))


local macro "combine_tac" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [Int.add, Int.sub, Int.and, Int.or, Int.xor, Int.shl, Int.lshr, Int.ashr, Int.icmp, Int.zext,
    Int.sext, Int.trunc, Int.bitreverse, Int.smin, Int.smax, Int.umin, Int.umax, GMIR.selectNonzero,
    Id.run, pure]
  llvm_refines [$ls,*]))

variable {w : Nat}

/-! ### Hoisting a logic operation over the hands of its operands -/

theorem hoist_and_shl (x y s : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool) :
    (x.shl s n₁ u₁).and (y.shl s n₂ u₂) ⊒ (x.and y).shl s := by
  cases x <;> cases y <;> cases s <;> combine_tac [BitVec.shiftLeft_and_distrib]

theorem hoist_or_shl (x y s : LLVM.Int w) (n₁ u₁ n₂ u₂ d : Bool) :
    (x.shl s n₁ u₁).or (y.shl s n₂ u₂) d ⊒ (x.or y).shl s := by
  cases x <;> cases y <;> cases s <;> combine_tac [BitVec.shiftLeft_or_distrib]

theorem hoist_xor_shl (x y s : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool) :
    (x.shl s n₁ u₁).xor (y.shl s n₂ u₂) ⊒ (x.xor y).shl s := by
  cases x <;> cases y <;> cases s <;> combine_tac [BitVec.shiftLeft_xor_distrib]

theorem hoist_and_lshr (x y s : LLVM.Int w) (e₁ e₂ : Bool) :
    (x.lshr s e₁).and (y.lshr s e₂) ⊒ (x.and y).lshr s := by
  cases x <;> cases y <;> cases s <;> combine_tac [BitVec.ushiftRight_and_distrib]

theorem hoist_or_lshr (x y s : LLVM.Int w) (e₁ e₂ d : Bool) :
    (x.lshr s e₁).or (y.lshr s e₂) d ⊒ (x.or y).lshr s := by
  cases x <;> cases y <;> cases s <;> combine_tac [BitVec.ushiftRight_or_distrib]

theorem hoist_xor_lshr (x y s : LLVM.Int w) (e₁ e₂ : Bool) :
    (x.lshr s e₁).xor (y.lshr s e₂) ⊒ (x.xor y).lshr s := by
  cases x <;> cases y <;> cases s <;> combine_tac [BitVec.ushiftRight_xor_distrib]

theorem hoist_and_ashr (x y s : LLVM.Int w) (e₁ e₂ : Bool) :
    (x.ashr s e₁).and (y.ashr s e₂) ⊒ (x.and y).ashr s := by
  cases x <;> cases y <;> cases s <;> combine_tac [BitVec.sshiftRight_and_distrib, BitVec.sshiftRight_eq']

theorem hoist_or_ashr (x y s : LLVM.Int w) (e₁ e₂ d : Bool) :
    (x.ashr s e₁).or (y.ashr s e₂) d ⊒ (x.or y).ashr s := by
  cases x <;> cases y <;> cases s <;> combine_tac [BitVec.sshiftRight_or_distrib, BitVec.sshiftRight_eq']

theorem hoist_xor_ashr (x y s : LLVM.Int w) (e₁ e₂ : Bool) :
    (x.ashr s e₁).xor (y.ashr s e₂) ⊒ (x.xor y).ashr s := by
  cases x <;> cases y <;> cases s <;> combine_tac [BitVec.sshiftRight_xor_distrib, BitVec.sshiftRight_eq']

theorem and_and_and_right (x y z : BitVec w) : x &&& z &&& (y &&& z) = x &&& y &&& z := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem xor_and_and_right (x y z : BitVec w) : x &&& z ^^^ y &&& z = (x ^^^ y) &&& z := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_xor]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem hoist_and_and (x y z : LLVM.Int w) : (x.and z).and (y.and z) ⊒ (x.and y).and z := by
  cases x <;> cases y <;> cases z <;> combine_tac [and_and_and_right]

theorem hoist_or_and (x y z : LLVM.Int w) (d : Bool) : (x.and z).or (y.and z) d ⊒ (x.or y).and z := by
  cases x <;> cases y <;> cases z <;> combine_tac [BitVec.and_or_distrib_right]

theorem hoist_xor_and (x y z : LLVM.Int w) : (x.and z).xor (y.and z) ⊒ (x.xor y).and z := by
  cases x <;> cases y <;> cases z <;> combine_tac [xor_and_and_right]

/-! ### Additive identities -/

theorem sub_add_reg_x_add_y_sub_y (x y : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool) :
    (x.add y n₁ u₁).sub y n₂ u₂ ⊒ x := by
  cases x <;> cases y <;> combine_tac [BitVec.add_sub_cancel]

theorem sub_add_reg_x_add_y_sub_x (x y : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool) :
    (x.add y n₁ u₁).sub x n₂ u₂ ⊒ y := by
  cases x <;> cases y <;> combine_tac []

theorem sub_add_reg_negate (x y : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool) :
    x.sub (y.add x n₁ u₁) n₂ u₂ ⊒ (LLVM.Int.val 0#w).sub y := by
  cases x <;> cases y <;> combine_tac []

theorem sub_add_reg_negate_x_first (x y : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool) :
    x.sub (x.add y n₁ u₁) n₂ u₂ ⊒ (LLVM.Int.val 0#w).sub y := by
  cases x <;> cases y <;> combine_tac []

theorem add_sub_reg_0 (x y : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool) : x.add (y.sub x n₁ u₁) n₂ u₂ ⊒ y := by
  cases x <;> cases y <;> combine_tac []

theorem add_sub_reg_1 (x y : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool) : (y.sub x n₁ u₁).add x n₂ u₂ ⊒ y := by
  cases x <;> cases y <;> combine_tac []

theorem same_val_zero_sub (x : LLVM.Int w) (n u : Bool) : x.sub x n u ⊒ LLVM.Int.val 0#w := by
  cases x <;> combine_tac []

theorem same_val_zero_xor (x : LLVM.Int w) : x.xor x ⊒ LLVM.Int.val 0#w := by
  cases x <;> combine_tac []

theorem binop_same_val_and (x : LLVM.Int w) : x.and x ⊒ x := by
  cases x <;> combine_tac []

theorem binop_same_val_or (x : LLVM.Int w) (d : Bool) : x.or x d ⊒ x := by
  cases x <;> combine_tac []

theorem APlusBMinusCMinusB (a b c : LLVM.Int w) (n₁ u₁ n₂ u₂ n₃ u₃ : Bool) :
    (a.add (b.sub c n₁ u₁) n₂ u₂).sub b n₃ u₃ ⊒ a.sub c := by
  cases a <;> cases b <;> cases c <;> combine_tac []

theorem AMinusBMinusCMinusC (a b c : LLVM.Int w) (n₁ u₁ n₂ u₂ n₃ u₃ : Bool) :
    (a.sub (b.sub c n₁ u₁) n₂ u₂).sub c n₃ u₃ ⊒ a.sub b := by
  cases a <;> cases b <;> cases c <;> combine_tac []

theorem AMinusBPlusCMinusA (a b c : LLVM.Int w) (n₁ u₁ n₂ u₂ n₃ u₃ : Bool) :
    (a.sub b n₁ u₁).add (c.sub a n₂ u₂) n₃ u₃ ⊒ c.sub b := by
  cases a <;> cases b <;> cases c <;> combine_tac []

theorem AMinusBPlusBMinusC (a b c : LLVM.Int w) (n₁ u₁ n₂ u₂ n₃ u₃ : Bool) :
    (a.sub b n₁ u₁).add (b.sub c n₂ u₂) n₃ u₃ ⊒ a.sub c := by
  cases a <;> cases b <;> cases c <;> combine_tac []

theorem APlusBMinusAPlusC (a b c : LLVM.Int w) (n₁ u₁ n₂ u₂ n₃ u₃ : Bool) :
    a.add (b.sub (a.add c n₁ u₁) n₂ u₂) n₃ u₃ ⊒ b.sub c := by
  cases a <;> cases b <;> cases c <;> combine_tac []

theorem APlusBMinusCPlusA (a b c : LLVM.Int w) (n₁ u₁ n₂ u₂ n₃ u₃ : Bool) :
    a.add (b.sub (c.add a n₁ u₁) n₂ u₂) n₃ u₃ ⊒ b.sub c := by
  cases a <;> cases b <;> cases c <;> combine_tac []

theorem AMinusBMinusA (a b : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool) : a.sub (a.sub b n₁ u₁) n₂ u₂ ⊒ b := by
  cases a <;> cases b <;> combine_tac []

theorem AMinusBMinusC (a b c : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool) :
    a.sub (b.sub c n₁ u₁) n₂ u₂ ⊒ a.add (c.sub b) := by
  cases a <;> cases b <;> cases c <;> combine_tac []


theorem xor_of_and_with_same_reg (x y : LLVM.Int w) :
    (x.and y).xor y ⊒ (x.xor (.val (BitVec.ofInt w (-1)))).and y := by
  have : BitVec.ofInt w (-1) = BitVec.allOnes w := by
    rw [show (-1 : _root_.Int) = _root_.Int.negSucc 0 from rfl, BitVec.ofInt_negSucc_eq_not_ofNat]
    simp
  have hb : ∀ a b : BitVec w, a &&& b ^^^ b = (a ^^^ BitVec.allOnes w) &&& b := by
    intro a b
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp only [BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_allOnes]
    cases a[i] <;> cases b[i] <;> rfl
  cases x <;> cases y <;> combine_tac [this, hb]

theorem combine_or_of_and_left (x y : LLVM.Int w) (d : Bool) : (x.and y).or x d ⊒ x := by
  cases x <;> cases y <;> combine_tac [BitVec.and_or_self]

theorem combine_or_of_and_left' (x y : LLVM.Int w) (d : Bool) : (y.and x).or x d ⊒ x := by
  cases x <;> cases y <;> combine_tac [BitVec.and_comm, BitVec.and_or_self]

theorem combine_or_of_and_right (x y : LLVM.Int w) (d : Bool) : x.or (x.and y) d ⊒ x := by
  cases x <;> cases y <;> combine_tac [BitVec.or_and_self]

theorem combine_or_of_and_right' (x y : LLVM.Int w) (d : Bool) : x.or (y.and x) d ⊒ x := by
  cases x <;> cases y <;> combine_tac [BitVec.and_comm, BitVec.or_and_self]

/-! ### Casts of casts -/

theorem trunc_of_zext {W : Nat} (x : LLVM.Int w) (h : w < W) (h' : W > w) (nneg nsw nuw : Bool) :
    (x.zext W nneg h).trunc w nsw nuw h' ⊒ x := by
  cases x <;> combine_tac [BitVec.truncate_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (Nat.le_of_lt h)]

theorem trunc_of_sext {W : Nat} (x : LLVM.Int w) (h : w < W) (h' : W > w) (nsw nuw : Bool) :
    (x.sext W h).trunc w nsw nuw h' ⊒ x := by
  cases x <;> combine_tac [BitVec.truncate_eq_setWidth, BitVec.setWidth_signExtend_eq_self]

theorem zext_of_zext {M W : Nat} (x : LLVM.Int w) (h₁ : w < M) (h₂ : M < W) (h₃ : w < W)
    (n₁ n₂ : Bool) : (x.zext M n₁ h₁).zext W n₂ h₂ ⊒ x.zext W false h₃ := by
  cases x <;> combine_tac [BitVec.setWidth_setWidth_of_le _ (Nat.le_of_lt h₁)]

theorem sext_of_sext {M W : Nat} (x : LLVM.Int w) (h₁ : w < M) (h₂ : M < W) (h₃ : w < W) :
    (x.sext M h₁).sext W h₂ ⊒ x.sext W h₃ := by
  cases x <;> combine_tac [BitVec.signExtend_signExtend_of_le (Nat.le_of_lt h₁)]

/-- Zero extension without `nneg` keeps refinement both ways. -/
theorem zext_isRefinedBy_zext {W : Nat} (x y : LLVM.Int w) (h : w < W) :
    x.zext W false h ⊒ y.zext W false h ↔ x ⊒ y := by
  cases x <;> cases y <;> simp [Int.zext, Id.run, isRefinedBy_eq, poison_isRefinedBy, pure]
  rename_i a b
  constructor
  · intro hab
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat hab
    have hW : 2 ^ w ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt h)
    simpa [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.isLt hW),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt hW)] using this
  · rintro rfl; rfl

/-! ### Bit reverse of a shifted bit reverse -/

theorem bitreverse_shl (x s : LLVM.Int w) (n u : Bool) :
    (x.bitreverse.shl s n u).bitreverse ⊒ x.lshr s := by
  cases x <;> cases s <;> combine_tac [reverse_shiftLeft_reverse]

theorem bitreverse_lshr (x s : LLVM.Int w) (e : Bool) :
    (x.bitreverse.lshr s e).bitreverse ⊒ x.shl s := by
  cases x <;> cases s <;> combine_tac [reverse_ushiftRight_reverse]

/-! ### Comparisons against a binary operation of the compared value -/

theorem add_eq_self (x y : LLVM.Int w) (n u : Bool) :
    (x.add y n u).icmp x .eq ⊒ y.icmp (.val 0#w) .eq := by
  cases x <;> cases y <;> combine_tac [IntPred.eval]

theorem add_ne_self (x y : LLVM.Int w) (n u : Bool) :
    (x.add y n u).icmp x .ne ⊒ y.icmp (.val 0#w) .ne := by
  cases x <;> cases y <;> combine_tac [IntPred.eval]

theorem sub_eq_self (x y : LLVM.Int w) (n u : Bool) :
    (x.sub y n u).icmp x .eq ⊒ y.icmp (.val 0#w) .eq := by
  cases x <;> cases y <;> combine_tac [IntPred.eval]

theorem sub_ne_self (x y : LLVM.Int w) (n u : Bool) :
    (x.sub y n u).icmp x .ne ⊒ y.icmp (.val 0#w) .ne := by
  cases x <;> cases y <;> combine_tac [IntPred.eval]

theorem xor_eq_self_iff (x y : BitVec w) : (x ^^^ y = x) ↔ y = 0#w := by
  constructor
  · intro h
    have := congrArg (x ^^^ ·) h
    simpa [← BitVec.xor_assoc] using this
  · rintro rfl
    simp

theorem xor_beq_self (x y : BitVec w) : (x ^^^ y == x) = (y == 0#w) := by
  rw [Bool.eq_iff_iff]
  simp [xor_eq_self_iff]

theorem xor_eq_self (x y : LLVM.Int w) : (x.xor y).icmp x .eq ⊒ y.icmp (.val 0#w) .eq := by
  cases x <;> cases y <;> simp [Int.xor, Int.icmp, Id.run, pure, IntPred.eval, isRefinedBy_eq, xor_beq_self]

theorem xor_ne_self (x y : LLVM.Int w) : (x.xor y).icmp x .ne ⊒ y.icmp (.val 0#w) .ne := by
  cases x <;> cases y <;> simp [Int.xor, Int.icmp, Id.run, pure, IntPred.eval, isRefinedBy_eq, xor_beq_self, bne]

theorem ofBool_eq_zero (b : Bool) : (BitVec.ofBool b = 0#1) ↔ b = false := by
  cases b <;> decide

/-- Closes the select-to-min/max lemmas: both sides pick the same operand. -/
local macro "select_minmax_tac" : tactic => `(tactic| (
  simp [Int.icmp, Int.umax, Int.umin, Int.smax, Int.smin, GMIR.selectNonzero, Id.run, pure, IntPred.eval,
    poison_isRefinedBy, ofBool_eq_zero]
  all_goals (repeat' split)
  all_goals simp_all [BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle, isRefinedBy_eq]
  all_goals first | omega | (apply BitVec.eq_of_toNat_eq; omega) | (apply BitVec.eq_of_toInt_eq; omega)))

/-! ### Selects -/

theorem select_same_val {wc : Nat} (c : LLVM.Int wc) (x : LLVM.Int w) : GMIR.selectNonzero c x x ⊒ x := by
  cases c <;> cases x <;> combine_tac []

theorem select_ugt_umax (x y : LLVM.Int w) : GMIR.selectNonzero (x.icmp y .ugt) x y ⊒ x.umax y := by
  cases x <;> cases y <;> select_minmax_tac

theorem select_uge_umax (x y : LLVM.Int w) : GMIR.selectNonzero (x.icmp y .uge) x y ⊒ x.umax y := by
  cases x <;> cases y <;> select_minmax_tac

theorem select_sgt_smax (x y : LLVM.Int w) : GMIR.selectNonzero (x.icmp y .sgt) x y ⊒ x.smax y := by
  cases x <;> cases y <;> select_minmax_tac

theorem select_sge_smax (x y : LLVM.Int w) : GMIR.selectNonzero (x.icmp y .sge) x y ⊒ x.smax y := by
  cases x <;> cases y <;> select_minmax_tac

theorem select_ult_umin (x y : LLVM.Int w) : GMIR.selectNonzero (x.icmp y .ult) x y ⊒ x.umin y := by
  cases x <;> cases y <;> select_minmax_tac

theorem select_ule_umin (x y : LLVM.Int w) : GMIR.selectNonzero (x.icmp y .ule) x y ⊒ x.umin y := by
  cases x <;> cases y <;> select_minmax_tac

theorem select_slt_smin (x y : LLVM.Int w) : GMIR.selectNonzero (x.icmp y .slt) x y ⊒ x.smin y := by
  cases x <;> cases y <;> select_minmax_tac

theorem select_sle_smin (x y : LLVM.Int w) : GMIR.selectNonzero (x.icmp y .sle) x y ⊒ x.smin y := by
  cases x <;> cases y <;> select_minmax_tac

theorem zext_of_select {wc W : Nat} (c : LLVM.Int wc) (x y : LLVM.Int w) (h : w < W) (nneg : Bool) :
    (GMIR.selectNonzero c x y).zext W nneg h ⊒
      GMIR.selectNonzero c (x.zext W false h) (y.zext W false h) := by
  cases c <;> cases x <;> cases y <;> combine_tac []

theorem trunc_of_select {wc W : Nat} (c : LLVM.Int wc) (x y : LLVM.Int W) (h : W > w) (nsw nuw : Bool) :
    (GMIR.selectNonzero c x y).trunc w nsw nuw h ⊒
      GMIR.selectNonzero c (x.trunc w false false h) (y.trunc w false false h) := by
  cases c <;> cases x <;> cases y <;> combine_tac []

/-! ### Selects of a binary operation on the other arm, with the arms exchanged -/

theorem select_into_add_swapped {wc : Nat} (c : LLVM.Int wc) (x k : LLVM.Int w) (n u : Bool) :
    GMIR.selectNonzero c x (x.add k n u) ⊒ x.add (GMIR.selectNonzero c (.val 0#w) k) := by
  cases c <;> cases x <;> cases k <;> combine_tac []

theorem select_into_add' {wc : Nat} (c : LLVM.Int wc) (x k : LLVM.Int w) (n u : Bool) :
    GMIR.selectNonzero c (x.add k n u) x ⊒ x.add (GMIR.selectNonzero c k (.val 0#w)) := by
  cases c <;> cases x <;> cases k <;> combine_tac []

theorem select_into_sub_swapped {wc : Nat} (c : LLVM.Int wc) (x k : LLVM.Int w) (n u : Bool) :
    GMIR.selectNonzero c x (x.sub k n u) ⊒ x.sub (GMIR.selectNonzero c (.val 0#w) k) := by
  cases c <;> cases x <;> cases k <;> combine_tac []

theorem select_into_sub' {wc : Nat} (c : LLVM.Int wc) (x k : LLVM.Int w) (n u : Bool) :
    GMIR.selectNonzero c (x.sub k n u) x ⊒ x.sub (GMIR.selectNonzero c k (.val 0#w)) := by
  cases c <;> cases x <;> cases k <;> combine_tac []

theorem select_into_or_swapped {wc : Nat} (c : LLVM.Int wc) (x k : LLVM.Int w) (d : Bool) :
    GMIR.selectNonzero c x (x.or k d) ⊒ x.or (GMIR.selectNonzero c (.val 0#w) k) := by
  cases c <;> cases x <;> cases k <;> combine_tac []

theorem select_into_or' {wc : Nat} (c : LLVM.Int wc) (x k : LLVM.Int w) (d : Bool) :
    GMIR.selectNonzero c (x.or k d) x ⊒ x.or (GMIR.selectNonzero c k (.val 0#w)) := by
  cases c <;> cases x <;> cases k <;> combine_tac []

theorem select_into_xor_swapped {wc : Nat} (c : LLVM.Int wc) (x k : LLVM.Int w) :
    GMIR.selectNonzero c x (x.xor k) ⊒ x.xor (GMIR.selectNonzero c (.val 0#w) k) := by
  cases c <;> cases x <;> cases k <;> combine_tac []

theorem select_into_xor' {wc : Nat} (c : LLVM.Int wc) (x k : LLVM.Int w) :
    GMIR.selectNonzero c (x.xor k) x ⊒ x.xor (GMIR.selectNonzero c k (.val 0#w)) := by
  cases c <;> cases x <;> cases k <;> combine_tac []

/-! ### Combines of a matched constant

The constant `c` is matched at the width of its result (see `matchConstant`), and the hypotheses on
it are the predicates of its matcher.
-/

theorem ofInt_toInt_add (x y : BitVec w) : BitVec.ofInt w (x.toInt + y.toInt) = x + y := by
  apply BitVec.eq_of_toInt_eq; simp [BitVec.toInt_ofInt, BitVec.toInt_add]

theorem ofInt_toInt_sub (x y : BitVec w) : BitVec.ofInt w (x.toInt - y.toInt) = x - y := by
  apply BitVec.eq_of_toInt_eq; simp [BitVec.toInt_ofInt, BitVec.toInt_sub]

theorem ofInt_toInt_mul (x y : BitVec w) : BitVec.ofInt w (x.toInt * y.toInt) = x * y := by
  apply BitVec.eq_of_toInt_eq; simp [BitVec.toInt_ofInt, BitVec.toInt_mul]

theorem ofInt_neg_toInt (x : BitVec w) : BitVec.ofInt w (-x.toInt) = -x := by
  apply BitVec.eq_of_toInt_eq; simp [BitVec.toInt_ofInt, BitVec.toInt_neg]

theorem right_identity_zero_sub (x : LLVM.Int w) (c : BitVec w) (hc : c = 0) (n u : Bool) :
    x.sub (.val c) n u ⊒ x := by
  subst hc; cases x <;> combine_tac []

theorem right_identity_zero_add (x : LLVM.Int w) (c : BitVec w) (hc : c = 0) (n u : Bool) :
    x.add (.val c) n u ⊒ x := by
  subst hc; cases x <;> combine_tac []

theorem right_identity_zero_or (x : LLVM.Int w) (c : BitVec w) (hc : c = 0) (d : Bool) :
    x.or (.val c) d ⊒ x := by
  subst hc; cases x <;> combine_tac []

theorem right_identity_zero_xor (x : LLVM.Int w) (c : BitVec w) (hc : c = 0) :
    x.xor (.val c) ⊒ x := by
  subst hc; cases x <;> combine_tac []

theorem binop_right_to_zero (x : LLVM.Int w) (c : BitVec w) (hc : c = 0) (n u : Bool) :
    x.mul (.val c) n u ⊒ .val c := by
  subst hc; cases x <;> simp only [LLVM.Int.mul, Id.run, pure] <;>
    llvm_refines [BitVec.mul_zero, BitVec.zero_mul, BitVec.mul_one]

theorem binop_left_to_zero_mul (x : LLVM.Int w) (c : BitVec w) (hc : c = 0) (n u : Bool) :
    (LLVM.Int.val c).mul x n u ⊒ .val c := by
  subst hc; cases x <;> simp only [LLVM.Int.mul, Id.run, pure] <;>
    llvm_refines [BitVec.mul_zero, BitVec.zero_mul, BitVec.mul_one]

theorem right_identity_one_mul (x : LLVM.Int w) (c : BitVec w) (hc : c.toNat = 1) (n u : Bool) :
    x.mul (.val c) n u ⊒ x := by
  have : c = 1#w := by
    apply BitVec.eq_of_toNat_eq; rw [hc]
    have : 1 < 2 ^ w := by
      rcases Nat.lt_or_ge 1 (2 ^ w) with h | h
      · exact h
      · have := c.isLt; omega
    simp [Nat.mod_eq_of_lt this]
  subst this
  cases x <;> simp only [LLVM.Int.mul, Id.run, pure] <;>
    llvm_refines [BitVec.mul_zero, BitVec.zero_mul, BitVec.mul_one]

theorem sub_minus_one (x : LLVM.Int w) (c : BitVec w) (hc : c = -1) (n u : Bool) :
    (LLVM.Int.val c).sub x n u ⊒ x.xor (.val c) := by
  subst hc; cases x <;> combine_tac [BitVec.neg_one_eq_allOnes, BitVec.allOnes_sub_eq_not,
    BitVec.xor_allOnes]

theorem ZeroMinusAPlusB (a b : LLVM.Int w) (c : BitVec w) (hc : c = 0) (n₁ u₁ n₂ u₂ : Bool) :
    ((LLVM.Int.val c).sub a n₁ u₁).add b n₂ u₂ ⊒ b.sub a := by
  subst hc; cases a <;> cases b <;> combine_tac [BitVec.sub_eq_add_neg, BitVec.add_comm]

theorem APlusZeroMinusB (a b : LLVM.Int w) (c : BitVec w) (hc : c = 0) (n₁ u₁ n₂ u₂ : Bool) :
    a.add ((LLVM.Int.val c).sub b n₁ u₁) n₂ u₂ ⊒ a.sub b := by
  subst hc; cases a <;> cases b <;> combine_tac [BitVec.sub_eq_add_neg]

theorem AMinusZeroMinusB (a b : LLVM.Int w) (c : BitVec w) (hc : c = 0) (n₁ u₁ n₂ u₂ : Bool) :
    a.sub ((LLVM.Int.val c).sub b n₁ u₁) n₂ u₂ ⊒ a.add b := by
  subst hc; cases a <;> cases b <;> combine_tac [BitVec.sub_eq_add_neg]

theorem sub_one_from_sub (x y : LLVM.Int w) (c : BitVec w) (hc : c.toInt = 1) (n₁ u₁ n₂ u₂ : Bool) :
    (x.sub y n₁ u₁).sub (.val c) n₂ u₂ ⊒ (y.xor (.val (BitVec.ofInt w (-1)))).add x := by
  have : c = 1#w := by
    rw [← BitVec.ofInt_toInt (x := c), hc]; simp
  subst this
  have hsub (a b : BitVec w) : a - b - 1#w = ~~~b + a := by
    rw [BitVec.not_eq_neg_add]; simp only [BitVec.sub_eq_add_neg]; ac_rfl
  rw [ofInt_neg_one]
  cases x <;> cases y <;> combine_tac [BitVec.xor_allOnes, hsub]

theorem APlusC1MinusC2 (a : LLVM.Int w) (c₁ c₂ : BitVec w) (n₁ u₁ n₂ u₂ : Bool) :
    (a.add (.val c₁) n₁ u₁).sub (.val c₂) n₂ u₂ ⊒
      a.add (.val (BitVec.ofInt w (c₁.toInt - c₂.toInt))) := by
  rw [ofInt_toInt_sub]; cases a <;> combine_tac [BitVec.add_sub_assoc]

theorem C2MinusAPlusC1 (a : LLVM.Int w) (c₁ c₂ : BitVec w) (n₁ u₁ n₂ u₂ : Bool) :
    (LLVM.Int.val c₂).sub (a.add (.val c₁) n₁ u₁) n₂ u₂ ⊒
      (LLVM.Int.val (BitVec.ofInt w (c₂.toInt - c₁.toInt))).sub a := by
  rw [ofInt_toInt_sub]; cases a <;> combine_tac []
  all_goals bv_decide

theorem AMinusC1MinusC2 (a : LLVM.Int w) (c₁ c₂ : BitVec w) (n₁ u₁ n₂ u₂ : Bool) :
    (a.sub (.val c₁) n₁ u₁).sub (.val c₂) n₂ u₂ ⊒
      a.sub (.val (BitVec.ofInt w (c₁.toInt + c₂.toInt))) := by
  rw [ofInt_toInt_add]; cases a <;> combine_tac []
  all_goals bv_decide

theorem C1MinusAMinusC2 (a : LLVM.Int w) (c₁ c₂ : BitVec w) (n₁ u₁ n₂ u₂ : Bool) :
    ((LLVM.Int.val c₁).sub a n₁ u₁).sub (.val c₂) n₂ u₂ ⊒
      (LLVM.Int.val (BitVec.ofInt w (c₁.toInt - c₂.toInt))).sub a := by
  rw [ofInt_toInt_sub]; cases a <;> combine_tac []
  all_goals bv_decide

theorem AMinusC1PlusC2 (a : LLVM.Int w) (c₁ c₂ : BitVec w) (n₁ u₁ n₂ u₂ : Bool) :
    (a.sub (.val c₁) n₁ u₁).add (.val c₂) n₂ u₂ ⊒
      a.add (.val (BitVec.ofInt w (c₂.toInt - c₁.toInt))) := by
  rw [ofInt_toInt_sub]; cases a <;> combine_tac []
  all_goals bv_decide

theorem binop_left_to_zero_shl (c : BitVec w) (hc : c = 0) (s : LLVM.Int w) (n u : Bool) :
    (LLVM.Int.val c).shl s n u ⊒ .val c := by
  subst hc
  cases s <;> simp only [LLVM.Int.shl, Id.run, pure, BitVec.sshiftRight'] <;> llvm_refines [BitVec.zero_shiftLeft]

theorem binop_left_to_zero_lshr (c : BitVec w) (hc : c = 0) (s : LLVM.Int w) (e : Bool) :
    (LLVM.Int.val c).lshr s e ⊒ .val c := by
  subst hc
  cases s <;> simp only [LLVM.Int.lshr, Id.run, pure, BitVec.sshiftRight'] <;> llvm_refines [BitVec.zero_ushiftRight]

theorem binop_left_to_zero_ashr (c : BitVec w) (hc : c = 0) (s : LLVM.Int w) (e : Bool) :
    (LLVM.Int.val c).ashr s e ⊒ .val c := by
  subst hc
  cases s <;> simp only [LLVM.Int.ashr, Id.run, pure, BitVec.sshiftRight'] <;> llvm_refines [BitVec.zero_sshiftRight]

theorem sub_of_mul_const (a x : LLVM.Int w) (c : BitVec w) (n₁ u₁ n₂ u₂ : Bool) :
    a.sub (x.mul (.val c) n₁ u₁) n₂ u₂ ⊒ a.add (x.mul (.val (BitVec.ofInt w (-c.toInt)))) := by
  rw [ofInt_neg_toInt]
  cases a <;> cases x <;> simp only [LLVM.Int.mul, Id.run, pure] <;>
    combine_tac [BitVec.mul_neg, BitVec.sub_eq_add_neg]

theorem mul_by_neg_one (x : LLVM.Int w) (c : BitVec w) (hc : c = -1) (n u : Bool) :
    x.mul (.val c) n u ⊒ (LLVM.Int.val 0#w).sub x n := by
  subst hc
  cases x with
  | poison => simp [LLVM.Int.mul, Id.run, poison_isRefinedBy]
  | val x =>
    have hov : BitVec.smulOverflow x (-1#w) = BitVec.ssubOverflow 0#w x := by
      rcases Nat.eq_zero_or_pos w with rfl | hw
      · simp [BitVec.smulOverflow, BitVec.ssubOverflow, BitVec.toInt_of_zero_length]
      have hm : (-1#w).toInt = -1 := by
        rw [BitVec.neg_one_eq_allOnes, BitVec.toInt_allOnes]; simp [hw]
      simp only [BitVec.smulOverflow, BitVec.ssubOverflow, hm, BitVec.toInt_zero]
      congr 1 <;> simp <;> omega
    simp only [LLVM.Int.mul, LLVM.Int.sub, Id.run, pure, hov]
    llvm_refines [BitVec.mul_neg, BitVec.mul_one, BitVec.zero_sub]

theorem mulo_by_2 (x : LLVM.Int w) (c : BitVec w) (hc : c.toInt = 2) (n u : Bool) :
    x.mul (.val c) n u ⊒ x.add x n u := by
  have hn : c.toNat = 2 := by
    have := BitVec.toInt_eq_toNat_of_msb (x := c); grind [BitVec.toInt_eq_toNat_cond]
  cases x with
  | poison => simp [LLVM.Int.mul, Id.run, poison_isRefinedBy]
  | val x =>
    have hs : BitVec.smulOverflow x c = BitVec.saddOverflow x x := by
      simp only [BitVec.smulOverflow, BitVec.saddOverflow, hc]; congr 1 <;> simp <;> omega
    have hu : BitVec.umulOverflow x c = BitVec.uaddOverflow x x := by
      simp only [BitVec.umulOverflow, BitVec.uaddOverflow, hn]; congr 1; simp; omega
    have hv : x * c = x + x := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_mul, BitVec.toNat_add, hn, Nat.mul_two]
    simp only [LLVM.Int.mul, LLVM.Int.add, Id.run, hs, hu, hv]
    exact isRefinedBy_refl _

theorem add_shift (a b s : LLVM.Int w) (c : BitVec w) (hc : c = 0) (n₁ u₁ n₂ u₂ n₃ u₃ : Bool) :
    a.add (((LLVM.Int.val c).sub b n₁ u₁).shl s n₂ u₂) n₃ u₃ ⊒ a.sub (b.shl s) := by
  subst hc
  cases a <;> cases b <;> cases s <;>
    combine_tac [BitVec.zero_sub, BitVec.shiftLeft_neg, BitVec.sub_eq_add_neg]

theorem add_shift' (a b s : LLVM.Int w) (c : BitVec w) (hc : c = 0) (n₁ u₁ n₂ u₂ n₃ u₃ : Bool) :
    (((LLVM.Int.val c).sub b n₁ u₁).shl s n₂ u₂).add a n₃ u₃ ⊒ a.sub (b.shl s) := by
  subst hc
  cases a <;> cases b <;> cases s <;>
    combine_tac [BitVec.zero_sub, BitVec.shiftLeft_neg, BitVec.sub_eq_add_neg, BitVec.add_comm]

theorem NotAPlusNegOne (x : LLVM.Int w) (c₁ c₂ : BitVec w) (h₁ : c₁ = -1) (h₂ : c₂ = -1)
    (n u : Bool) :
    (x.add (.val c₁) n u).xor (.val c₂) ⊒ (LLVM.Int.val 0#w).sub x n u := by
  subst h₁ h₂
  cases x with
  | poison => simp [LLVM.Int.add, LLVM.Int.xor, Id.run, poison_isRefinedBy]
  | val x =>
    have hs : BitVec.saddOverflow x (-1#w) = BitVec.ssubOverflow 0#w x := by
      rcases Nat.eq_zero_or_pos w with rfl | hw
      · simp [BitVec.saddOverflow, BitVec.ssubOverflow, BitVec.toInt_of_zero_length]
      have hm : (-1#w).toInt = -1 := by
        rw [BitVec.neg_one_eq_allOnes, BitVec.toInt_allOnes]; simp [hw]
      have := BitVec.toInt_lt (x := x); have := BitVec.le_toInt (x := x)
      simp only [BitVec.saddOverflow, BitVec.ssubOverflow, hm, BitVec.toInt_zero]
      rw [Bool.eq_iff_iff]; simp; omega
    have hu : BitVec.uaddOverflow x (-1#w) = BitVec.usubOverflow 0#w x := by
      have hmn : (-1#w).toNat = 2 ^ w - 1 := by
        rw [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]
      have := Nat.one_le_two_pow (n := w)
      have := x.isLt
      simp only [BitVec.uaddOverflow, BitVec.usubOverflow, hmn, BitVec.toNat_zero]
      rw [Bool.eq_iff_iff]
      by_cases hx : 0 < x.toNat <;> simp [hx] <;> omega
    have hv : (x + -1#w) ^^^ -1#w = 0#w - x := by
      rw [BitVec.neg_one_eq_allOnes, BitVec.xor_allOnes, BitVec.not_eq_neg_add, BitVec.zero_sub,
        ← BitVec.neg_one_eq_allOnes]
      rw [_root_.BitVec.neg_add, _root_.BitVec.sub_neg, _root_.BitVec.add_sub_cancel]
    simp only [LLVM.Int.add, LLVM.Int.sub, LLVM.Int.xor, Id.run, pure, hs, hu]
    llvm_refines [hv]

theorem and_not_or_self (x y : BitVec w) : x &&& (y ^^^ BitVec.allOnes w) ||| y = x ||| y := by
  ext i hi; simp; cases x[i] <;> cases y[i] <;> rfl

theorem or_not_and_self (x y : BitVec w) : (x ||| (y ^^^ BitVec.allOnes w)) &&& y = x &&& y := by
  ext i hi; simp; cases x[i] <;> cases y[i] <;> rfl

theorem and_or_not_self (x y : BitVec w) :
    x &&& y ||| (y ^^^ BitVec.allOnes w) = x ||| (y ^^^ BitVec.allOnes w) := by
  ext i hi; simp; cases x[i] <;> cases y[i] <;> rfl

theorem or_and_not_self (x y : BitVec w) :
    (x ||| y) &&& (y ^^^ BitVec.allOnes w) = x &&& (y ^^^ BitVec.allOnes w) := by
  ext i hi; simp; cases x[i] <;> cases y[i] <;> rfl

theorem or_and_xor_to_or (x y : LLVM.Int w) (c : BitVec w) (hc : c = -1#w) (d : Bool) :
    (x.and (y.xor (.val c))).or y d ⊒ x.or y := by
  subst hc; simp only [BitVec.neg_one_eq_allOnes]
  cases x <;> cases y <;> combine_tac [and_not_or_self]

theorem or_and_xor_to_or' (x y : LLVM.Int w) (c : BitVec w) (hc : c = -1#w) (d : Bool) :
    (x.or (y.xor (.val c)) d).and y ⊒ x.and y := by
  subst hc; simp only [BitVec.neg_one_eq_allOnes]
  cases x <;> cases y <;> combine_tac [or_not_and_self]

theorem or_and_xor_to_xor_or (x y : LLVM.Int w) (c : BitVec w) (hc : c = -1#w) (d : Bool) :
    (x.and y).or (y.xor (.val c)) d ⊒ x.or (y.xor (.val c)) := by
  subst hc; simp only [BitVec.neg_one_eq_allOnes]
  cases x <;> cases y <;> combine_tac [and_or_not_self]

theorem or_and_xor_to_xor_or' (x y : LLVM.Int w) (c : BitVec w) (hc : c = -1#w) (d : Bool) :
    (x.or y d).and (y.xor (.val c)) ⊒ x.and (y.xor (.val c)) := by
  subst hc; simp only [BitVec.neg_one_eq_allOnes]
  cases x <;> cases y <;> combine_tac [or_and_not_self]

theorem simplify_neg_smax (a : LLVM.Int w) (c₁ c₂ : BitVec w) (h₁ : c₁ = 0) (h₂ : c₂ = 0)
    (n₁ u₁ n₂ u₂ : Bool) :
    (LLVM.Int.val c₁).sub (a.smax ((LLVM.Int.val c₂).sub a n₁ u₁)) n₂ u₂ ⊒
      a.smin ((LLVM.Int.val c₂).sub a n₁ u₁) := by
  subst h₁ h₂; cases a <;> combine_tac [BitVec.zero_sub, BitVec.neg_neg]

theorem simplify_neg_umax (a : LLVM.Int w) (c₁ c₂ : BitVec w) (h₁ : c₁ = 0) (h₂ : c₂ = 0)
    (n₁ u₁ n₂ u₂ : Bool) :
    (LLVM.Int.val c₁).sub (a.umax ((LLVM.Int.val c₂).sub a n₁ u₁)) n₂ u₂ ⊒
      a.umin ((LLVM.Int.val c₂).sub a n₁ u₁) := by
  subst h₁ h₂; cases a <;> combine_tac [BitVec.zero_sub, BitVec.neg_neg]

theorem simplify_neg_smin (a : LLVM.Int w) (c₁ c₂ : BitVec w) (h₁ : c₁ = 0) (h₂ : c₂ = 0)
    (n₁ u₁ n₂ u₂ : Bool) :
    (LLVM.Int.val c₁).sub (a.smin ((LLVM.Int.val c₂).sub a n₁ u₁)) n₂ u₂ ⊒
      a.smax ((LLVM.Int.val c₂).sub a n₁ u₁) := by
  subst h₁ h₂; cases a <;> combine_tac [BitVec.zero_sub, BitVec.neg_neg]

theorem simplify_neg_umin (a : LLVM.Int w) (c₁ c₂ : BitVec w) (h₁ : c₁ = 0) (h₂ : c₂ = 0)
    (n₁ u₁ n₂ u₂ : Bool) :
    (LLVM.Int.val c₁).sub (a.umin ((LLVM.Int.val c₂).sub a n₁ u₁)) n₂ u₂ ⊒
      a.umax ((LLVM.Int.val c₂).sub a n₁ u₁) := by
  subst h₁ h₂; cases a <;> combine_tac [BitVec.zero_sub, BitVec.neg_neg]

/-- The predicate of the negated comparison, as `not_cmp_fold_pattern` pairs them. -/
@[expose] def IntPred.inverse : IntPred → IntPred
  | .eq => .ne | .ne => .eq | .ugt => .ule | .uge => .ult | .ult => .uge | .ule => .ugt
  | .sgt => .sle | .sge => .slt | .slt => .sge | .sle => .sgt

theorem IntPred.eval_inverse {v : Nat} (p : IntPred) (a b : BitVec v) :
    p.inverse.eval a b = !p.eval a b := by
  cases p <;> simp [IntPred.inverse, IntPred.eval, BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle,
    BitVec.lt_def, BitVec.le_def]
  all_goals first
    | rfl
    | simp [bne]
    | (rw [Bool.eq_iff_iff]; simp only [Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]; omega)

theorem not_cmp_fold {v : Nat} (x y : LLVM.Int v) (p : IntPred) (c : BitVec 1) (hc : c.toNat = 1) :
    (x.icmp y p).xor (.val c) ⊒ x.icmp y p.inverse := by
  have : c = 1#1 := BitVec.eq_of_toNat_eq (by simp [hc])
  subst this
  cases x <;> cases y <;> simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run, poison_isRefinedBy,
    IntPred.eval_inverse]
  rename_i a b
  cases p.eval a b <;> exact isRefinedBy_refl _

theorem not_cmp_fold_zext {v W : Nat} (x y : LLVM.Int v) (p : IntPred) (h : 1 < W) (c : BitVec W)
    (hc : c.toNat = 1) :
    ((x.icmp y p).zext W false h).xor (.val c) ⊒ (x.icmp y p.inverse).zext W false h := by
  have : c = 1#W := BitVec.eq_of_toNat_eq (by
    simp [hc, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h (Nat.le_of_lt Nat.lt_two_pow_self))])
  subst this
  cases x <;> cases y <;> simp [LLVM.Int.icmp, LLVM.Int.xor, LLVM.Int.zext, Id.run,
    poison_isRefinedBy, IntPred.eval_inverse]
  rename_i a b
  cases p.eval a b <;>
    simp [BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide : 0 < 1), isRefinedBy_refl]

theorem or_beq_zero {v : Nat} (a b : BitVec v) : (a ||| b == 0#v) = (a == 0#v && b == 0#v) := by
  rw [Bool.eq_iff_iff]; simp [BitVec.or_eq_zero_iff]

theorem or_bne_zero {v : Nat} (a b : BitVec v) : (a ||| b != 0#v) = (a != 0#v || b != 0#v) := by
  rw [Bool.eq_iff_iff]; simp [BitVec.or_eq_zero_iff]; by_cases a = 0#v <;> simp_all

theorem double_icmp_zero_and {v : Nat} (x y : LLVM.Int v) (c₁ c₂ : BitVec v) (h₁ : c₁ = 0)
    (h₂ : c₂ = 0) :
    (x.icmp (.val c₁) .eq).and (y.icmp (.val c₂) .eq) ⊒ (x.or y).icmp (.val c₁) .eq := by
  subst h₁ h₂
  cases x <;> cases y <;> simp [LLVM.Int.icmp, LLVM.Int.and, LLVM.Int.or, IntPred.eval, Id.run,
    poison_isRefinedBy]
  rename_i a b
  rw [or_beq_zero]; exact isRefinedBy_refl _

theorem double_icmp_zero_or {v : Nat} (x y : LLVM.Int v) (c₁ c₂ : BitVec v) (h₁ : c₁ = 0)
    (h₂ : c₂ = 0) (d : Bool) :
    (x.icmp (.val c₁) .ne).or (y.icmp (.val c₂) .ne) d ⊒ (x.or y).icmp (.val c₁) .ne := by
  subst h₁ h₂
  cases x <;> cases y <;> simp [LLVM.Int.icmp, LLVM.Int.or, IntPred.eval, Id.run, poison_isRefinedBy]
  rename_i a b
  rw [or_bne_zero]
  generalize (a != 0#v) = p; generalize (b != 0#v) = q
  cases p <;> cases q <;> simp [BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide : 0 < 1),
    isRefinedBy_refl, poison_isRefinedBy] <;> (try split) <;> (try simp_all [isRefinedBy_refl, poison_isRefinedBy, pure])

theorem double_icmp_zero_and_zext {v W : Nat} (h : 1 < W) (x y : LLVM.Int v) (c₁ c₂ : BitVec v)
    (h₁ : c₁ = 0) (h₂ : c₂ = 0) :
    ((x.icmp (.val c₁) .eq).zext W false h).and ((y.icmp (.val c₂) .eq).zext W false h) ⊒
      ((x.or y).icmp (.val c₁) .eq).zext W false h := by
  subst h₁ h₂
  cases x <;> cases y <;> simp [LLVM.Int.icmp, LLVM.Int.and, LLVM.Int.or, LLVM.Int.zext,
    IntPred.eval, Id.run, poison_isRefinedBy]
  rename_i a b
  rw [or_beq_zero]
  generalize (a == 0#v) = p; generalize (b == 0#v) = q
  cases p <;> cases q <;> simp [BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide : 0 < 1),
    isRefinedBy_refl, poison_isRefinedBy] <;> (try split) <;> (try simp_all [isRefinedBy_refl, poison_isRefinedBy, pure])

theorem double_icmp_zero_or_zext {v W : Nat} (h : 1 < W) (x y : LLVM.Int v) (c₁ c₂ : BitVec v)
    (h₁ : c₁ = 0) (h₂ : c₂ = 0) (d : Bool) :
    ((x.icmp (.val c₁) .ne).zext W false h).or ((y.icmp (.val c₂) .ne).zext W false h) d ⊒
      ((x.or y).icmp (.val c₁) .ne).zext W false h := by
  subst h₁ h₂
  cases x <;> cases y <;> simp [LLVM.Int.icmp, LLVM.Int.or, LLVM.Int.zext, IntPred.eval, Id.run,
    poison_isRefinedBy]
  rename_i a b
  rw [or_bne_zero]
  generalize (a != 0#v) = p; generalize (b != 0#v) = q
  cases p <;> cases q <;> simp [BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide : 0 < 1),
    isRefinedBy_refl, poison_isRefinedBy] <;> (try split) <;> (try simp_all [isRefinedBy_refl, poison_isRefinedBy, pure])

theorem constant_fold_add (c₁ c₂ : BitVec w) (n u : Bool) :
    (LLVM.Int.val c₁).add (.val c₂) n u ⊒ .val (BitVec.ofInt w (c₁.toInt + c₂.toInt)) := by
  rw [ofInt_toInt_add]; combine_tac []

theorem constant_fold_sub (c₁ c₂ : BitVec w) (n u : Bool) :
    (LLVM.Int.val c₁).sub (.val c₂) n u ⊒ .val (BitVec.ofInt w (c₁.toInt - c₂.toInt)) := by
  rw [ofInt_toInt_sub]; combine_tac []

theorem constant_fold_mul (c₁ c₂ : BitVec w) (n u : Bool) :
    (LLVM.Int.val c₁).mul (.val c₂) n u ⊒ .val (BitVec.ofInt w (c₁.toInt * c₂.toInt)) := by
  rw [ofInt_toInt_mul]; simp only [LLVM.Int.mul, Id.run, pure]; llvm_refines []

theorem constant_fold_smin (c₁ c₂ : BitVec w) :
    (LLVM.Int.val c₁).smin (.val c₂) ⊒ .val (BitVec.ofInt w (min c₁.toInt c₂.toInt)) := by
  simp only [LLVM.Int.smin, Id.run, BitVec.sle, Int.min_def]
  split <;> split <;> simp_all [BitVec.ofInt_toInt, isRefinedBy_refl] <;> omega

theorem constant_fold_smax (c₁ c₂ : BitVec w) :
    (LLVM.Int.val c₁).smax (.val c₂) ⊒ .val (BitVec.ofInt w (max c₁.toInt c₂.toInt)) := by
  simp only [LLVM.Int.smax, Id.run, BitVec.sle, Int.max_def]
  split <;> split <;> simp_all [BitVec.ofInt_toInt, isRefinedBy_refl] <;> omega

theorem select_constant_cmp_nonzero {wc : Nat} (c : BitVec wc) (hc : ¬ c = 0#wc) (x y : LLVM.Int w) :
    GMIR.selectNonzero (.val c) x y ⊒ x := by
  simp [GMIR.selectNonzero, Id.run, hc, isRefinedBy_refl]

theorem select_constant_cmp_zero {wc : Nat} (c : BitVec wc) (hc : c = 0#wc) (x y : LLVM.Int w) :
    GMIR.selectNonzero (.val c) x y ⊒ y := by
  simp [GMIR.selectNonzero, Id.run, hc, isRefinedBy_refl]

theorem sub_to_add (a : LLVM.Int w) (c : BitVec w) (n u : Bool) :
    a.sub (.val c) n u ⊒
      a.add (.val (BitVec.ofInt w (-c.toInt))) (n && !decide (c = BitVec.intMin w)) := by
  rw [ofInt_neg_toInt]
  cases a with
  | poison => simp [LLVM.Int.sub, Id.run, poison_isRefinedBy]
  | val a =>
    by_cases hmin : c = BitVec.intMin w
    · simp only [hmin, decide_true, Bool.not_true, Bool.and_false]
      simp only [LLVM.Int.sub, LLVM.Int.add, Id.run, pure]
      llvm_refines [BitVec.sub_eq_add_neg]
    · have hs : BitVec.saddOverflow a (-c) = BitVec.ssubOverflow a c := by
        simp only [BitVec.saddOverflow, BitVec.ssubOverflow, BitVec.toInt_neg_of_ne_intMin hmin]
        congr 1 <;> simp <;> omega
      simp only [hmin, decide_false, Bool.not_false, Bool.and_true]
      simp only [LLVM.Int.sub, LLVM.Int.add, Id.run, pure, hs]
      llvm_refines [BitVec.sub_eq_add_neg]

/-- `redundant_and_select_pattern`, whose mask `k` is odd as an integer, at every width. -/
theorem and_select_bool_odd {wc : Nat} (c : LLVM.Int wc) (t f : LLVM.Int w) (k : _root_.Int)
    (hk : k % 2 = 1)
    (ht : t = .poison ∨ t = .val 0#w ∨ t = .val 1#w)
    (hf : f = .poison ∨ f = .val 0#w ∨ f = .val 1#w) :
    LLVM.Int.and (GMIR.selectNonzero c t f) (.val (BitVec.ofInt w k)) ⊒ GMIR.selectNonzero c t f := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · generalize GMIR.selectNonzero c t f = r
    cases r <;> simp [LLVM.Int.and, Id.run, poison_isRefinedBy, isRefinedBy_refl,
      BitVec.of_length_zero]
  · rw [and_select_bool c t f _ _ ht hf]
    · exact isRefinedBy_refl _
    · have hd : (2 : _root_.Int) ∣ ((2 ^ w : Nat) : _root_.Int) := by
        refine ⟨((2 ^ (w - 1) : Nat) : _root_.Int), ?_⟩
        rw [show w = (w - 1) + 1 by omega, Nat.pow_succ]
        push_cast
        rw [_root_.Int.mul_comm]
      have h0 : 0 ≤ k % ((2 ^ w : Nat) : _root_.Int) :=
        _root_.Int.emod_nonneg _ (by have := Nat.two_pow_pos w; omega)
      have h1 : (k % ((2 ^ w : Nat) : _root_.Int)) % 2 = 1 := by
        rw [_root_.Int.emod_emod_of_dvd _ hd]; exact hk
      simp only [BitVec.toNat_ofInt]
      omega

/-- An `i1` comparison arm of `redundant_and_select_pattern` is poison, zero or one. -/
theorem icmp_eq_poison_or_zero_or_one {v : Nat} (x y : LLVM.Int v) (p : IntPred) :
    x.icmp y p = .poison ∨ x.icmp y p = .val 0#1 ∨ x.icmp y p = .val 1#1 := by
  cases x <;> cases y <;> simp [LLVM.Int.icmp, Id.run]
  rename_i a b
  cases p.eval a b <;> simp

/-- A constant arm of `redundant_and_select_pattern` is zero or one. -/
theorem boolArm_of_constant (c : BitVec w) (h : c = 0 ∨ c = 1) :
    LLVM.Int.val c = .poison ∨ LLVM.Int.val c = .val 0#w ∨ LLVM.Int.val c = .val 1#w := by
  rcases h with rfl | rfl <;> simp

/-- Prove the correctness of `mul_to_shl_pattern`: `x * 2^k` → `x << k`, whose flags carry over. A
multiplication that does not overflow makes the shift's no-wrap checks pass. -/
theorem mul_twoPow_shl (x : LLVM.Int w) (k : Nat) (hk : k + 1 < w) (n u : Bool) :
    x.mul (.val (BitVec.twoPow w k)) n u ⊒ x.shl (LLVM.Int.constant w k) n u := by
  have hkw : k < 2 ^ w := Nat.lt_trans (by omega) Nat.lt_two_pow_self
  have hlt : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
  have hkn : (BitVec.ofInt w (k : _root_.Int)).toNat = k := by
    rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkw]
  have hrange : ¬ (w : BitVec w) ≤ BitVec.ofInt w (k : _root_.Int) :=
    BitVec.not_le.mpr (BitVec.lt_ofInt_natCast_ofNat_of_lt (by omega))
  have hti : (BitVec.twoPow w k).toInt = 2 ^ k := by
    rw [BitVec.toInt_twoPow]
    simp only [show ¬ w ≤ k by omega, show ¬ k + 1 = w by omega, ite_false]
  cases x with
  | poison => simp [LLVM.Int.mul, Id.run, poison_isRefinedBy]
  | val x =>
    have hv : x <<< BitVec.ofInt w (k : _root_.Int) = x * BitVec.twoPow w k := by
      rw [BitVec.shiftLeft_eq', hkn, BitVec.shiftLeft_eq_mul_twoPow]
    have hnuw (h : ¬ BitVec.umulOverflow x (BitVec.twoPow w k) = true) :
        x <<< BitVec.ofInt w (k : _root_.Int) >>> BitVec.ofInt w (k : _root_.Int) = x := by
      simp only [BitVec.umulOverflow, BitVec.toNat_twoPow_of_lt (by omega : k < w),
        decide_eq_true_eq, ge_iff_le, Nat.not_le] at h
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.ushiftRight_eq', hkn, hv, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
        BitVec.toNat_twoPow_of_lt (by omega), Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow,
        Nat.mul_div_cancel _ (Nat.two_pow_pos k)]
    have hnsw (h : ¬ BitVec.smulOverflow x (BitVec.twoPow w k) = true) :
        (x <<< BitVec.ofInt w (k : _root_.Int)).sshiftRight' (BitVec.ofInt w (k : _root_.Int)) = x := by
      simp only [BitVec.smulOverflow, hti, Bool.or_eq_true, decide_eq_true_eq, not_or,
        ge_iff_le, _root_.Int.not_le, _root_.Int.not_lt] at h
      apply BitVec.eq_of_toInt_eq
      rw [BitVec.sshiftRight_eq', hkn, hv, BitVec.toInt_sshiftRight, BitVec.toInt_mul, hti,
        bmod_two_pow_of_range (by omega) h.2 h.1, _root_.Int.shiftRight_eq_div_pow]
      have hpos : (0 : _root_.Int) < 2 ^ k := by exact_mod_cast Nat.two_pow_pos k
      push_cast
      exact _root_.Int.mul_ediv_cancel _ (_root_.Int.ne_of_gt hpos)
    simp only [LLVM.Int.mul, LLVM.Int.shl, LLVM.Int.constant, Id.run, pure, ge_iff_le, hrange,
      ite_false]
    by_cases hs : n = true ∧ BitVec.smulOverflow x (BitVec.twoPow w k) = true
    · simp [hs, poison_isRefinedBy]
    by_cases hu : u = true ∧ BitVec.umulOverflow x (BitVec.twoPow w k) = true
    · simp [hu, poison_isRefinedBy]
    have hs' : ¬ (n = true ∧ (x <<< BitVec.ofInt w (k : _root_.Int)).sshiftRight'
        (BitVec.ofInt w (k : _root_.Int)) ≠ x) := by
      rintro ⟨hn, hne⟩; exact hne (hnsw fun h => hs ⟨hn, h⟩)
    have hu' : ¬ (u = true ∧ x <<< BitVec.ofInt w (k : _root_.Int) >>>
        BitVec.ofInt w (k : _root_.Int) ≠ x) := by
      rintro ⟨hn, hne⟩; exact hne (hnuw fun h => hu ⟨hn, h⟩)
    simp only [hs, hu, hs', hu', ite_false]
    rw [hv]
    exact isRefinedBy_refl _

end Combines

end Veir.Data.LLVM

end
