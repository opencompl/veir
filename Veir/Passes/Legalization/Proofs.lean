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

private theorem notI1_poison : notI1 .poison = .poison := by
  simp [notI1, LLVM.Int.xor, Id.run]

private theorem notI1_one : notI1 (.val 1#1) = .val 0#1 := by
  simp [notI1, LLVM.Int.xor, LLVM.Int.constant, Id.run]

private theorem notI1_zero : notI1 (.val 0#1) = .val 1#1 := by
  simp [notI1, LLVM.Int.xor, LLVM.Int.constant, Id.run]

private theorem setWidth_one {w : Nat} : BitVec.setWidth w 1#1 = 1#w := by
  apply BitVec.eq_of_toNat_eq
  simp

private theorem ofInt_neg_one {w : Nat} : BitVec.ofInt w (-1) = BitVec.allOnes w := by
  rw [BitVec.ofInt_neg, ← BitVec.neg_one_eq_allOnes]
  simp

private theorem signExtend_one {w : Nat} : BitVec.signExtend w 1#1 = BitVec.allOnes w := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [BitVec.getElem_signExtend, BitVec.msb]

private theorem signExtend_zero {w : Nat} : BitVec.signExtend w 0#1 = 0#w := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [BitVec.getElem_signExtend, BitVec.msb]

private theorem mod_two_pow_of_lt {k w : Nat} (hk : k < w) : k % 2 ^ w = k :=
  Nat.mod_eq_of_lt (Nat.lt_trans hk Nat.lt_two_pow_self)

/-- Closes one case of a `tryFoldSelectOfConstants` proof, where the condition is known. -/
local macro "select_const_tac" : tactic =>
  `(tactic| (simp_all [notI1_poison, notI1_one, notI1_zero, setWidth_one, signExtend_one,
      signExtend_zero, ofInt_neg_one, mod_two_pow_of_lt, BitVec.twoPow_eq,
      BitVec.add_comm, BitVec.sub_eq_add_neg, BitVec.neg_one_eq_allOnes,
      LLVM.Int.zext, LLVM.Int.sext, LLVM.Int.add, LLVM.Int.shl, LLVM.Int.or, LLVM.Int.constant,
      Id.run, isRefinedBy]))

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
  apply selectNonzero_refines <;> rintro rfl <;> select_const_tac <;>
    simp [show ¬ w ≤ k by omega]

/-- Prove the correctness of combining `c ? 0 : 2^k` to `shl (zext (not c)), k`. -/
theorem select_zero_pow2 {w : Nat} (h : 1 < w) (c : LLVM.Int 1) (k : Nat) (hk : k < w) :
    GMIR.selectNonzero c (LLVM.Int.constant w 0) (LLVM.Int.val (BitVec.twoPow w k)) ⊒
      LLVM.Int.shl (LLVM.Int.zext (notI1 c) w false h) (LLVM.Int.constant w k) := by
  apply selectNonzero_refines <;> rintro rfl <;> select_const_tac <;>
    simp [show ¬ w ≤ k by omega]

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

/-! ### Word operations -/

/-- `x` is its low bits after any extension. -/
private theorem trunc_ext {n m : Nat} (h : n < m) (x : LLVM.Int n) (ext : BitVec (m - n)) :
    LLVM.Int.trunc (LLVM.Int.ext x m ext h) n false false h = x := by
  cases x <;> simp [LLVM.Int.ext, LLVM.Int.trunc, LLVM.Int.cast, Id.run,
    BitVec.eq_of_getElem_eq_iff]
  grind

/-- `x` is its low bits after a sign extension. -/
private theorem trunc_sext {n m : Nat} (h : n < m) (x : LLVM.Int n) :
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

end Veir.Data.LLVM

end
