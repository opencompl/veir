module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Casting
public import Veir.Dialects.GMIR.Semantics
public import Veir.Dialects.GMIR_RISCV.Semantics
meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect
meta import Veir.Meta.Tactic.PBVDecide
public meta import Veir.PatternRewriter.Puddle.CTreeProofs
import Veir.ForLean
import all Veir.Data.LLVM.Int.Basic
import all Veir.Dialects.GMIR.Semantics
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR_RISCV.Semantics
public import Veir.IR.Simp
public import Veir.IR.Attribute
import all Veir.PatternRewriter.Puddle.CTreeProofs
import all Veir.Passes.Legalization.LegalizerHelper
import all Veir.Passes.Legalization.LegalizationArtifactCombiner
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
import all Veir.Passes.Legalization.CombinerHelper
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.GMIR_RISCV.OpInfo
import all Veir.GlobalOpInfo
import all Veir.Interpreter.Basic
import all Veir.Interpreter.CTreeInterpreter
import all Veir.IR.Attribute
import Veir.PatternRewriter.Puddle.Definitions
import Veir.PatternRewriter.Puddle.Validity
import Veir.PatternRewriter.Puddle.CTreeValidityTactics
import all Veir.Data.LLVM.Int.Bitblast
import all Init.Data.Array.Basic
import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.ProofKind
import all Veir.Dialects.GMIR.Properties
import all Init.Data.Nat.Power2.Basic
import all Veir.Passes.Legalization.Validity.Common
import all Veir.Passes.Legalization.Validity.PBVNormalize

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

/-- `combineZExtOfTruncOfICmp`: a `g_zext` of a `g_trunc` of a `g_icmp` keeps its bit, whatever the
flags of the casts, when the truncation keeps at least that bit (`0 < n`). -/
theorem zext_trunc_zext_bit {n W : Nat} (hn : 0 < n) (hnW : n < W) (h1 : 1 < W) (c : LLVM.Int 1)
    (nsw nuw nneg : Bool) :
    LLVM.Int.zext (LLVM.Int.trunc (LLVM.Int.zext c W false h1) n nsw nuw hnW) W nneg hnW ⊒
      LLVM.Int.zext c W false h1 := by
  cases c with
  | poison => simp [LLVM.Int.zext, LLVM.Int.trunc, Id.run]
  | val c =>
    have hc : c.toNat < 2 ^ n := Nat.lt_of_lt_of_le c.isLt (Nat.pow_le_pow_right (by decide) hn)
    have hcW : c.toNat < 2 ^ W := Nat.lt_of_lt_of_le c.isLt (Nat.pow_le_pow_right (by decide) (by omega))
    have hval : (c.setWidth n).setWidth W = c.setWidth W := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hcW, Nat.mod_eq_of_lt hc]
    have hval' : ((c.setWidth W).setWidth n).setWidth W = c.setWidth W := by
      rw [BitVec.setWidth_setWidth_of_le _ (Nat.le_of_lt hnW), hval]
    simp [LLVM.Int.zext, LLVM.Int.trunc, Id.run]
    by_cases hA : nsw = true ∧
        ¬BitVec.signExtend W (BitVec.setWidth n (BitVec.setWidth W c)) = BitVec.setWidth W c
    · simp [hA]
    by_cases hB : nuw = true ∧
        ¬BitVec.setWidth W (BitVec.setWidth n (BitVec.setWidth W c)) = BitVec.setWidth W c
    · simp [hA, hB]
    simp [hA, hB]
    split <;> simp_all [pure]

/--
Prove the correctness of widening `g_poison`: truncating a wide poison, whatever the `nsw` and
`nuw` flags, refines the narrow poison.
-/
theorem poison_widening {w n : Nat} (h : n < w) (nsw nuw : Bool) :
    (LLVM.Int.poison : LLVM.Int n) ⊒ LLVM.Int.trunc (LLVM.Int.poison : LLVM.Int w) n nsw nuw h :=
  LLVM.Int.poison_isRefinedBy _

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

/-- Bit `i` of the mask `2 ^ n - 1`, as `veir_bv_normalize` writes it, is set exactly when
`i < n`. -/
private theorem getElem_twoPow_sub_one {m n i : Nat} (hi : i < m) :
    (BitVec.twoPow m n - 1#m)[i] = decide (i < n) := by
  rw [← BitVec.ofInt_two_pow_sub_one]
  exact getElem_ofInt_two_pow_sub_one hi

/--
Prove the correctness of lowering `g_zext` to a `g_and` of a `g_anyext` with the mask of the source
width, at every width.
-/
theorem zext_and_anyext (n m : Nat) (h : n < m) (x : LLVM.Int n) (nneg : Bool)
    (ext : BitVec (m - n)) :
    LLVM.Int.zext x m nneg h ⊒
      LLVM.Int.and (LLVM.Int.ext x m ext h) (LLVM.Int.constant m (2 ^ n - 1)) := by
  veir_bv_normalize
  simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_append]
  grind

/--
Prove `combineSExtOfTrunc false` at every width: `g_sext (g_trunc x)` is refined by the
`g_sext_inreg` of `x`, whatever the flags of the `g_trunc`. The `g_sext_inreg` size `k` is the width
`n` of the `g_trunc` as the combine computes it, through a 64-bit size.
-/
theorem sext_trunc_sext_inreg {w n k : Nat} (hk : k = n) (h : n < w) (h' : k < w) (x : LLVM.Int w)
    (nsw nuw : Bool) :
    LLVM.Int.sext (LLVM.Int.trunc x n nsw nuw h) w h ⊒
      LLVM.Int.sext (LLVM.Int.trunc x k false false h') w h' := by
  subst hk
  veir_bv_normalize
  simp

/--
Prove `combineZExtOfTrunc false` at every width: `g_zext (g_trunc x)` is refined by the `g_and` of
`x` with the mask of the truncated width, whatever the flags of the `g_trunc` and the `g_zext`.
-/
theorem zext_trunc_and {w n : Nat} (h : n < w) (x : LLVM.Int w) (nsw nuw nneg : Bool) :
    LLVM.Int.zext (LLVM.Int.trunc x n nsw nuw h) w nneg h ⊒
      LLVM.Int.and x (LLVM.Int.constant w (2 ^ n - 1)) :=
  have ⟨ext, hext⟩ := anyext_trunc_same w n h x nsw nuw
  LLVM.Int.isRefinedBy_trans (zext_and_anyext n w h _ nneg ext)
    (LLVM.Int.and_mono _ _ _ _ hext (LLVM.Int.isRefinedBy_refl _))

/--
Prove `combineSExtOfTrunc true` at every width: when `x` is wider than the `g_sext`, it is truncated
to its type first. As in `sext_trunc_sext_inreg`, `k` is the `g_sext_inreg` size.
-/
theorem sext_trunc_sext_inreg_of_trunc {w m n k : Nat} (hk : k = n) (hn : n < m) (hk' : k < m)
    (hm : m < w) (x : LLVM.Int w) (nsw nuw : Bool) :
    LLVM.Int.sext (LLVM.Int.trunc x n nsw nuw (by omega)) m hn ⊒
      LLVM.Int.sext (LLVM.Int.trunc (LLVM.Int.trunc x m false false hm) k false false hk') m hk' := by
  subst hk
  veir_bv_normalize
  simp [BitVec.setWidth_setWidth_of_le _ (Nat.le_of_lt hn)]

/--
Prove `combineZExtOfTrunc true` at every width: when `x` is wider than the `g_zext`, it is truncated
to its type first.
-/
theorem zext_trunc_and_of_trunc {w m n : Nat} (hn : n < m) (hm : m < w) (x : LLVM.Int w)
    (nsw nuw nneg : Bool) :
    LLVM.Int.zext (LLVM.Int.trunc x n nsw nuw (by omega)) m nneg hn ⊒
      LLVM.Int.and (LLVM.Int.trunc x m false false hm) (LLVM.Int.constant m (2 ^ n - 1)) :=
  have ⟨ext, hext⟩ := anyext_trunc_narrower w n m hn hm x nsw nuw
  LLVM.Int.isRefinedBy_trans (zext_and_anyext n m hn _ nneg ext)
    (LLVM.Int.and_mono _ _ _ _ hext (LLVM.Int.isRefinedBy_refl _))

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
Prove the correctness of widening `g_freeze` with `g_anyext`, at every width up to 64 and whatever
the high bits: the frozen low bits are the frozen value.
-/
theorem freeze_widening {n m : Nat} (h : n < m) (hm : m ≤ 64) (x : LLVM.Int n)
    (ext : BitVec (m - n)) :
    LLVM.Int.freeze x ⊒
      LLVM.Int.trunc (LLVM.Int.freeze (LLVM.Int.ext x m ext h)) n false false h := by
  veir_bv_normalize
  pbv_decide 64

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
  | poison => simp [GMIR.selectNonzero, LLVM.Int.trunc, Id.run, LLVM.Int.isRefinedBy]
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
  | poison => simp [GMIR.selectNonzero, LLVM.Int.zext, Id.run, LLVM.Int.isRefinedBy]
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

/-! ### Word operations -/

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
  refine LLVM.Int.isRefinedBy_trans (add_isRefinedBy_add x y nsw nuw) ?_
  cases x <;> cases y
  case val.val x y =>
    simp [LLVM.Int.add, LLVM.Int.uaddOverflowFlag, unmergeValues, uaddWithCarry, mergeValues,
      Id.run, BitVec.add_eq_append]
  -- A poison operand makes both sides poison.
  all_goals exact LLVM.Int.poison_isRefinedBy _

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
  refine LLVM.Int.isRefinedBy_trans (sub_isRefinedBy_sub x y nsw nuw) ?_
  cases x <;> cases y
  case val.val x y =>
    simp [LLVM.Int.sub, LLVM.Int.usubOverflowFlag, unmergeValues, usubWithBorrow, mergeValues,
      Id.run, BitVec.sub_eq_append]
  -- A poison operand makes both sides poison.
  all_goals exact LLVM.Int.poison_isRefinedBy _

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
  exact Data.LLVM.Int.isRefinedBy_refl _

theorem or_widening (h : w < W) (x y : LLVM.Int w) (m m' : BitVec (W - w)) (disjoint : Bool) :
    LLVM.Int.or x y disjoint ⊒
      LLVM.Int.trunc (LLVM.Int.or (LLVM.Int.ext x W m h) (LLVM.Int.ext y W m' h)) w false false h := by
  rw [trunc_or, trunc_ext, trunc_ext]
  grind

theorem xor_widening (h : w < W) (x y : LLVM.Int w) (m m' : BitVec (W - w)) :
    LLVM.Int.xor x y ⊒
      LLVM.Int.trunc (LLVM.Int.xor (LLVM.Int.ext x W m h) (LLVM.Int.ext y W m' h)) w false false h := by
  rw [trunc_xor, trunc_ext, trunc_ext]
  exact Data.LLVM.Int.isRefinedBy_refl _

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
    exact Data.LLVM.Int.isRefinedBy_refl _
  · have hS : x.toNat + y.toNat < 2 ^ W := by omega
    have hm := Nat.mod_lt (x.toNat + y.toNat) (Nat.two_pow_pos w)
    simp only [Data.LLVM.Int.isRefinedBy_eq, BitVec.ofBool_eq_iff_eq, bne_eq_decide_toNat, BitVec.uaddOverflow,
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
    exact Data.LLVM.Int.isRefinedBy_refl _
  · have hm := Nat.mod_lt ((2 ^ W - y.toNat + x.toNat) % 2 ^ W) (Nat.two_pow_pos w)
    simp only [Data.LLVM.Int.isRefinedBy_eq, BitVec.ofBool_eq_iff_eq, bne_eq_decide_toNat, BitVec.usubOverflow,
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
    exact Data.LLVM.Int.isRefinedBy_refl _
  · simp only [Data.LLVM.Int.isRefinedBy_eq, BitVec.ofBool_eq_iff_eq, bne_eq_decide_toInt]
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
    exact Data.LLVM.Int.isRefinedBy_refl _
  · simp only [Data.LLVM.Int.isRefinedBy_eq, BitVec.ofBool_eq_iff_eq, bne_eq_decide_toInt]
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
    Id.run, pure, IntPred.eval, Data.LLVM.Int.isRefinedBy_eq, BitVec.ofBool_xor_ofBool, BitVec.ofBool_eq_iff_eq,
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
    Id.run, pure, IntPred.eval, Data.LLVM.Int.isRefinedBy_eq, BitVec.ofBool_xor_ofBool, BitVec.ofBool_eq_iff_eq,
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
  exact Data.LLVM.Int.isRefinedBy_refl _

/-- The overflow flag of `lowerUAddSubO false`: the difference borrows exactly when `a <u b`. -/
theorem usubo_flag_lowering (x y : LLVM.Int w) :
    LLVM.Int.usubOverflowFlag x y ⊒ LLVM.Int.icmp x y .ult := by
  have := congrArg Prod.snd (usubo_lowering x y)
  simp only at this
  rw [this]
  exact Data.LLVM.Int.isRefinedBy_refl _

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

/-- A zero extension truncated to an intermediate width is the zero extension to that width. -/
theorem trunc_zext_of_lt {n w W : Nat} (hn : n < w) (hw : w < W) (c : LLVM.Int n) :
    LLVM.Int.trunc (LLVM.Int.zext c W false (by omega)) w false false hw = LLVM.Int.zext c w false hn := by
  cases c <;> simp [LLVM.Int.zext, LLVM.Int.trunc, Id.run, BitVec.setWidth_setWidth_of_le _ (Nat.le_of_lt hw)]

/-- `widenTypeGroup .g_icmp (.type 0) .g_anyext` at an `i1` result, which the interpreter yields
as is: the wide `g_icmp` zero-extends it, and the truncation reads it back. -/
theorem icmp_result_widening_one {w W : Nat} (hw : w ≤ 1) (hw0 : 0 < w) (hW : 1 < W) (hwW : w < W)
    (c : LLVM.Int 1) :
    ∃ h : 1 = w, LLVM.Int.cast c h ⊒ LLVM.Int.trunc (LLVM.Int.zext c W false hW) w false false hwW := by
  obtain rfl : w = 1 := by omega
  exact ⟨rfl, by rw [LLVM.Int.cast_self, trunc_zext hW]; exact Data.LLVM.Int.isRefinedBy_refl _⟩

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

/-- Lowering `g_uaddsat` with `g_umin`: `uadd.sat a b = a + umin (~a) b`. -/
theorem uaddSat_minmax (x y : LLVM.Int w) :
    x.uaddSat y ⊒ x.add ((x.xor (.val (BitVec.ofInt w (-1)))).umin y) := by
  cases x <;> cases y <;>
    simp [Int.uaddSat, Int.add, Int.xor, Int.umin, Id.run, Data.LLVM.Int.isRefinedBy_eq, pure, ofInt_neg_one,
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
  cases x <;> cases y <;> simp [Int.usubSat, Int.sub, Int.umin, Id.run, Data.LLVM.Int.isRefinedBy_eq, pure]
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
  cases x <;> cases y <;> simp [Int.saddSat, Int.add, Int.sub, Int.smin, Int.smax, Id.run, Data.LLVM.Int.isRefinedBy_eq,
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
  cases x <;> cases y <;> simp [Int.ssubSat, Int.sub, Int.smin, Int.smax, Id.run, Data.LLVM.Int.isRefinedBy_eq, pure]
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
    simp [Int.uaddSat, Int.add, Int.uaddOverflowFlag, GMIR.selectNonzero, Id.run, Data.LLVM.Int.isRefinedBy_eq, pure,
      ofInt_neg_one]
  rename_i x y
  by_cases h1 : x.uaddOverflow y <;> simp [h1]

/-- Lowering `g_usubsat` with `g_usubo`: `usub.sat a b = let (r, ov) := usubo a b; ov ? 0 : r`. -/
theorem usubSat_subo (x y : LLVM.Int w) :
    x.usubSat y ⊒ GMIR.selectNonzero (x.usubOverflowFlag y) (.val (BitVec.ofInt w 0)) (x.sub y) := by
  cases x <;> cases y <;>
    simp [Int.usubSat, Int.sub, Int.usubOverflowFlag, GMIR.selectNonzero, Id.run, Data.LLVM.Int.isRefinedBy_eq, pure]
  rename_i x y
  by_cases h1 : x.usubOverflow y <;> simp [h1]

end Saturating

/-! ## gMIR combines

Definitions and tactics for the correctness lemmas of the gMIR combines, which are stated next to
the validity theorems at the end of this file. `combine_tac` unfolds the operations, splits their
poison checks, and closes the remaining bit-vector identity with `simp`, `omega` or `grind`'s ring
solver. The interpreters are written in the `Id` monad, so their poison checks are equations at
`Id (LLVM.Int w)`, which the `_id` lemmas below rewrite. -/

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
elab "casesAnd" : tactic => do
  let goals ← getGoals
  setGoals (← goals.flatMapM fun goal => casesAnd goal)

macro "llvm_refines" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  (repeat' split) <;>
    try simp_all [Data.LLVM.Int.poison_isRefinedBy, Data.LLVM.Int.isRefinedBy_refl, Data.LLVM.Int.isRefinedBy_eq, ite_poison_eq_val_id, val_eq_val_id,
      poison_eq_val_id, $ls,*]
  all_goals casesAnd
  all_goals (try subst_vars)
  all_goals try simp_all [Data.LLVM.Int.poison_isRefinedBy, Data.LLVM.Int.isRefinedBy_refl, Data.LLVM.Int.isRefinedBy_eq, ite_poison_eq_val_id, val_eq_val_id,
      poison_eq_val_id, $ls,*]
  all_goals try (simp only [BitVec.le_def, BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_two_pow_self,
    BitVec.natCast_eq_ofNat, ge_iff_le] at *; omega)
  all_goals grind))

macro "combine_tac" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [Int.add, Int.sub, Int.and, Int.or, Int.xor, Int.shl, Int.lshr, Int.ashr, Int.icmp, Int.zext,
    Int.sext, Int.trunc, Int.bitreverse, Int.smin, Int.smax, Int.umin, Int.umax, GMIR.selectNonzero,
    Id.run, pure]
  llvm_refines [$ls,*]))

variable {w : Nat}

/-- The `i1` negation that `createNot` builds. -/
@[expose] def notI1 (c : LLVM.Int 1) : LLVM.Int 1 := LLVM.Int.xor c (LLVM.Int.constant 1 (-1))

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

end Combines

end Veir.Data.LLVM

end

/-! # CTree validity of the gMIR combines

The `Pattern.Valid` and `Status` theorems of the combines of `RISCV64PostLegalizerCombiner` and
`RISCV64PreLegalizerCombiner`. Most are proven by `proveLegalValid with veir_pbv_decide`
(namespace `PBV`). The others, which `pbv_decide` does not decide, are proven with a correctness
lemma stated directly above them. -/

/-! CTree validity of the gMIR combines of `Veir.Passes.Legalization.CombinerHelper`. The combines
that test or compute the value of a matched `g_constant` follow. -/

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

/-- `canonicalize_icmp_pattern`: swapping the operands of a comparison swaps its predicate. -/
@[combine_valid, proof_pbv]
theorem combine_canonicalize_icmp_valid : Puddle.CTree.Pattern.Valid canonicalize_icmp_pattern := by
  proveLegalValid with
    (casesLocalsOf Data.LLVM.IntPred)
    all_goals (try simp only [swapIntPred, Data.LLVM.IntPred.inverse] at *)
    all_goals (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

/-- The low bit of an odd constant is set. -/
private theorem one_and_ofInt_of_odd {W : Nat} (hW : 0 < W) (v : _root_.Int) (hv : v % 2 = 1) :
    1#W &&& BitVec.ofInt W v = 1#W := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_one]
  by_cases h : i = 0
  · subst h
    simp only [decide_true, Bool.true_and, BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofInt,
      Nat.testBit_zero, decide_eq_true_eq]
    have hd : (2 : _root_.Int) ∣ ((2 ^ W : Nat) : _root_.Int) := by
      refine ⟨((2 ^ (W - 1) : Nat) : _root_.Int), ?_⟩
      rw [show W = (W - 1) + 1 by omega, Nat.pow_succ]
      push_cast
      rw [_root_.Int.mul_comm]
    have h1 : (v % ((2 ^ W : Nat) : _root_.Int)) % 2 = 1 := by
      rw [_root_.Int.emod_emod_of_dvd _ hd]; exact hv
    have h0 : 0 ≤ v % ((2 ^ W : Nat) : _root_.Int) :=
      _root_.Int.emod_nonneg _ (by have := Nat.two_pow_pos W; omega)
    omega
  · simp [h]

/-- `redundant_and_pattern`, for an `i1` result: masking a comparison with an odd constant keeps it. -/
private theorem and_icmp_odd {v : Nat} (x y : Data.LLVM.Int v) (p : Data.LLVM.IntPred) (c : _root_.Int)
    (hc : c % 2 = 1) : (x.icmp y p).and (.val (BitVec.ofInt 1 c)) ⊒ x.icmp y p := by
  have := one_and_ofInt_of_odd (W := 1) (by decide) c hc
  cases x <;> cases y <;> simp only [Data.LLVM.Int.icmp, Data.LLVM.Int.and, Id.run, Data.LLVM.Int.isRefinedBy_eq, pure]
  rename_i a b
  cases Data.LLVM.IntPred.eval p a b <;> simp_all

/-- `redundant_and_pattern`, for a wider result: the comparison is zero-extended to `0` or `1`. -/
private theorem and_zext_icmp_odd {v W : Nat} (x y : Data.LLVM.Int v) (p : Data.LLVM.IntPred) (c : _root_.Int)
    (hc : c % 2 = 1) (hW : 1 < W) :
    ((x.icmp y p).zext W false hW).and (.val (BitVec.ofInt W c)) ⊒ (x.icmp y p).zext W false hW := by
  have := one_and_ofInt_of_odd (W := W) (by omega) c hc
  cases x <;> cases y <;>
    simp only [Data.LLVM.Int.icmp, Data.LLVM.Int.and, Data.LLVM.Int.zext, Id.run, Data.LLVM.Int.isRefinedBy_eq, pure]
  rename_i a b
  have h1 : BitVec.setWidth W 1#1 = 1#W := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, Nat.one_mod_two_pow (by omega : 0 < W)]
  cases Data.LLVM.IntPred.eval p a b <;> simp_all [BitVec.setWidth_eq]

/-- `redundant_and_select_pattern .icmp .icmp`, for an `i1` result: both arms are comparisons. -/
private theorem and_select_icmp_odd {wc v₁ v₂ : Nat} (c : Data.LLVM.Int wc) (x y : Data.LLVM.Int v₁)
    (x' y' : Data.LLVM.Int v₂) (p q : Data.LLVM.IntPred) (k : _root_.Int) (hk : k % 2 = 1) :
    (GMIR.selectNonzero c (x.icmp y p) (x'.icmp y' q)).and (.val (BitVec.ofInt 1 k)) ⊒
      GMIR.selectNonzero c (x.icmp y p) (x'.icmp y' q) := by
  cases c with
  | poison => simp [GMIR.selectNonzero, Data.LLVM.Int.and, Id.run, Data.LLVM.Int.poison_isRefinedBy]
  | val c =>
    by_cases h : c = 0#wc <;> simp only [GMIR.selectNonzero, Id.run, h, bne_self_eq_false, ite_false,
      ite_true, bne_iff_ne, ne_eq, not_false_eq_true, Bool.false_eq_true]
    · exact and_icmp_odd x' y' q k hk
    · exact and_icmp_odd x y p k hk

/-- `redundant_and_select_pattern .icmp .icmp`, for a wider result. -/
private theorem and_select_zext_icmp_odd {wc v₁ v₂ W : Nat} (c : Data.LLVM.Int wc) (x y : Data.LLVM.Int v₁)
    (x' y' : Data.LLVM.Int v₂) (p q : Data.LLVM.IntPred) (k : _root_.Int) (hk : k % 2 = 1) (hW : 1 < W) :
    (GMIR.selectNonzero c ((x.icmp y p).zext W false hW) ((x'.icmp y' q).zext W false hW)).and
        (.val (BitVec.ofInt W k)) ⊒
      GMIR.selectNonzero c ((x.icmp y p).zext W false hW) ((x'.icmp y' q).zext W false hW) := by
  cases c with
  | poison => simp [GMIR.selectNonzero, Data.LLVM.Int.and, Id.run, Data.LLVM.Int.poison_isRefinedBy]
  | val c =>
    by_cases h : c = 0#wc <;> simp only [GMIR.selectNonzero, Id.run, h, bne_self_eq_false, ite_false,
      ite_true, bne_iff_ne, ne_eq, not_false_eq_true, Bool.false_eq_true]
    · exact and_zext_icmp_odd x' y' q k hk hW
    · exact and_zext_icmp_odd x y p k hk hW

set_option maxHeartbeats 8000000 in
/-- The two comparisons and the constant make this the slowest combine to normalize. -/
@[combine_valid, proof_manual]
theorem combine_redundant_and_select_icmp_icmp_valid :
    Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .icmp .icmp) := by
  proveLegalValid with first
    | (apply and_select_zext_icmp_odd <;> assumption)
    | (apply and_select_icmp_odd <;> assumption)

@[combine_valid, proof_manual]
theorem combine_redundant_and_valid : Puddle.CTree.Pattern.Valid redundant_and_pattern := by
  proveLegalValid with first
    | (apply and_zext_icmp_odd <;> assumption)
    | (apply and_icmp_odd <;> assumption)

/-! ### Funnel shifts or-ed with the shift they subsume

`(fshl x z y) | (x << y) → fshl x z y` and `(z >> y) | (fshr x z y) → fshr x z y`, in both orders:
the plain shift's bits are among the funnel shift's when the amount is in range, and it is poison
otherwise. -/

/-- The bits of `x << s` are among those of `fshl x z s`, for `s < w`. -/
private theorem fshl_or_shl_bits {w : Nat} (x z : BitVec w) (s : Nat) :
    ((x ++ z) <<< s).extractLsb' w w ||| x <<< s = ((x ++ z) <<< s).extractLsb' w w := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_or, BitVec.getElem_extractLsb', BitVec.getElem_shiftLeft,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append]
  by_cases h : i < s
  · simp [h]
  · have : ¬ w + i < s := by omega
    simp only [h, this, decide_false, Bool.not_false, Bool.true_and, show w + i < w + w by omega,
      decide_true, show ¬ (w + i - s < w) by omega, ite_false, BitVec.getLsbD_eq_getElem (by omega : i - s < w),
      show w + i - s - w = i - s by omega]
    simp

private theorem fshl_or_shl {w v : Nat} (x z : Data.LLVM.Int w) (y : Data.LLVM.Int v) (n u d : Bool) :
    (x.fshl z (GMIR.funnelShiftAmount w y)).or (x.shl (shiftAmount w y) n u) d ⊒
      x.fshl z (GMIR.funnelShiftAmount w y) := by
  cases x <;> cases z <;> cases y <;>
    simp [GMIR.funnelShiftAmount, shiftAmount, Data.LLVM.Int.fshl, Data.LLVM.Int.shl, Data.LLVM.Int.or,
      Id.run, Data.LLVM.Int.poison_isRefinedBy, pure]
  rename_i x z y
  by_cases h : y.toNat < w
  · have hw : w < 2 ^ w := Nat.lt_two_pow_self
    have hsw : (BitVec.setWidth w y).toNat = y.toNat := by
      simp only [BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by omega)
    have hm : y.toNat % w % 2 ^ w % w = y.toNat := by
      rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show y.toNat < 2 ^ w by omega), Nat.mod_eq_of_lt h]
    have hlt : ¬ BitVec.ofNat w w ≤ BitVec.setWidth w y := by
      simp only [BitVec.le_def, hsw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
      omega
    simp only [h, ite_true, hlt, ite_false, hsw, hm]
    split
    · rename_i y' heq
      simp only [Data.LLVM.ite_poison_eq_val_id, Data.LLVM.val_eq_val_id] at heq
      obtain ⟨-, -, rfl⟩ := heq
      split <;> simp [Data.LLVM.Int.poison_isRefinedBy, Data.LLVM.Int.isRefinedBy_eq, fshl_or_shl_bits]
    · simp [Data.LLVM.Int.poison_isRefinedBy]
  · have hge : BitVec.ofNat w w ≤ BitVec.allOnes w := by
      have := Nat.lt_two_pow_self (n := w)
      simp [BitVec.le_def, BitVec.toNat_allOnes, Nat.mod_eq_of_lt this]
      omega
    simp [h, hge, Data.LLVM.Int.poison_isRefinedBy]

/-- `g_or` is commutative, including its `disjoint` check. -/
private theorem or_comm' {w : Nat} (a b : Data.LLVM.Int w) (d : Bool) : a.or b d = b.or a d := by
  cases a <;> cases b <;> simp [Data.LLVM.Int.or, Id.run, BitVec.or_comm, BitVec.and_comm]

private theorem shl_or_fshl {w v : Nat} (x z : Data.LLVM.Int w) (y : Data.LLVM.Int v) (n u d : Bool) :
    (x.shl (shiftAmount w y) n u).or (x.fshl z (GMIR.funnelShiftAmount w y)) d ⊒
      x.fshl z (GMIR.funnelShiftAmount w y) := by
  rw [or_comm']
  exact fshl_or_shl x z y n u d

@[combine_valid, proof_manual]
theorem combine_funnel_shift_fshl_or_shl_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_or_shift_pattern .g_fshl .g_shl true true) := by
  proveLegalValid using fshl_or_shl

@[combine_valid, proof_manual]
theorem combine_funnel_shift_shl_or_fshl_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_or_shift_pattern .g_fshl .g_shl true false) := by
  proveLegalValid using shl_or_fshl

/-! ## Status of every combine -/

@[legalization_status]
theorem combine_funnel_shift_fshl_or_shl_status :
    Status Unproven (funnel_shift_or_shift_pattern .g_fshl .g_shl true true) :=
  .proven combine_funnel_shift_fshl_or_shl_valid

@[legalization_status]
theorem combine_funnel_shift_shl_or_fshl_status :
    Status Unproven (funnel_shift_or_shift_pattern .g_fshl .g_shl true false) :=
  .proven combine_funnel_shift_shl_or_fshl_valid

@[legalization_status]
theorem combine_canonicalize_icmp_status :
    Status Unproven canonicalize_icmp_pattern :=
  .proven (combine_canonicalize_icmp_valid )

@[legalization_status]
theorem combine_redundant_and_status : Status Unproven redundant_and_pattern :=
  .proven combine_redundant_and_valid

@[legalization_status]
theorem combine_redundant_and_select_icmp_icmp_status :
    Status Unproven (redundant_and_select_pattern .icmp .icmp) :=
  .proven combine_redundant_and_select_icmp_icmp_valid

end Veir.Legalization.CTreeProofs

/-! CTree validity of the gMIR combines that test or compute the value of a matched `g_constant`.

`matchConstant` requires the constant's attribute to have the type of its result, as the verifier
does, so the combines read the constant at the width it has: `normalizeConstants` splits its
properties and substitutes that type, which leaves each constant as `BitVec.ofInt w v` with the
matcher's predicate as a hypothesis on it. Each goal is then closed by a lemma stated for an
arbitrary constant `c`, directly above the validity theorem that uses it.

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
macro "simpConstantPreds" : tactic => `(tactic|
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

open Veir.Data Veir.Data.LLVM in
/--
A widened `g_icmp` result is poison, zero or one: apply this to `LLVM.Int.icmp x y pred`.
These are the nonconstant arms matched by `matchBoolArm`; the constant arms are zero or one
directly.
-/
private theorem zext_i1_eq_poison_or_zero_or_one {w : Nat} (h : 1 < w) (c : LLVM.Int 1) :
    LLVM.Int.zext c w false h = .poison ∨
    LLVM.Int.zext c w false h = .val 0#w ∨
    LLVM.Int.zext c w false h = .val 1#w := by
  cases c with
  | poison => simp [LLVM.Int.zext, Id.run]
  | val c =>
    rcases BitVec.eq_zero_or_eq_one c with rfl | rfl <;>
      simp [LLVM.Int.zext, Id.run,
        BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide : 0 < 1)]

open Veir.Data Veir.Data.LLVM in
/-- An `i1` comparison arm of `redundant_and_select_pattern` is poison, zero or one. -/
private theorem icmp_eq_poison_or_zero_or_one {v : Nat} (x y : LLVM.Int v) (p : IntPred) :
    x.icmp y p = .poison ∨ x.icmp y p = .val 0#1 ∨ x.icmp y p = .val 1#1 := by
  cases x <;> cases y <;> simp [LLVM.Int.icmp, Id.run]
  rename_i a b
  cases p.eval a b <;> simp

open Veir.Data Veir.Data.LLVM in
/-- A constant arm of `redundant_and_select_pattern` is zero or one. -/
private theorem boolArm_of_constant {w : Nat} (c : BitVec w) (h : c = 0 ∨ c = 1) :
    LLVM.Int.val c = .poison ∨ LLVM.Int.val c = .val 0#w ∨ LLVM.Int.val c = .val 1#w := by
  rcases h with rfl | rfl <;> simp

/-- Closes a hypothesis of a local correctness lemma: a predicate of the matcher, or a
comparison or constant arm that is zero or one. -/
macro "closeConstSide" : tactic => `(tactic| first
  | assumption
  | exact zext_i1_eq_poison_or_zero_or_one ‹_› _
  | exact icmp_eq_poison_or_zero_or_one _ _ _
  | exact boolArm_of_constant _ ‹_›
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

/-- The steps of `normalizeTypedConstants` after `simpLegalSemantics`. -/
macro "normalizeTypedConstantsAfterSemantics" : tactic => `(tactic| (
  normalizeLegalValid
  normalizeConstants
  all_goals (casesLocalsOf Subtype)
  all_goals (try subst_vars)
  all_goals (try simp_all)
  normalizeLegalValid))

/-- Normalize a combine whose types are `TypeAttr`s, as the funnel shifts: also split each type, so
that the type of the constant, which `matchConstant` equates, substitutes, and normalize again. -/
macro "normalizeTypedConstants" : tactic => `(tactic| (
  conv => arg 1; cbv
  simpPuddleValid
  simpLegalSemantics
  normalizeTypedConstantsAfterSemantics))

/-! ### Multiplications and subtractions by a matched constant -/

open Veir.Data Veir.Data.LLVM in
private theorem right_identity_one_mul {w : Nat} (x : LLVM.Int w) (c : BitVec w) (hc : c.toNat = 1) (n u : Bool) :
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

@[combine_valid, proof_manual]
theorem combine_right_identity_one_int_valid :
    Puddle.CTree.Pattern.Valid (right_identity_one_int_pattern) := by
  proveConstValid using right_identity_one_mul

open Veir.Data Veir.Data.LLVM in
private theorem sub_one_from_sub {w : Nat} (x y : LLVM.Int w) (c : BitVec w) (hc : c.toInt = 1) (n₁ u₁ n₂ u₂ : Bool) :
    (x.sub y n₁ u₁).sub (.val c) n₂ u₂ ⊒ (y.xor (.val (BitVec.ofInt w (-1)))).add x := by
  have : c = 1#w := by
    rw [← BitVec.ofInt_toInt (x := c), hc]; simp
  subst this
  have hsub (a b : BitVec w) : a - b - 1#w = ~~~b + a := by
    rw [BitVec.not_eq_neg_add]; simp only [BitVec.sub_eq_add_neg]; ac_rfl
  rw [ofInt_neg_one]
  cases x <;> cases y <;> combine_tac [BitVec.xor_allOnes, hsub]

@[combine_valid, proof_manual]
theorem combine_sub_one_from_sub_valid :
    Puddle.CTree.Pattern.Valid (sub_one_from_sub_pattern) := by
  proveConstValid using sub_one_from_sub

open Veir.Data Veir.Data.LLVM in
private theorem ofInt_neg_toInt {w : Nat} (x : BitVec w) : BitVec.ofInt w (-x.toInt) = -x := by
  apply BitVec.eq_of_toInt_eq; simp [BitVec.toInt_ofInt, BitVec.toInt_neg]

open Veir.Data Veir.Data.LLVM in
private theorem sub_of_mul_const {w : Nat} (a x : LLVM.Int w) (c : BitVec w) (n₁ u₁ n₂ u₂ : Bool) :
    a.sub (x.mul (.val c) n₁ u₁) n₂ u₂ ⊒ a.add (x.mul (.val (BitVec.ofInt w (-c.toInt)))) := by
  rw [ofInt_neg_toInt]
  cases a <;> cases x <;> simp only [LLVM.Int.mul, Id.run, pure] <;>
    combine_tac [BitVec.mul_neg, BitVec.sub_eq_add_neg]

@[combine_valid, proof_manual]
theorem combine_sub_of_mul_const_valid :
    Puddle.CTree.Pattern.Valid (sub_of_mul_const_pattern) := by
  proveConstValid using sub_of_mul_const

open Veir.Data Veir.Data.LLVM in
private theorem mul_by_neg_one {w : Nat} (x : LLVM.Int w) (c : BitVec w) (hc : c = -1) (n u : Bool) :
    x.mul (.val c) n u ⊒ (LLVM.Int.val 0#w).sub x n := by
  subst hc
  cases x with
  | poison => simp [LLVM.Int.mul, Id.run, Data.LLVM.Int.poison_isRefinedBy]
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

@[combine_valid, proof_manual]
theorem combine_mul_by_neg_one_valid :
    Puddle.CTree.Pattern.Valid (mul_by_neg_one_pattern) := by
  proveConstValid using mul_by_neg_one

open Veir.Data Veir.Data.LLVM in
private theorem mulo_by_2 {w : Nat} (x : LLVM.Int w) (c : BitVec w) (hc : c.toInt = 2) (n u : Bool) :
    x.mul (.val c) n u ⊒ x.add x n u := by
  have hn : c.toNat = 2 := by
    have := BitVec.toInt_eq_toNat_of_msb (x := c); grind [BitVec.toInt_eq_toNat_cond]
  cases x with
  | poison => simp [LLVM.Int.mul, Id.run, Data.LLVM.Int.poison_isRefinedBy]
  | val x =>
    have hs : BitVec.smulOverflow x c = BitVec.saddOverflow x x := by
      simp only [BitVec.smulOverflow, BitVec.saddOverflow, hc]; congr 1 <;> simp <;> omega
    have hu : BitVec.umulOverflow x c = BitVec.uaddOverflow x x := by
      simp only [BitVec.umulOverflow, BitVec.uaddOverflow, hn]; congr 1; simp; omega
    have hv : x * c = x + x := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_mul, BitVec.toNat_add, hn, Nat.mul_two]
    simp only [LLVM.Int.mul, LLVM.Int.add, Id.run, hs, hu, hv]
    exact Data.LLVM.Int.isRefinedBy_refl _

@[combine_valid, proof_manual]
theorem combine_mulo_by_2_valid :
    Puddle.CTree.Pattern.Valid (mulo_by_2_pattern) := by
  proveConstValid using mulo_by_2

/-! ### Negated comparisons -/

open Veir.Data Veir.Data.LLVM in
private theorem not_cmp_fold {v : Nat} (x y : LLVM.Int v) (p : IntPred) (c : BitVec 1) (hc : c.toNat = 1) :
    (x.icmp y p).xor (.val c) ⊒ x.icmp y p.inverse := by
  have : c = 1#1 := BitVec.eq_of_toNat_eq (by simp [hc])
  subst this
  cases x <;> cases y <;> simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run, Data.LLVM.Int.poison_isRefinedBy,
    IntPred.eval_inverse]
  rename_i a b
  cases p.eval a b <;> exact Data.LLVM.Int.isRefinedBy_refl _

open Veir.Data Veir.Data.LLVM in
private theorem not_cmp_fold_zext {v W : Nat} (x y : LLVM.Int v) (p : IntPred) (h : 1 < W) (c : BitVec W)
    (hc : c.toNat = 1) :
    ((x.icmp y p).zext W false h).xor (.val c) ⊒ (x.icmp y p.inverse).zext W false h := by
  have : c = 1#W := BitVec.eq_of_toNat_eq (by
    simp [hc, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h (Nat.le_of_lt Nat.lt_two_pow_self))])
  subst this
  cases x <;> cases y <;> simp [LLVM.Int.icmp, LLVM.Int.xor, LLVM.Int.zext, Id.run,
    Data.LLVM.Int.poison_isRefinedBy, IntPred.eval_inverse]
  rename_i a b
  cases p.eval a b <;>
    simp [BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide : 0 < 1), Data.LLVM.Int.isRefinedBy_refl]

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_eq_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .eq .ne) := by
  proveConstValid using not_cmp_fold_zext, not_cmp_fold

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_ne_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ne .eq) := by
  proveConstValid using not_cmp_fold_zext, not_cmp_fold

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_ugt_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ugt .ule) := by
  proveConstValid using not_cmp_fold_zext, not_cmp_fold

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_uge_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .uge .ult) := by
  proveConstValid using not_cmp_fold_zext, not_cmp_fold

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_ult_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ult .uge) := by
  proveConstValid using not_cmp_fold_zext, not_cmp_fold

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_ule_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ule .ugt) := by
  proveConstValid using not_cmp_fold_zext, not_cmp_fold

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_sgt_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sgt .sle) := by
  proveConstValid using not_cmp_fold_zext, not_cmp_fold

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_sge_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sge .slt) := by
  proveConstValid using not_cmp_fold_zext, not_cmp_fold

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_slt_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .slt .sge) := by
  proveConstValid using not_cmp_fold_zext, not_cmp_fold

@[combine_valid, proof_manual]
theorem combine_not_cmp_fold_sle_valid :
    Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sle .sgt) := by
  proveConstValid using not_cmp_fold_zext, not_cmp_fold

/-! ### Powers of two

The matcher reads a power of two `±2^k` with `exactLog2?`, and the rewrite shifts by `k`.

The combines are proved for every width `w`. The divisor is the constant `±2^k`, and the created
shift amounts are the constants `k`, `w - 1` and `w - k`. -/

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
  veir_bv_normalize
  grind [BitVec.lt_ofInt_natCast_ofNat_of_lt, BitVec.toNat_ofInt_natCast_of_lt,
    BitVec.udiv_twoPow_eq_of_lt]

@[combine_valid, proof_manual]
theorem combine_udiv_by_pow2_valid :
    Puddle.CTree.Pattern.Valid (udiv_by_pow2_pattern) := by
  proveConstValid using udiv_pow2

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
    veir_bv_normalize
    grind [BitVec.twoPow_eq_shiftLeft_one_ofInt_natCast, BitVec.lt_ofInt_natCast_ofNat_of_lt,
      BitVec.toNat_ofInt_natCast_of_lt, BitVec.sdiv_one_shl_of_smod_eq_zero]

@[combine_valid, proof_manual]
theorem combine_sdiv_exact_by_pow2_pos_valid :
    Puddle.CTree.Pattern.Valid (sdiv_exact_by_pow2_pattern false) := by
  proveConstValid using sdiv_exact_pow2_pos

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
    veir_bv_normalize
    grind [BitVec.twoPow_eq_shiftLeft_one_ofInt_natCast, BitVec.lt_ofInt_natCast_ofNat_of_lt,
      BitVec.toNat_ofInt_natCast_of_lt, BitVec.sdiv_neg_one_shl_of_smod_eq_zero]

@[combine_valid, proof_manual]
theorem combine_sdiv_exact_by_pow2_neg_valid :
    Puddle.CTree.Pattern.Valid (sdiv_exact_by_pow2_pattern true) := by
  proveConstValid using sdiv_exact_pow2_neg

private theorem shiftAmount_ofInt {w k : Nat} (hk : k < w) :
    shiftAmount w (Data.LLVM.Int.val (BitVec.ofInt w (k : Int))) = Data.LLVM.Int.constant w k := by
  rw [BitVec.ofInt_natCast]; exact shiftAmount_ofNat hk

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
    veir_bv_normalize
    grind [BitVec.twoPow_eq_shiftLeft_one_ofInt_natCast, BitVec.lt_ofInt_natCast_ofNat_of_lt,
      BitVec.toNat_ofInt_natCast_of_lt, BitVec.sdiv_one_shl_eq_biased_sshiftRight]

@[combine_valid, proof_manual]
theorem combine_sdiv_by_pow2_pos_valid :
    Puddle.CTree.Pattern.Valid (sdiv_by_pow2_pattern false) := by
  proveConstValid using sdiv_pow2_pos

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
    veir_bv_normalize
    grind [BitVec.twoPow_eq_shiftLeft_one_ofInt_natCast, BitVec.lt_ofInt_natCast_ofNat_of_lt,
      BitVec.toNat_ofInt_natCast_of_lt, BitVec.sdiv_neg_one_shl_eq_neg_biased_sshiftRight]

@[combine_valid, proof_manual]
theorem combine_sdiv_by_pow2_neg_valid :
    Puddle.CTree.Pattern.Valid (sdiv_by_pow2_pattern true) := by
  proveConstValid using sdiv_pow2_neg

open Veir.Data Veir.Data.LLVM in
/-- Prove the correctness of `mul_to_shl_pattern`: `x * 2^k` → `x << k`, whose flags carry over. A
multiplication that does not overflow makes the shift's no-wrap checks pass. -/
private theorem mul_twoPow_shl {w : Nat} (x : LLVM.Int w) (k : Nat) (hk : k + 1 < w) (n u : Bool) :
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
  | poison => simp [LLVM.Int.mul, Id.run, Data.LLVM.Int.poison_isRefinedBy]
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
    · simp [hs, Data.LLVM.Int.poison_isRefinedBy]
    by_cases hu : u = true ∧ BitVec.umulOverflow x (BitVec.twoPow w k) = true
    · simp [hu, Data.LLVM.Int.poison_isRefinedBy]
    have hs' : ¬ (n = true ∧ (x <<< BitVec.ofInt w (k : _root_.Int)).sshiftRight'
        (BitVec.ofInt w (k : _root_.Int)) ≠ x) := by
      rintro ⟨hn, hne⟩; exact hne (hnsw fun h => hs ⟨hn, h⟩)
    have hu' : ¬ (u = true ∧ x <<< BitVec.ofInt w (k : _root_.Int) >>>
        BitVec.ofInt w (k : _root_.Int) ≠ x) := by
      rintro ⟨hn, hne⟩; exact hne (hnuw fun h => hu ⟨hn, h⟩)
    simp only [hs, hu, hs', hu', ite_false]
    rw [hv]
    exact Data.LLVM.Int.isRefinedBy_refl _

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
  exact mul_twoPow_shl x k hkw n u

@[combine_valid, proof_manual]
theorem combine_mul_to_shl_valid :
    Puddle.CTree.Pattern.Valid (mul_to_shl_pattern) := by
  proveConstValid using mul_pow2

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
  | poison => simp [Data.LLVM.Int.urem, Id.run, Data.LLVM.Int.poison_isRefinedBy]
  | val x =>
    have hv : x % BitVec.twoPow w k = x &&& BitVec.ofNat w (2 ^ k - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_umod, BitVec.toNat_and, BitVec.toNat_twoPow_of_lt (by omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le (2 ^ k) 1) hlt),
        Nat.and_two_pow_sub_one_eq_mod]
    simp [Data.LLVM.Int.urem, Data.LLVM.Int.and, Id.run, hne, hv, Data.LLVM.Int.isRefinedBy_refl]

@[combine_valid, proof_manual]
theorem combine_urem_pow2_to_mask_valid :
    Puddle.CTree.Pattern.Valid (urem_pow2_to_mask_pattern) := by
  proveConstValid using urem_pow2

/-! ### Constant folding -/

@[combine_valid, proof_pbv]
theorem combine_constant_fold_mul_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_mul ((· * ·))) := by
  conv => arg 1; cbv
  simpPuddleValid
  simpLegalSemantics
  normalizeLegalValid
  normalizeConstants
  all_goals (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

/-! ### Selects of two constants -/

open Veir.Data Veir.Data.LLVM in
/--
Prove all four `redundant_and_select_pattern` arm combinations at every width, for any mask with
its low bit set. The hypotheses admit poison from a comparison, including on an unselected arm;
`zext_i1_eq_poison_or_zero_or_one` supplies them for widened comparisons.
-/
private theorem and_select_bool {w wc : Nat} (c : LLVM.Int wc) (t f : LLVM.Int w)
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

open Veir.Data Veir.Data.LLVM in
/-- `redundant_and_select_pattern`, whose mask `k` is odd as an integer, at every width. -/
private theorem and_select_bool_odd {w : Nat} {wc : Nat} (c : LLVM.Int wc) (t f : LLVM.Int w) (k : _root_.Int)
    (hk : k % 2 = 1)
    (ht : t = .poison ∨ t = .val 0#w ∨ t = .val 1#w)
    (hf : f = .poison ∨ f = .val 0#w ∨ f = .val 1#w) :
    LLVM.Int.and (GMIR.selectNonzero c t f) (.val (BitVec.ofInt w k)) ⊒ GMIR.selectNonzero c t f := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · generalize GMIR.selectNonzero c t f = r
    cases r <;> simp [LLVM.Int.and, Id.run, Data.LLVM.Int.poison_isRefinedBy, Data.LLVM.Int.isRefinedBy_refl,
      BitVec.of_length_zero]
  · rw [and_select_bool c t f _ _ ht hf]
    · exact Data.LLVM.Int.isRefinedBy_refl _
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

set_option maxHeartbeats 4000000 in
@[combine_valid, proof_manual]
theorem combine_redundant_and_select_icmp_constant_valid :
    Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .icmp .constant) := by
  proveConstValid using and_select_bool_odd

set_option maxHeartbeats 4000000 in
@[combine_valid, proof_manual]
theorem combine_redundant_and_select_constant_icmp_valid :
    Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .constant .icmp) := by
  proveConstValid using and_select_bool_odd

set_option maxHeartbeats 4000000 in
@[combine_valid, proof_manual]
theorem combine_redundant_and_select_constant_constant_valid :
    Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .constant .constant) := by
  proveConstValid using and_select_bool_odd

open Veir.Data Veir.Data.LLVM in
/-- A property of `GMIR.selectNonzero` on an `i1` condition follows from its three cases. -/
private theorem selectNonzero_refines {w : Nat} (c : LLVM.Int 1) (x y : LLVM.Int w)
    (r : LLVM.Int w)
    (hp : c = .poison → r = .poison)
    (h1 : c = .val 1#1 → x ⊒ r) (h0 : c = .val 0#1 → y ⊒ r) :
    GMIR.selectNonzero c x y ⊒ r := by
  cases c with
  | poison => simp [GMIR.selectNonzero, Id.run, hp, LLVM.Int.isRefinedBy]
  | val c =>
    rcases BitVec.eq_zero_or_eq_one c with rfl | rfl
    · simpa [GMIR.selectNonzero, Id.run] using h0 rfl
    · simpa [GMIR.selectNonzero, Id.run] using h1 rfl

/-- Closes one case of a `tryFoldSelectOfConstants` proof, where the condition is known. -/
macro "select_const_tac" : tactic =>
  `(tactic| (simp_all [Veir.Data.LLVM.notI1, Nat.not_le_of_gt, Nat.mod_eq_of_lt,
      BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt, BitVec.signExtend, BitVec.ofInt_neg,
      BitVec.twoPow_eq, BitVec.add_comm, BitVec.sub_eq_add_neg, BitVec.neg_one_eq_allOnes,
      Veir.Data.LLVM.Int.xor, Veir.Data.LLVM.Int.zext, Veir.Data.LLVM.Int.sext, Veir.Data.LLVM.Int.add, Veir.Data.LLVM.Int.shl, Veir.Data.LLVM.Int.or,
      Veir.Data.LLVM.Int.constant, Id.run, Veir.Data.LLVM.Int.isRefinedBy]))

open Veir.Data Veir.Data.LLVM in
/-- Prove the correctness of combining `c ? 2^k : 0` to `shl (zext c), k`. -/
private theorem select_pow2_zero {w : Nat} (h : 1 < w) (c : LLVM.Int 1) (k : Nat) (hk : k < w) :
    GMIR.selectNonzero c (LLVM.Int.val (BitVec.twoPow w k)) (LLVM.Int.constant w 0) ⊒
      LLVM.Int.shl (LLVM.Int.zext c w false h) (LLVM.Int.constant w k) := by
  have hkpow := Nat.lt_trans hk Nat.lt_two_pow_self
  apply selectNonzero_refines <;> rintro rfl <;> select_const_tac

private theorem constant_eq {w : Nat} (v : Int) :
    Data.LLVM.Int.constant w v = .val (BitVec.ofInt w v) := rfl

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
  simpa [constant_eq] using select_pow2_zero h c k hkw

@[combine_valid, proof_manual]
theorem combine_select_pow2_zero_valid :
    Puddle.CTree.Pattern.Valid (select_pow2_zero_pattern) := by
  proveConstValid using soc_pow2_zero

open Veir.Data Veir.Data.LLVM in
/-- Prove the correctness of combining `c ? 0 : 2^k` to `shl (zext (not c)), k`. -/
private theorem select_zero_pow2 {w : Nat} (h : 1 < w) (c : LLVM.Int 1) (k : Nat) (hk : k < w) :
    GMIR.selectNonzero c (LLVM.Int.constant w 0) (LLVM.Int.val (BitVec.twoPow w k)) ⊒
      LLVM.Int.shl (LLVM.Int.zext (notI1 c) w false h) (LLVM.Int.constant w k) := by
  have hkpow := Nat.lt_trans hk Nat.lt_two_pow_self
  apply selectNonzero_refines <;> rintro rfl <;> select_const_tac

private theorem ofInt_one_neg_one : BitVec.ofInt 1 (-1) = 1#1 := by decide

private theorem notI1_eq (c : Data.LLVM.Int 1) : Data.LLVM.notI1 c = c.xor (.val 1#1) := by
  simp [Data.LLVM.notI1, constant_eq, ofInt_one_neg_one]

private theorem soc_zero_pow2 {w : Nat} (h : 1 < w) (_hw : w ≤ 64) (c : Data.LLVM.Int 1)
    (t f : BitVec w) (hf : (exactLog2? f.toNat).isSome = true) (ht : t = 0) :
    GMIR.selectNonzero c (.val t) (.val f) ⊒
      ((c.xor (.val 1#1)).zext w false h).shl
        (shiftAmount w (.val (BitVec.ofNat w (exactLog2? f.toNat).get!))) := by
  obtain ⟨k, hk, hkw, rfl⟩ := ulog2_some hf
  subst ht
  rw [hk, Option.get!_some, shiftAmount_ofNat hkw]
  simpa [constant_eq, notI1_eq] using select_zero_pow2 h c k hkw

@[combine_valid, proof_manual]
theorem combine_select_zero_pow2_valid :
    Puddle.CTree.Pattern.Valid (select_zero_pow2_pattern) := by
  proveConstValid using soc_zero_pow2

/-! ### Funnel shifts by a constant -/

private theorem fshr_zero {w v : Nat} (x y : Data.LLVM.Int w) (c : BitVec v) (hc : c = 0) :
    x.fshr y (GMIR.funnelShiftAmount w (.val c)) ⊒ y := by
  subst hc
  cases x <;> cases y <;> simp [Data.LLVM.Int.fshr, GMIR.funnelShiftAmount, Id.run, Data.LLVM.Int.poison_isRefinedBy]
  ext i hi; simp [hi, BitVec.getLsbD_append]

set_option maxHeartbeats 4000000 in
@[combine_valid, proof_manual]
theorem combine_funnel_shift_right_zero_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_zero_pattern .g_fshr true) := by
  normalizeTypedConstants
  all_goals closeConstWith fshr_zero

private theorem fshl_zero {w v : Nat} (x y : Data.LLVM.Int w) (c : BitVec v) (hc : c = 0) :
    x.fshl y (GMIR.funnelShiftAmount w (.val c)) ⊒ x := by
  subst hc
  cases x <;> cases y <;> simp [Data.LLVM.Int.fshl, GMIR.funnelShiftAmount, Id.run, Data.LLVM.Int.poison_isRefinedBy]
  ext i hi; simp [hi, BitVec.getLsbD_append, BitVec.getElem_extractLsb', BitVec.getElem_append,
    show ¬ w + i < w by omega]

set_option maxHeartbeats 4000000 in
@[combine_valid, proof_manual]
theorem combine_funnel_shift_left_zero_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_zero_pattern .g_fshl false) := by
  normalizeTypedConstants
  all_goals closeConstWith fshl_zero

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

set_option maxHeartbeats 4000000 in
@[combine_valid, proof_manual]
theorem combine_funnel_shift_overshift_l_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_overshift_pattern .g_fshl) := by
  conv => arg 1; cbv
  simpPuddleValid
  simpLegalSemantics
  /- The created `g_constant` reads its type `amtType` as an integer or a pointer type: substitute
  the integer type the matched constant gives it before `simp_all` rewrites with that equation. -/
  intros
  all_goals (casesLocalsOf Subtype)
  all_goals (try dsimp only at *)
  all_goals (try subst_vars)
  normalizeTypedConstantsAfterSemantics
  all_goals (obtain ⟨t, rfl⟩ := overshiftAmount?_isSome ‹_›)
  all_goals (simp only [RuntimeValue.Conforms] at *)
  all_goals subst_vars
  all_goals (simp only [overshiftAmount?_integerType] at *)
  all_goals split
  all_goals (try simp_all [funnelShiftAmount_overshift', RuntimeValue.isRefinedBy, Data.LLVM.Int.isRefinedBy_refl])
  all_goals (rename_i heq; subst heq)
  all_goals (simp only [funnelShiftAmount_overshift']; exact Data.LLVM.Int.isRefinedBy_refl _)

set_option maxHeartbeats 4000000 in
@[combine_valid, proof_manual]
theorem combine_funnel_shift_overshift_r_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_overshift_pattern .g_fshr) := by
  conv => arg 1; cbv
  simpPuddleValid
  simpLegalSemantics
  /- The created `g_constant` reads its type `amtType` as an integer or a pointer type: substitute
  the integer type the matched constant gives it before `simp_all` rewrites with that equation. -/
  intros
  all_goals (casesLocalsOf Subtype)
  all_goals (try dsimp only at *)
  all_goals (try subst_vars)
  normalizeTypedConstantsAfterSemantics
  all_goals (obtain ⟨t, rfl⟩ := overshiftAmount?_isSome ‹_›)
  all_goals (simp only [RuntimeValue.Conforms] at *)
  all_goals subst_vars
  all_goals (simp only [overshiftAmount?_integerType] at *)
  all_goals split
  all_goals (try simp_all [funnelShiftAmount_overshift', RuntimeValue.isRefinedBy, Data.LLVM.Int.isRefinedBy_refl])
  all_goals (rename_i heq; subst heq)
  all_goals (simp only [funnelShiftAmount_overshift']; exact Data.LLVM.Int.isRefinedBy_refl _)

/-! ## Status of every combine that matches a constant -/

@[legalization_status]
theorem combine_right_identity_one_int_status :
    Status Unproven (right_identity_one_int_pattern) :=
  .proven (combine_right_identity_one_int_valid)

@[legalization_status]
theorem combine_sub_one_from_sub_status :
    Status Unproven (sub_one_from_sub_pattern) :=
  .proven (combine_sub_one_from_sub_valid)

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
theorem combine_constant_fold_mul_status :
    Status Unproven (constant_fold_binop_pattern .g_mul ((· * ·))) :=
  .proven (combine_constant_fold_mul_valid)

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
theorem combine_select_pow2_zero_status :
    Status Unproven (select_pow2_zero_pattern) :=
  .proven (combine_select_pow2_zero_valid)

@[legalization_status]
theorem combine_select_zero_pow2_status :
    Status Unproven (select_zero_pow2_pattern) :=
  .proven (combine_select_zero_pow2_valid)

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

/-!
# CTree validity of the gMIR combines (`Validity/Combine`) by `pbv_decide`

Each rule is proven by `proveLegalValid with veir_pbv_decide` alone, without `sorry`: the matchers
bound every integer width by 64, which discharges the side goals `w ≤ 64` of `pbv_decide`. The rules `veir_pbv_decide` does not prove are commented out, with the reason it
fails.
-/
namespace Veir.Legalization.CTreeProofs.PBV

open Puddle
open Puddle.CTree
open _root_.CTree

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  GMIR.interpretOp' GMIR.interpretOpCTree GMIR_RISCV.interpretOp'

attribute [local simp] GMIR.isTerminator GMIR.getEffects GMIR_RISCV.base

attribute [local implicit_reducible] TypeAttr

@[combine_valid, proof_pbv]
theorem combine_hoist_and_shl_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_and .g_shl) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_hoist_and_shl_status :
    Status Unproven (hoist_logic_op_pattern .g_and .g_shl) :=
  .proven (combine_hoist_and_shl_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_and_lshr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_and .g_lshr) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_hoist_and_lshr_status :
    Status Unproven (hoist_logic_op_pattern .g_and .g_lshr) :=
  .proven (combine_hoist_and_lshr_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_and_ashr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_and .g_ashr) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_hoist_and_ashr_status :
    Status Unproven (hoist_logic_op_pattern .g_and .g_ashr) :=
  .proven (combine_hoist_and_ashr_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_and_and_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_and .g_and) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_hoist_and_and_status :
    Status Unproven (hoist_logic_op_pattern .g_and .g_and) :=
  .proven (combine_hoist_and_and_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_or_shl_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_or .g_shl) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_hoist_or_shl_status :
    Status Unproven (hoist_logic_op_pattern .g_or .g_shl) :=
  .proven (combine_hoist_or_shl_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_or_lshr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_or .g_lshr) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_hoist_or_lshr_status :
    Status Unproven (hoist_logic_op_pattern .g_or .g_lshr) :=
  .proven (combine_hoist_or_lshr_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_or_ashr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_or .g_ashr) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_hoist_or_ashr_status :
    Status Unproven (hoist_logic_op_pattern .g_or .g_ashr) :=
  .proven (combine_hoist_or_ashr_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_or_and_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_or .g_and) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_hoist_or_and_status :
    Status Unproven (hoist_logic_op_pattern .g_or .g_and) :=
  .proven (combine_hoist_or_and_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_xor_shl_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_xor .g_shl) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_hoist_xor_shl_status :
    Status Unproven (hoist_logic_op_pattern .g_xor .g_shl) :=
  .proven (combine_hoist_xor_shl_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_xor_lshr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_xor .g_lshr) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_hoist_xor_lshr_status :
    Status Unproven (hoist_logic_op_pattern .g_xor .g_lshr) :=
  .proven (combine_hoist_xor_lshr_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_xor_ashr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_xor .g_ashr) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_hoist_xor_ashr_status :
    Status Unproven (hoist_logic_op_pattern .g_xor .g_ashr) :=
  .proven (combine_hoist_xor_ashr_valid )

@[combine_valid, proof_pbv]
theorem combine_hoist_xor_and_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_xor .g_and) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_hoist_xor_and_status :
    Status Unproven (hoist_logic_op_pattern .g_xor .g_and) :=
  .proven (combine_hoist_xor_and_valid )

@[combine_valid, proof_pbv]
theorem combine_sub_add_reg_x_add_y_sub_y_valid : Puddle.CTree.Pattern.Valid sub_add_reg_x_add_y_sub_y_pattern := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_sub_add_reg_x_add_y_sub_y_status :
    Status Unproven sub_add_reg_x_add_y_sub_y_pattern :=
  .proven (combine_sub_add_reg_x_add_y_sub_y_valid )

@[combine_valid, proof_pbv]
theorem combine_sub_add_reg_x_add_y_sub_x_valid : Puddle.CTree.Pattern.Valid sub_add_reg_x_add_y_sub_x_pattern := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_sub_add_reg_x_add_y_sub_x_status :
    Status Unproven sub_add_reg_x_add_y_sub_x_pattern :=
  .proven (combine_sub_add_reg_x_add_y_sub_x_valid )

@[combine_valid, proof_pbv]
theorem combine_sub_add_reg_negate_valid : Puddle.CTree.Pattern.Valid (sub_add_reg_negate_pattern false) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_sub_add_reg_negate_status :
    Status Unproven (sub_add_reg_negate_pattern false) :=
  .proven (combine_sub_add_reg_negate_valid )

@[combine_valid, proof_pbv]
theorem combine_sub_add_reg_negate_x_first_valid : Puddle.CTree.Pattern.Valid (sub_add_reg_negate_pattern true) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_sub_add_reg_negate_x_first_status :
    Status Unproven (sub_add_reg_negate_pattern true) :=
  .proven (combine_sub_add_reg_negate_x_first_valid )

@[combine_valid, proof_pbv]
theorem combine_xor_of_and_with_same_reg_valid : Puddle.CTree.Pattern.Valid xor_of_and_with_same_reg_pattern := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_xor_of_and_with_same_reg_status :
    Status Unproven xor_of_and_with_same_reg_pattern :=
  .proven (combine_xor_of_and_with_same_reg_valid )

@[combine_valid, proof_pbv]
theorem combine_trunc_of_zext_valid : Puddle.CTree.Pattern.Valid (trunc_of_ext_pattern .g_zext) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_trunc_of_zext_status :
    Status Unproven (trunc_of_ext_pattern .g_zext) :=
  .proven (combine_trunc_of_zext_valid )

@[combine_valid, proof_pbv]
theorem combine_trunc_of_sext_valid : Puddle.CTree.Pattern.Valid (trunc_of_ext_pattern .g_sext) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_trunc_of_sext_status :
    Status Unproven (trunc_of_ext_pattern .g_sext) :=
  .proven (combine_trunc_of_sext_valid )

@[combine_valid, proof_pbv]
theorem combine_redundant_add_eq_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_add .eq) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_redundant_add_eq_status :
    Status Unproven (redundant_binop_in_equality_pattern .g_add .eq) :=
  .proven (combine_redundant_add_eq_valid )

@[combine_valid, proof_pbv]
theorem combine_redundant_add_ne_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_add .ne) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_redundant_add_ne_status :
    Status Unproven (redundant_binop_in_equality_pattern .g_add .ne) :=
  .proven (combine_redundant_add_ne_valid )

@[combine_valid, proof_pbv]
theorem combine_redundant_sub_eq_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_sub .eq) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_redundant_sub_eq_status :
    Status Unproven (redundant_binop_in_equality_pattern .g_sub .eq) :=
  .proven (combine_redundant_sub_eq_valid )

@[combine_valid, proof_pbv]
theorem combine_redundant_sub_ne_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_sub .ne) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_redundant_sub_ne_status :
    Status Unproven (redundant_binop_in_equality_pattern .g_sub .ne) :=
  .proven (combine_redundant_sub_ne_valid )

@[combine_valid, proof_pbv]
theorem combine_redundant_xor_eq_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_xor .eq) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_redundant_xor_eq_status :
    Status Unproven (redundant_binop_in_equality_pattern .g_xor .eq) :=
  .proven (combine_redundant_xor_eq_valid )

@[combine_valid, proof_pbv]
theorem combine_redundant_xor_ne_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_xor .ne) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_redundant_xor_ne_status :
    Status Unproven (redundant_binop_in_equality_pattern .g_xor .ne) :=
  .proven (combine_redundant_xor_ne_valid )

@[combine_valid, proof_pbv]
theorem combine_combine_or_of_and_tt_valid : Puddle.CTree.Pattern.Valid (combine_or_of_and_pattern true true) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_combine_or_of_and_tt_status :
    Status Unproven (combine_or_of_and_pattern true true) :=
  .proven (combine_combine_or_of_and_tt_valid )

@[combine_valid, proof_pbv]
theorem combine_combine_or_of_and_tf_valid : Puddle.CTree.Pattern.Valid (combine_or_of_and_pattern true false) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_combine_or_of_and_tf_status :
    Status Unproven (combine_or_of_and_pattern true false) :=
  .proven (combine_combine_or_of_and_tf_valid )

@[combine_valid, proof_pbv]
theorem combine_combine_or_of_and_ft_valid : Puddle.CTree.Pattern.Valid (combine_or_of_and_pattern false true) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_combine_or_of_and_ft_status :
    Status Unproven (combine_or_of_and_pattern false true) :=
  .proven (combine_combine_or_of_and_ft_valid )

@[combine_valid, proof_pbv]
theorem combine_combine_or_of_and_ff_valid : Puddle.CTree.Pattern.Valid (combine_or_of_and_pattern false false) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_combine_or_of_and_ff_status :
    Status Unproven (combine_or_of_and_pattern false false) :=
  .proven (combine_combine_or_of_and_ff_valid )

@[combine_valid, proof_pbv]
theorem combine_AMinusBMinusC_valid : Puddle.CTree.Pattern.Valid AMinusBMinusC_pattern := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_AMinusBMinusC_status :
    Status Unproven AMinusBMinusC_pattern :=
  .proven (combine_AMinusBMinusC_valid )

@[combine_valid, proof_pbv]
theorem combine_zext_of_zext_valid : Puddle.CTree.Pattern.Valid (ext_of_ext_pattern .g_zext) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_zext_of_zext_status :
    Status Unproven (ext_of_ext_pattern .g_zext) :=
  .proven (combine_zext_of_zext_valid )

@[combine_valid, proof_pbv]
theorem combine_sext_of_sext_valid : Puddle.CTree.Pattern.Valid (ext_of_ext_pattern .g_sext) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_sext_of_sext_status :
    Status Unproven (ext_of_ext_pattern .g_sext) :=
  .proven (combine_sext_of_sext_valid )

@[combine_valid, proof_pbv]
theorem combine_bitreverse_shl_valid : Puddle.CTree.Pattern.Valid (bitreverse_shift_pattern .g_shl .g_lshr) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_bitreverse_shl_status :
    Status Unproven (bitreverse_shift_pattern .g_shl .g_lshr) :=
  .proven (combine_bitreverse_shl_valid )

@[combine_valid, proof_pbv]
theorem combine_bitreverse_lshr_valid : Puddle.CTree.Pattern.Valid (bitreverse_shift_pattern .g_lshr .g_shl) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_bitreverse_lshr_status :
    Status Unproven (bitreverse_shift_pattern .g_lshr .g_shl) :=
  .proven (combine_bitreverse_lshr_valid )

@[combine_valid, proof_pbv]
theorem combine_binop_same_val_and_valid : Puddle.CTree.Pattern.Valid (binop_same_val_pattern .g_and) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_binop_same_val_and_status :
    Status Unproven (binop_same_val_pattern .g_and) :=
  .proven (combine_binop_same_val_and_valid )

@[combine_valid, proof_pbv]
theorem combine_binop_same_val_or_valid : Puddle.CTree.Pattern.Valid (binop_same_val_pattern .g_or) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_binop_same_val_or_status :
    Status Unproven (binop_same_val_pattern .g_or) :=
  .proven (combine_binop_same_val_or_valid )

@[combine_valid, proof_pbv]
theorem combine_same_val_zero_sub_valid : Puddle.CTree.Pattern.Valid (same_val_zero_pattern .g_sub) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_same_val_zero_sub_status :
    Status Unproven (same_val_zero_pattern .g_sub) :=
  .proven (combine_same_val_zero_sub_valid )

@[combine_valid, proof_pbv]
theorem combine_same_val_zero_xor_valid : Puddle.CTree.Pattern.Valid (same_val_zero_pattern .g_xor) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_same_val_zero_xor_status :
    Status Unproven (same_val_zero_pattern .g_xor) :=
  .proven (combine_same_val_zero_xor_valid )

@[combine_valid, proof_pbv]
theorem combine_add_sub_reg_0_valid : Puddle.CTree.Pattern.Valid add_sub_reg_0_pattern := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_add_sub_reg_0_status :
    Status Unproven add_sub_reg_0_pattern :=
  .proven (combine_add_sub_reg_0_valid )

@[combine_valid, proof_pbv]
theorem combine_add_sub_reg_1_valid : Puddle.CTree.Pattern.Valid add_sub_reg_1_pattern := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_add_sub_reg_1_status :
    Status Unproven add_sub_reg_1_pattern :=
  .proven (combine_add_sub_reg_1_valid )

@[combine_valid, proof_pbv]
theorem combine_APlusBMinusCMinusB_valid : Puddle.CTree.Pattern.Valid APlusBMinusCMinusB_pattern := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_APlusBMinusCMinusB_status :
    Status Unproven APlusBMinusCMinusB_pattern :=
  .proven (combine_APlusBMinusCMinusB_valid )

@[combine_valid, proof_pbv]
theorem combine_AMinusBMinusCMinusC_valid : Puddle.CTree.Pattern.Valid AMinusBMinusCMinusC_pattern := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_AMinusBMinusCMinusC_status :
    Status Unproven AMinusBMinusCMinusC_pattern :=
  .proven (combine_AMinusBMinusCMinusC_valid )

@[combine_valid, proof_pbv]
theorem combine_AMinusBPlusCMinusA_valid : Puddle.CTree.Pattern.Valid AMinusBPlusCMinusA_pattern := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_AMinusBPlusCMinusA_status :
    Status Unproven AMinusBPlusCMinusA_pattern :=
  .proven (combine_AMinusBPlusCMinusA_valid )

@[combine_valid, proof_pbv]
theorem combine_AMinusBPlusBMinusC_valid : Puddle.CTree.Pattern.Valid AMinusBPlusBMinusC_pattern := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_AMinusBPlusBMinusC_status :
    Status Unproven AMinusBPlusBMinusC_pattern :=
  .proven (combine_AMinusBPlusBMinusC_valid )

@[combine_valid, proof_pbv]
theorem combine_AMinusBMinusA_valid : Puddle.CTree.Pattern.Valid AMinusBMinusA_pattern := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_AMinusBMinusA_status :
    Status Unproven AMinusBMinusA_pattern :=
  .proven (combine_AMinusBMinusA_valid )

@[combine_valid, proof_pbv]
theorem combine_APlusBMinusAPlusC_valid : Puddle.CTree.Pattern.Valid (APlusBMinusAPlusC_pattern true) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_APlusBMinusAPlusC_status :
    Status Unproven (APlusBMinusAPlusC_pattern true) :=
  .proven (combine_APlusBMinusAPlusC_valid )

@[combine_valid, proof_pbv]
theorem combine_APlusBMinusCPlusA_valid : Puddle.CTree.Pattern.Valid (APlusBMinusAPlusC_pattern false) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_APlusBMinusCPlusA_status :
    Status Unproven (APlusBMinusAPlusC_pattern false) :=
  .proven (combine_APlusBMinusCPlusA_valid )

@[combine_valid, proof_pbv]
theorem combine_select_same_val_valid : Puddle.CTree.Pattern.Valid select_same_val_pattern := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_same_val_status :
    Status Unproven select_same_val_pattern :=
  .proven (combine_select_same_val_valid )

@[combine_valid, proof_pbv]
theorem combine_select_ugt_umax_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .ugt .g_umax) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_ugt_umax_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .ugt .g_umax) :=
  .proven (combine_select_ugt_umax_valid info )

@[combine_valid, proof_pbv]
theorem combine_select_uge_umax_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .uge .g_umax) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_uge_umax_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .uge .g_umax) :=
  .proven (combine_select_uge_umax_valid info )

@[combine_valid, proof_pbv]
theorem combine_select_sgt_smax_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .sgt .g_smax) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_sgt_smax_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .sgt .g_smax) :=
  .proven (combine_select_sgt_smax_valid info )

@[combine_valid, proof_pbv]
theorem combine_select_sge_smax_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .sge .g_smax) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_sge_smax_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .sge .g_smax) :=
  .proven (combine_select_sge_smax_valid info )

@[combine_valid, proof_pbv]
theorem combine_select_ult_umin_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .ult .g_umin) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_ult_umin_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .ult .g_umin) :=
  .proven (combine_select_ult_umin_valid info )

@[combine_valid, proof_pbv]
theorem combine_select_ule_umin_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .ule .g_umin) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_ule_umin_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .ule .g_umin) :=
  .proven (combine_select_ule_umin_valid info )

@[combine_valid, proof_pbv]
theorem combine_select_slt_smin_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .slt .g_smin) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_slt_smin_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .slt .g_smin) :=
  .proven (combine_select_slt_smin_valid info )

@[combine_valid, proof_pbv]
theorem combine_select_sle_smin_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .sle .g_smin) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_sle_smin_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .sle .g_smin) :=
  .proven (combine_select_sle_smin_valid info )

@[combine_valid, proof_pbv]
theorem combine_zext_of_select_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_of_cast_pattern info .g_zext) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_zext_of_select_status (info : LegalizerInfo) :
    Status Unproven (select_of_cast_pattern info .g_zext) :=
  .proven (combine_zext_of_select_valid info )

@[combine_valid, proof_pbv]
theorem combine_trunc_of_select_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_of_cast_pattern info .g_trunc) := by
  proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_trunc_of_select_status (info : LegalizerInfo) :
    Status Unproven (select_of_cast_pattern info .g_trunc) :=
  .proven (combine_trunc_of_select_valid info )

@[combine_valid, proof_pbv]
theorem combine_select_into_sub_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_sub false) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_sub_status :
    Status Unproven (select_into_binop_pattern .g_sub false) :=
  .proven (combine_select_into_sub_valid )

@[combine_valid, proof_pbv]
theorem combine_select_into_sub_swapped_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_sub true) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_sub_swapped_status :
    Status Unproven (select_into_binop_pattern .g_sub true) :=
  .proven (combine_select_into_sub_swapped_valid )

@[combine_valid, proof_pbv]
theorem combine_select_into_add_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_add false) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_add_status :
    Status Unproven (select_into_binop_pattern .g_add false) :=
  .proven (combine_select_into_add_valid )

@[combine_valid, proof_pbv]
theorem combine_select_into_add_swapped_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_add true) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_add_swapped_status :
    Status Unproven (select_into_binop_pattern .g_add true) :=
  .proven (combine_select_into_add_swapped_valid )

@[combine_valid, proof_pbv]
theorem combine_select_into_or_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_or false) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_or_status :
    Status Unproven (select_into_binop_pattern .g_or false) :=
  .proven (combine_select_into_or_valid )

@[combine_valid, proof_pbv]
theorem combine_select_into_or_swapped_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_or true) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_or_swapped_status :
    Status Unproven (select_into_binop_pattern .g_or true) :=
  .proven (combine_select_into_or_swapped_valid )

@[combine_valid, proof_pbv]
theorem combine_select_into_xor_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_xor false) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_xor_status :
    Status Unproven (select_into_binop_pattern .g_xor false) :=
  .proven (combine_select_into_xor_valid )

@[combine_valid, proof_pbv]
theorem combine_select_into_xor_swapped_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_xor true) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_xor_swapped_status :
    Status Unproven (select_into_binop_pattern .g_xor true) :=
  .proven (combine_select_into_xor_swapped_valid )

-- the `icmp` predicate is abstracted (with `maxHeartbeats 0`; at the default it times out first)
-- theorem combine_redundant_and_select_icmp_icmp_valid :
--     Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .icmp .icmp) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the `icmp` predicate is abstracted
-- theorem combine_redundant_and_valid : Puddle.CTree.Pattern.Valid redundant_and_pattern := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[combine_valid, proof_pbv]
theorem combine_funnel_shift_fshr_or_lshr_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_or_shift_pattern .g_fshr .g_lshr false true) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_funnel_shift_fshr_or_lshr_status :
    Status Unproven (funnel_shift_or_shift_pattern .g_fshr .g_lshr false true) :=
  .proven combine_funnel_shift_fshr_or_lshr_valid

@[combine_valid, proof_pbv]
theorem combine_funnel_shift_lshr_or_fshr_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_or_shift_pattern .g_fshr .g_lshr false false) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_funnel_shift_lshr_or_fshr_status :
    Status Unproven (funnel_shift_or_shift_pattern .g_fshr .g_lshr false false) :=
  .proven combine_funnel_shift_lshr_or_fshr_valid

end Veir.Legalization.CTreeProofs.PBV

/-!
# CTree validity of the gMIR combines that match constants (`Validity/CombineConstant`) by `pbv_decide`

Each rule is proven by `proveLegalValid with veir_pbv_decide` alone, without `sorry`: the matchers
bound every integer width by 64, which discharges the side goals `w ≤ 64` of `pbv_decide`. The rules `veir_pbv_decide` does not prove are commented out, with the reason it
fails.
-/
namespace Veir.Legalization.CTreeProofs.PBV

open Puddle
open Puddle.CTree
open _root_.CTree

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  GMIR.interpretOp' GMIR.interpretOpCTree GMIR_RISCV.interpretOp'

attribute [local simp] GMIR.isTerminator GMIR.getEffects GMIR_RISCV.base

attribute [local implicit_reducible] TypeAttr

@[combine_valid, proof_pbv]
theorem combine_right_identity_zero_sub_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_sub) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_right_identity_zero_sub_status :
    Status Unproven (right_identity_zero_pattern .g_sub) :=
  .proven (combine_right_identity_zero_sub_valid)

@[combine_valid, proof_pbv]
theorem combine_right_identity_zero_add_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_add) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_right_identity_zero_add_status :
    Status Unproven (right_identity_zero_pattern .g_add) :=
  .proven (combine_right_identity_zero_add_valid)

@[combine_valid, proof_pbv]
theorem combine_right_identity_zero_or_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_or) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_right_identity_zero_or_status :
    Status Unproven (right_identity_zero_pattern .g_or) :=
  .proven (combine_right_identity_zero_or_valid)

@[combine_valid, proof_pbv]
theorem combine_right_identity_zero_xor_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_xor) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_right_identity_zero_xor_status :
    Status Unproven (right_identity_zero_pattern .g_xor) :=
  .proven (combine_right_identity_zero_xor_valid)

@[combine_valid, proof_pbv]
theorem combine_right_identity_zero_shl_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_shl) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_right_identity_zero_shl_status :
    Status Unproven (right_identity_zero_pattern .g_shl) :=
  .proven (combine_right_identity_zero_shl_valid)

@[combine_valid, proof_pbv]
theorem combine_right_identity_zero_ashr_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_ashr) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_right_identity_zero_ashr_status :
    Status Unproven (right_identity_zero_pattern .g_ashr) :=
  .proven (combine_right_identity_zero_ashr_valid)

@[combine_valid, proof_pbv]
theorem combine_right_identity_zero_lshr_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_lshr) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_right_identity_zero_lshr_status :
    Status Unproven (right_identity_zero_pattern .g_lshr) :=
  .proven (combine_right_identity_zero_lshr_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_right_identity_one_int_valid :
--     Puddle.CTree.Pattern.Valid (right_identity_one_int_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[combine_valid, proof_pbv]
theorem combine_binop_right_to_zero_valid :
    Puddle.CTree.Pattern.Valid (binop_right_to_zero_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_binop_right_to_zero_status :
    Status Unproven (binop_right_to_zero_pattern) :=
  .proven (combine_binop_right_to_zero_valid)

@[combine_valid, proof_pbv]
theorem combine_binop_left_to_zero_shl_valid :
    Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_shl) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_binop_left_to_zero_shl_status :
    Status Unproven (binop_left_to_zero_pattern .g_shl) :=
  .proven (combine_binop_left_to_zero_shl_valid)

@[combine_valid, proof_pbv]
theorem combine_binop_left_to_zero_lshr_valid :
    Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_lshr) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_binop_left_to_zero_lshr_status :
    Status Unproven (binop_left_to_zero_pattern .g_lshr) :=
  .proven (combine_binop_left_to_zero_lshr_valid)

@[combine_valid, proof_pbv]
theorem combine_binop_left_to_zero_ashr_valid :
    Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_ashr) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_binop_left_to_zero_ashr_status :
    Status Unproven (binop_left_to_zero_pattern .g_ashr) :=
  .proven (combine_binop_left_to_zero_ashr_valid)

@[combine_valid, proof_pbv]
theorem combine_binop_left_to_zero_mul_valid :
    Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_mul) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_binop_left_to_zero_mul_status :
    Status Unproven (binop_left_to_zero_pattern .g_mul) :=
  .proven (combine_binop_left_to_zero_mul_valid)

@[combine_valid, proof_pbv]
theorem combine_sub_minus_one_valid :
    Puddle.CTree.Pattern.Valid (sub_minus_one_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_sub_minus_one_status :
    Status Unproven (sub_minus_one_pattern) :=
  .proven (combine_sub_minus_one_valid)

@[combine_valid, proof_pbv]
theorem combine_ZeroMinusAPlusB_valid :
    Puddle.CTree.Pattern.Valid (ZeroMinusAPlusB_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_ZeroMinusAPlusB_status :
    Status Unproven (ZeroMinusAPlusB_pattern) :=
  .proven (combine_ZeroMinusAPlusB_valid)

@[combine_valid, proof_pbv]
theorem combine_APlusZeroMinusB_valid :
    Puddle.CTree.Pattern.Valid (APlusZeroMinusB_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_APlusZeroMinusB_status :
    Status Unproven (APlusZeroMinusB_pattern) :=
  .proven (combine_APlusZeroMinusB_valid)

@[combine_valid, proof_pbv]
theorem combine_AMinusZeroMinusB_valid :
    Puddle.CTree.Pattern.Valid (AMinusZeroMinusB_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_AMinusZeroMinusB_status :
    Status Unproven (AMinusZeroMinusB_pattern) :=
  .proven (combine_AMinusZeroMinusB_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sub_one_from_sub_valid :
--     Puddle.CTree.Pattern.Valid (sub_one_from_sub_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[combine_valid, proof_pbv]
theorem combine_APlusC1MinusC2_valid :
    Puddle.CTree.Pattern.Valid (APlusC1MinusC2_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_APlusC1MinusC2_status :
    Status Unproven (APlusC1MinusC2_pattern) :=
  .proven (combine_APlusC1MinusC2_valid)

@[combine_valid, proof_pbv]
theorem combine_C2MinusAPlusC1_valid :
    Puddle.CTree.Pattern.Valid (C2MinusAPlusC1_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_C2MinusAPlusC1_status :
    Status Unproven (C2MinusAPlusC1_pattern) :=
  .proven (combine_C2MinusAPlusC1_valid)

@[combine_valid, proof_pbv]
theorem combine_AMinusC1MinusC2_valid :
    Puddle.CTree.Pattern.Valid (AMinusC1MinusC2_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_AMinusC1MinusC2_status :
    Status Unproven (AMinusC1MinusC2_pattern) :=
  .proven (combine_AMinusC1MinusC2_valid)

@[combine_valid, proof_pbv]
theorem combine_C1MinusAMinusC2_valid :
    Puddle.CTree.Pattern.Valid (C1MinusAMinusC2_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_C1MinusAMinusC2_status :
    Status Unproven (C1MinusAMinusC2_pattern) :=
  .proven (combine_C1MinusAMinusC2_valid)

@[combine_valid, proof_pbv]
theorem combine_AMinusC1PlusC2_valid :
    Puddle.CTree.Pattern.Valid (AMinusC1PlusC2_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_AMinusC1PlusC2_status :
    Status Unproven (AMinusC1PlusC2_pattern) :=
  .proven (combine_AMinusC1PlusC2_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sub_of_mul_const_valid :
--     Puddle.CTree.Pattern.Valid (sub_of_mul_const_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_mul_by_neg_one_valid :
--     Puddle.CTree.Pattern.Valid (mul_by_neg_one_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_mulo_by_2_valid :
--     Puddle.CTree.Pattern.Valid (mulo_by_2_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[combine_valid, proof_pbv]
theorem combine_NotAPlusNegOne_valid :
    Puddle.CTree.Pattern.Valid (NotAPlusNegOne_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_NotAPlusNegOne_status :
    Status Unproven (NotAPlusNegOne_pattern) :=
  .proven (combine_NotAPlusNegOne_valid)

@[combine_valid, proof_pbv]
theorem combine_add_shift_valid :
    Puddle.CTree.Pattern.Valid (add_shift_pattern false) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_add_shift_status :
    Status Unproven (add_shift_pattern false) :=
  .proven (combine_add_shift_valid)

@[combine_valid, proof_pbv]
theorem combine_add_shift_swapped_valid :
    Puddle.CTree.Pattern.Valid (add_shift_pattern true) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_add_shift_swapped_status :
    Status Unproven (add_shift_pattern true) :=
  .proven (combine_add_shift_swapped_valid)

@[combine_valid, proof_pbv]
theorem combine_or_and_xor_to_or_or_and_valid :
    Puddle.CTree.Pattern.Valid (or_and_xor_to_or_pattern .g_or .g_and) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_or_and_xor_to_or_or_and_status :
    Status Unproven (or_and_xor_to_or_pattern .g_or .g_and) :=
  .proven (combine_or_and_xor_to_or_or_and_valid)

@[combine_valid, proof_pbv]
theorem combine_or_and_xor_to_or_and_or_valid :
    Puddle.CTree.Pattern.Valid (or_and_xor_to_or_pattern .g_and .g_or) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_or_and_xor_to_or_and_or_status :
    Status Unproven (or_and_xor_to_or_pattern .g_and .g_or) :=
  .proven (combine_or_and_xor_to_or_and_or_valid)

@[combine_valid, proof_pbv]
theorem combine_or_and_xor_to_xor_or_or_and_valid :
    Puddle.CTree.Pattern.Valid (or_and_xor_to_xor_or_pattern .g_or .g_and) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_or_and_xor_to_xor_or_or_and_status :
    Status Unproven (or_and_xor_to_xor_or_pattern .g_or .g_and) :=
  .proven (combine_or_and_xor_to_xor_or_or_and_valid)

@[combine_valid, proof_pbv]
theorem combine_or_and_xor_to_xor_or_and_or_valid :
    Puddle.CTree.Pattern.Valid (or_and_xor_to_xor_or_pattern .g_and .g_or) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_or_and_xor_to_xor_or_and_or_status :
    Status Unproven (or_and_xor_to_xor_or_pattern .g_and .g_or) :=
  .proven (combine_or_and_xor_to_xor_or_and_or_valid)

@[combine_valid, proof_pbv]
theorem combine_simplify_neg_smax_valid :
    Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_smax .g_smin) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_simplify_neg_smax_status :
    Status Unproven (simplify_neg_minmax_pattern .g_smax .g_smin) :=
  .proven (combine_simplify_neg_smax_valid)

@[combine_valid, proof_pbv]
theorem combine_simplify_neg_umax_valid :
    Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_umax .g_umin) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_simplify_neg_umax_status :
    Status Unproven (simplify_neg_minmax_pattern .g_umax .g_umin) :=
  .proven (combine_simplify_neg_umax_valid)

@[combine_valid, proof_pbv]
theorem combine_simplify_neg_smin_valid :
    Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_smin .g_smax) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_simplify_neg_smin_status :
    Status Unproven (simplify_neg_minmax_pattern .g_smin .g_smax) :=
  .proven (combine_simplify_neg_smin_valid)

@[combine_valid, proof_pbv]
theorem combine_simplify_neg_umin_valid :
    Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_umin .g_umax) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_simplify_neg_umin_status :
    Status Unproven (simplify_neg_minmax_pattern .g_umin .g_umax) :=
  .proven (combine_simplify_neg_umin_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_eq_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .eq .ne) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_ne_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ne .eq) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_ugt_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ugt .ule) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_uge_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .uge .ult) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_ult_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ult .uge) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_ule_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ule .ugt) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_sgt_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sgt .sle) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_sge_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sge .slt) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_slt_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .slt .sge) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_sle_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sle .sgt) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[combine_valid, proof_pbv]
theorem combine_double_icmp_zero_and_valid :
    Puddle.CTree.Pattern.Valid (double_icmp_zero_pattern .g_and .eq) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_double_icmp_zero_and_status :
    Status Unproven (double_icmp_zero_pattern .g_and .eq) :=
  .proven (combine_double_icmp_zero_and_valid)

@[combine_valid, proof_pbv]
theorem combine_double_icmp_zero_or_valid :
    Puddle.CTree.Pattern.Valid (double_icmp_zero_pattern .g_or .ne) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_double_icmp_zero_or_status :
    Status Unproven (double_icmp_zero_pattern .g_or .ne) :=
  .proven (combine_double_icmp_zero_or_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_udiv_by_pow2_valid :
--     Puddle.CTree.Pattern.Valid (udiv_by_pow2_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sdiv_exact_by_pow2_pos_valid :
--     Puddle.CTree.Pattern.Valid (sdiv_exact_by_pow2_pattern false) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sdiv_exact_by_pow2_neg_valid :
--     Puddle.CTree.Pattern.Valid (sdiv_exact_by_pow2_pattern true) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sdiv_by_pow2_pos_valid :
--     Puddle.CTree.Pattern.Valid (sdiv_by_pow2_pattern false) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sdiv_by_pow2_neg_valid :
--     Puddle.CTree.Pattern.Valid (sdiv_by_pow2_pattern true) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_mul_to_shl_valid :
--     Puddle.CTree.Pattern.Valid (mul_to_shl_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_urem_pow2_to_mask_valid :
--     Puddle.CTree.Pattern.Valid (urem_pow2_to_mask_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[combine_valid, proof_pbv]
theorem combine_constant_fold_add_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_add (fun a b => a + b)) := by
  proveLegalValid with (normalizeConstants; veir_pbv_decide 64 (bv_decide := false); bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_constant_fold_add_status :
    Status Unproven (constant_fold_binop_pattern .g_add (fun a b => a + b)) :=
  .proven (combine_constant_fold_add_valid)

@[combine_valid, proof_pbv]
theorem combine_constant_fold_sub_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_sub ((· - ·))) := by
  proveLegalValid with (normalizeConstants; veir_pbv_decide 64 (bv_decide := false); bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_constant_fold_sub_status :
    Status Unproven (constant_fold_binop_pattern .g_sub ((· - ·))) :=
  .proven (combine_constant_fold_sub_valid)

@[combine_valid, proof_pbv]
theorem combine_constant_fold_smin_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_smin (min)) := by
  proveLegalValid with (normalizeConstants; veir_pbv_decide 64 (bv_decide := false); bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_constant_fold_smin_status :
    Status Unproven (constant_fold_binop_pattern .g_smin (min)) :=
  .proven (combine_constant_fold_smin_valid)

@[combine_valid, proof_pbv]
theorem combine_constant_fold_smax_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_smax (max)) := by
  proveLegalValid with (normalizeConstants; veir_pbv_decide 64 (bv_decide := false); bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_constant_fold_smax_status :
    Status Unproven (constant_fold_binop_pattern .g_smax (max)) :=
  .proven (combine_constant_fold_smax_valid)

@[combine_valid, proof_pbv]
theorem combine_select_constant_cmp_nonzero_valid :
    Puddle.CTree.Pattern.Valid (select_constant_cmp_pattern true) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_constant_cmp_nonzero_status :
    Status Unproven (select_constant_cmp_pattern true) :=
  .proven (combine_select_constant_cmp_nonzero_valid)

@[combine_valid, proof_pbv]
theorem combine_select_constant_cmp_zero_valid :
    Puddle.CTree.Pattern.Valid (select_constant_cmp_pattern false) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_constant_cmp_zero_status :
    Status Unproven (select_constant_cmp_pattern false) :=
  .proven (combine_select_constant_cmp_zero_valid)

@[combine_valid, proof_pbv]
theorem combine_sub_to_add_valid (info : LegalizerInfo) :
    Puddle.CTree.Pattern.Valid (sub_to_add_pattern info) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_sub_to_add_status (info : LegalizerInfo) :
    Status Unproven (sub_to_add_pattern info) :=
  .proven (combine_sub_to_add_valid info)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_redundant_and_select_icmp_constant_valid :
--     Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .icmp .constant) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_redundant_and_select_constant_icmp_valid :
--     Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .constant .icmp) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_redundant_and_select_constant_constant_valid :
--     Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .constant .constant) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[combine_valid, proof_pbv]
theorem combine_select_into_shl_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_shl false) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_shl_status :
    Status Unproven (select_into_binop_pattern .g_shl false) :=
  .proven (combine_select_into_shl_valid)

@[combine_valid, proof_pbv]
theorem combine_select_into_shl_swapped_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_shl true) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_shl_swapped_status :
    Status Unproven (select_into_binop_pattern .g_shl true) :=
  .proven (combine_select_into_shl_swapped_valid)

@[combine_valid, proof_pbv]
theorem combine_select_into_lshr_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_lshr false) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_lshr_status :
    Status Unproven (select_into_binop_pattern .g_lshr false) :=
  .proven (combine_select_into_lshr_valid)

@[combine_valid, proof_pbv]
theorem combine_select_into_lshr_swapped_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_lshr true) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_lshr_swapped_status :
    Status Unproven (select_into_binop_pattern .g_lshr true) :=
  .proven (combine_select_into_lshr_swapped_valid)

@[combine_valid, proof_pbv]
theorem combine_select_into_ashr_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_ashr false) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_ashr_status :
    Status Unproven (select_into_binop_pattern .g_ashr false) :=
  .proven (combine_select_into_ashr_valid)

@[combine_valid, proof_pbv]
theorem combine_select_into_ashr_swapped_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_ashr true) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_ashr_swapped_status :
    Status Unproven (select_into_binop_pattern .g_ashr true) :=
  .proven (combine_select_into_ashr_swapped_valid)

@[combine_valid, proof_pbv]
theorem combine_select_one_zero_valid :
    Puddle.CTree.Pattern.Valid (select_one_zero_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_one_zero_status :
    Status Unproven (select_one_zero_pattern) :=
  .proven (combine_select_one_zero_valid)

@[combine_valid, proof_pbv]
theorem combine_select_allOnes_zero_valid :
    Puddle.CTree.Pattern.Valid (select_allOnes_zero_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_allOnes_zero_status :
    Status Unproven (select_allOnes_zero_pattern) :=
  .proven (combine_select_allOnes_zero_valid)

@[combine_valid, proof_pbv]
theorem combine_select_zero_one_valid :
    Puddle.CTree.Pattern.Valid (select_zero_one_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_zero_one_status :
    Status Unproven (select_zero_one_pattern) :=
  .proven (combine_select_zero_one_valid)

@[combine_valid, proof_pbv]
theorem combine_select_zero_allOnes_valid :
    Puddle.CTree.Pattern.Valid (select_zero_allOnes_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_zero_allOnes_status :
    Status Unproven (select_zero_allOnes_pattern) :=
  .proven (combine_select_zero_allOnes_valid)

@[combine_valid, proof_pbv]
theorem combine_select_succ_valid :
    Puddle.CTree.Pattern.Valid (select_succ_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_succ_status :
    Status Unproven (select_succ_pattern) :=
  .proven (combine_select_succ_valid)

@[combine_valid, proof_pbv]
theorem combine_select_pred_valid :
    Puddle.CTree.Pattern.Valid (select_pred_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_pred_status :
    Status Unproven (select_pred_pattern) :=
  .proven (combine_select_pred_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_select_pow2_zero_valid :
--     Puddle.CTree.Pattern.Valid (select_pow2_zero_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_select_zero_pow2_valid :
--     Puddle.CTree.Pattern.Valid (select_zero_pow2_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[combine_valid, proof_pbv]
theorem combine_select_allOnes_const_valid :
    Puddle.CTree.Pattern.Valid (select_allOnes_const_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_allOnes_const_status :
    Status Unproven (select_allOnes_const_pattern) :=
  .proven (combine_select_allOnes_const_valid)

@[combine_valid, proof_pbv]
theorem combine_select_const_allOnes_valid :
    Puddle.CTree.Pattern.Valid (select_const_allOnes_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_const_allOnes_status :
    Status Unproven (select_const_allOnes_pattern) :=
  .proven (combine_select_const_allOnes_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_funnel_shift_right_zero_valid :
--     Puddle.CTree.Pattern.Valid (funnel_shift_zero_pattern .g_fshr true) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_funnel_shift_left_zero_valid :
--     Puddle.CTree.Pattern.Valid (funnel_shift_zero_pattern .g_fshl false) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- spurious counterexample: the overshift amount's hypotheses are abstracted
-- theorem combine_funnel_shift_overshift_l_valid :
--     Puddle.CTree.Pattern.Valid (funnel_shift_overshift_pattern .g_fshl) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- spurious counterexample: the overshift amount's hypotheses are abstracted
-- theorem combine_funnel_shift_overshift_r_valid :
--     Puddle.CTree.Pattern.Valid (funnel_shift_overshift_pattern .g_fshr) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

end Veir.Legalization.CTreeProofs.PBV
