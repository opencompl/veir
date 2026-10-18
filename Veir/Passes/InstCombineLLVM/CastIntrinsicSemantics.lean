module

public import Veir.Passes.InstCombineLLVM.Semantics
public import Veir.Data.PBV.Mask
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Byte.Lemmas
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.Refinement

namespace Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics

open Veir Veir.Data Veir.Puddle
open Veir.Data.PBV

public theorem shl_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .shl : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .shl) props #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.shl x y props.nsw props.nuw) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', ne_eq, not_true_eq_false, ↓reduceDIte, LLVM.Int.cast_self,
    Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
    List.cons.injEq, and_true, TypeAttr.of_val]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public theorem zext_flag_refines {w₁ w₂ : Nat} (h : w₁ < w₂) (x : LLVM.Int w₁)
    (nneg : Bool) : LLVM.Int.zext x w₂ nneg h ⊒ LLVM.Int.zext x w₂ false h := by
  cases x with
  | poison => simp [LLVM.Int.zext, Id.run]
  | val x =>
    cases nneg
    · exact isRefinedBy_refl _
    · by_cases hx : x.msb = true
      · simp only [LLVM.Int.zext, Id.run, hx]
        exact poison_isRefinedBy _
      · simp [LLVM.Int.zext, Id.run, hx]

private theorem lowmask_src_lt {m s n : Nat} (hms : m < s) (_hsn : s < n)
    (x : BitVec s) :
    (x.truncate m).zeroExtend n =
      (x &&& maskOfWidth s m).zeroExtend n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_and,
    toNat_maskOfWidth (Nat.le_of_lt hms)]
  rw [Nat.and_two_pow_sub_one_eq_mod]

private theorem lowmask_src_eq {m n : Nat} (hmn : m < n) (x : BitVec n) :
    (x.truncate m).zeroExtend n = x &&& maskOfWidth n m := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_and,
    toNat_maskOfWidth (Nat.le_of_lt hmn)]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have hpow : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_of_le (by omega) (Nat.le_of_lt hmn)
  have hxmod : x.toNat % 2 ^ m < 2 ^ n :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos m)) hpow
  exact Nat.mod_eq_of_lt hxmod

private theorem lowmask_src_gt {m n s : Nat} (hmn : m < n) (_hns : n < s)
    (x : BitVec s) :
    (x.truncate m).zeroExtend n =
      x.truncate n &&& maskOfWidth n m := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_and,
    toNat_maskOfWidth (Nat.le_of_lt hmn)]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have hdvd : 2 ^ m ∣ 2 ^ n := (Nat.pow_dvd_pow_iff_le_right' (b := 0)).mpr
    (Nat.le_of_lt hmn)
  rw [Nat.mod_mod_of_dvd _ hdvd]
  have hpow : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_of_le (by omega) (Nat.le_of_lt hmn)
  have hxmod : x.toNat % 2 ^ m < 2 ^ n :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos m)) hpow
  exact Nat.mod_eq_of_lt hxmod

public theorem zext_trunc_lowmask_src_lt {m s n : Nat} (hms : m < s) (hsn : s < n)
    (x : LLVM.Int s)
    (tnsw tnuw znneg : Bool) :
    LLVM.Int.zext (LLVM.Int.trunc x m tnsw tnuw hms) n znneg (by omega) ⊒
      LLVM.Int.zext (LLVM.Int.and x (.val (maskOfWidth s m))) n false hsn := by
  apply isRefinedBy_trans (zext_flag_refines (by omega) _ znneg)
  apply isRefinedBy_trans (LLVM.Int.zext_mono _ _ (by omega)
    (trunc_flags_refine s m hms x tnsw tnuw))
  cases x <;> simp [LLVM.Int.trunc, LLVM.Int.zext, LLVM.Int.and, Id.run,
    lowmask_src_lt hms hsn]

public theorem zext_trunc_lowmask_src_eq {m n : Nat} (hmn : m < n) (x : LLVM.Int n)
    (tnsw tnuw znneg : Bool) :
    LLVM.Int.zext (LLVM.Int.trunc x m tnsw tnuw hmn) n znneg hmn ⊒
      LLVM.Int.and x (.val (maskOfWidth n m)) := by
  apply isRefinedBy_trans (zext_flag_refines hmn _ znneg)
  apply isRefinedBy_trans (LLVM.Int.zext_mono _ _ hmn
    (trunc_flags_refine n m hmn x tnsw tnuw))
  cases x <;> simp [LLVM.Int.trunc, LLVM.Int.zext, LLVM.Int.and, Id.run,
    lowmask_src_eq hmn]

public theorem zext_trunc_lowmask_src_gt {m n s : Nat} (hmn : m < n) (hns : n < s)
    (x : LLVM.Int s)
    (tnsw tnuw znneg : Bool) :
    LLVM.Int.zext (LLVM.Int.trunc x m tnsw tnuw (by omega)) n znneg hmn ⊒
      LLVM.Int.and (LLVM.Int.trunc x n false false hns)
        (.val (maskOfWidth n m)) := by
  apply isRefinedBy_trans (zext_flag_refines hmn _ znneg)
  apply isRefinedBy_trans (LLVM.Int.zext_mono _ _ hmn
    (trunc_flags_refine s m (by omega) x tnsw tnuw))
  cases x <;> simp [LLVM.Int.trunc, LLVM.Int.zext, LLVM.Int.and, Id.run,
    lowmask_src_gt hmn hns]

private theorem narrow_and_zext {n w : Nat} (hnw : n < w) (x : BitVec w)
    (c : BitVec n) :
    (x.truncate n &&& c).zeroExtend w = x &&& c.zeroExtend w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_and]
  have hpow : 2 ^ n ≤ 2 ^ w := Nat.pow_le_pow_of_le (by omega) (Nat.le_of_lt hnw)
  have hcW : c.toNat < 2 ^ w := Nat.lt_of_lt_of_le c.isLt hpow
  rw [Nat.mod_eq_of_lt hcW]
  have hAnd : x.toNat &&& c.toNat < 2 ^ n :=
    Nat.lt_of_le_of_lt Nat.and_le_right c.isLt
  have hAndLeft : x.toNat % 2 ^ n &&& c.toNat < 2 ^ w :=
    Nat.lt_of_le_of_lt Nat.and_le_right hcW
  rw [Nat.mod_eq_of_lt hAndLeft]
  have heq := (Nat.and_mod_two_pow (a := x.toNat) (b := c.toNat) (n := n))
  rw [Nat.mod_eq_of_lt hAnd, Nat.mod_eq_of_lt c.isLt] at heq
  exact heq.symm

private theorem narrow_and_zext' {n w : Nat} (hnw : n < w) (x : BitVec w)
    (c : BitVec n) :
    BitVec.setWidth w (BitVec.setWidth n x) &&& BitVec.setWidth w c =
      x &&& BitVec.setWidth w c := by
  rw [← BitVec.setWidth_and]
  exact narrow_and_zext hnw x c

public theorem zext_and_trunc_mask {n w : Nat} (hnw : n < w) (x : LLVM.Int w)
    (c : LLVM.Int n)
    (tnsw tnuw znneg : Bool) :
    LLVM.Int.zext (LLVM.Int.and (LLVM.Int.trunc x n tnsw tnuw hnw) c)
      w znneg hnw ⊒
    LLVM.Int.and x (LLVM.Int.zext c w false hnw) := by
  apply isRefinedBy_trans (zext_flag_refines hnw _ znneg)
  apply isRefinedBy_trans (LLVM.Int.zext_mono _ _ hnw
    (LLVM.Int.and_mono _ _ _ _ (trunc_flags_refine w n hnw x tnsw tnuw)
      (isRefinedBy_refl c)))
  cases x with
  | poison => simp [LLVM.Int.trunc, LLVM.Int.zext, LLVM.Int.and, Id.run]
  | val x => cases c with
    | poison => simp [LLVM.Int.trunc, LLVM.Int.zext, LLVM.Int.and, Id.run]
    | val c =>
      simp [LLVM.Int.trunc, LLVM.Int.zext, LLVM.Int.and, Id.run]
      rw [narrow_and_zext' hnw]
      exact isRefinedBy_refl _

public theorem zext_xor_and_trunc_mask {n w : Nat} (hnw : n < w) (x : LLVM.Int w)
    (c : LLVM.Int n)
    (tnsw tnuw znneg : Bool) :
    LLVM.Int.zext (LLVM.Int.xor
      (LLVM.Int.and (LLVM.Int.trunc x n tnsw tnuw hnw) c) c)
      w znneg hnw ⊒
    LLVM.Int.xor (LLVM.Int.and x (LLVM.Int.zext c w false hnw))
      (LLVM.Int.zext c w false hnw) := by
  apply isRefinedBy_trans (zext_flag_refines hnw _ znneg)
  apply isRefinedBy_trans (LLVM.Int.zext_mono _ _ hnw
    (LLVM.Int.xor_mono _ _ _ _
      (LLVM.Int.and_mono _ _ _ _ (trunc_flags_refine w n hnw x tnsw tnuw)
        (isRefinedBy_refl c)) (isRefinedBy_refl c)))
  cases x with
  | poison => simp [LLVM.Int.trunc, LLVM.Int.zext, LLVM.Int.and, LLVM.Int.xor, Id.run]
  | val x => cases c with
    | poison => simp [LLVM.Int.trunc, LLVM.Int.zext, LLVM.Int.and, LLVM.Int.xor, Id.run]
    | val c =>
      simp [LLVM.Int.trunc, LLVM.Int.zext, LLVM.Int.and, LLVM.Int.xor, Id.run,
        BitVec.setWidth_xor]
      rw [narrow_and_zext' hnw]
      exact isRefinedBy_refl _

private theorem narrow_neg_zext {n w : Nat} (hnw : n < w) (x : BitVec w) :
    (-(x.truncate n)).zeroExtend w = (-x) &&& maskOfWidth w n := by
  simp only [BitVec.truncate_eq_setWidth]
  rw [← BitVec.setWidth_neg_of_le (x := x) (Nat.le_of_lt hnw)]
  exact setWidth_eq_and_maskOfWidth (Nat.le_of_lt hnw) (by simp)

public theorem zext_neg_trunc_lowmask {n w : Nat} (hnw : n < w) (x : LLVM.Int w)
    (tnsw tnuw snsw snuw znneg : Bool) :
    LLVM.Int.zext (LLVM.Int.sub (.val (BitVec.ofInt n 0))
      (LLVM.Int.trunc x n tnsw tnuw hnw) snsw snuw) w znneg hnw ⊒
    LLVM.Int.and (LLVM.Int.sub (.val (BitVec.ofInt w 0)) x)
      (.val (maskOfWidth w n)) := by
  apply isRefinedBy_trans (zext_flag_refines hnw _ znneg)
  apply isRefinedBy_trans (LLVM.Int.zext_mono _ _ hnw
    (isRefinedBy_trans (sub_flags_refine n _ _ snsw snuw)
      (sub_refine_mono n (isRefinedBy_refl _)
        (trunc_flags_refine w n hnw x tnsw tnuw))))
  cases x <;> simp [LLVM.Int.trunc, LLVM.Int.zext, LLVM.Int.sub, LLVM.Int.and,
    Id.run, narrow_neg_zext hnw]

public theorem lshr_exact_refine {w : Nat} (x y : LLVM.Int w) (exact : Bool) :
    LLVM.Int.lshr x y exact ⊒ LLVM.Int.lshr x y false := by
  cases x <;> cases y <;> simp [LLVM.Int.lshr, Id.run]
  split
  · exact poison_isRefinedBy _
  · cases exact
    · exact isRefinedBy_refl _
    · split
      · exact poison_isRefinedBy _
      · exact isRefinedBy_refl _

public theorem ashr_exact_refine {w : Nat} (x y : LLVM.Int w) (exact : Bool) :
    LLVM.Int.ashr x y exact ⊒ LLVM.Int.ashr x y false := by
  cases x <;> cases y <;> simp [LLVM.Int.ashr, Id.run]
  split
  · exact poison_isRefinedBy _
  · cases exact
    · exact isRefinedBy_refl _
    · split
      · exact poison_isRefinedBy _
      · exact isRefinedBy_refl _

private theorem bitvec_ashr_top {w : Nat} (hw : 0 < w) (x : BitVec w) :
    x.sshiftRight (w - 1) = if x.msb then BitVec.allOnes w else 0 := by
  apply BitVec.eq_of_toNat_eq
  by_cases hmsb : x.msb = true
  · rw [ite_eq_left hmsb, BitVec.toNat_allOnes,
      BitVec.toNat_sshiftRight_of_msb_true hmsb]
    have hle := BitVec.le_toNat_of_msb_true hmsb
    have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by
      calc
        2 ^ w = 2 ^ ((w - 1) + 1) := by congr 1 <;> omega
        _ = 2 * 2 ^ (w - 1) := by rw [Nat.pow_add_one]; omega
    have hsmall : 2 ^ w - 1 - x.toNat < 2 ^ (w - 1) := by omega
    rw [Nat.shiftRight_eq_zero _ _ hsmall]
    omega
  · rw [Bool.not_eq_true] at hmsb
    have hfalse : x.msb = false := hmsb
    rw [ite_eq_right (by simpa using hmsb), show (0 : BitVec w).toNat = 0 by simp,
      BitVec.toNat_sshiftRight_of_msb_false hfalse]
    exact Nat.shiftRight_eq_zero _ _ (BitVec.toNat_lt_of_msb_false hfalse)

private theorem bitvec_lshr_top {w : Nat} (hw : 0 < w) (x : BitVec w) :
    x >>> (w - 1) = if x.msb then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  by_cases hmsb : x.msb = true
  · rw [ite_eq_left hmsb, show (1 : BitVec w).toNat = 1 by simp [hw],
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    apply Nat.div_eq_of_lt_le
    · simpa using BitVec.le_toNat_of_msb_true hmsb
    · have hx := x.isLt
      have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by
        calc
          2 ^ w = 2 ^ ((w - 1) + 1) := by congr 1 <;> omega
          _ = 2 * 2 ^ (w - 1) := by rw [Nat.pow_add_one]; omega
      rw [hpow] at hx
      simpa [Nat.mul_comm] using hx
  · rw [Bool.not_eq_true] at hmsb
    have hfalse : x.msb = false := hmsb
    rw [ite_eq_right (by simpa using hmsb), show (0 : BitVec w).toNat = 0 by simp,
      BitVec.toNat_ushiftRight]
    exact Nat.shiftRight_eq_zero _ _ (BitVec.toNat_lt_of_msb_false hfalse)

private theorem top_shift_amount_toNat {w : Nat} (hw : 0 < w) :
    (BitVec.ofInt w (Int.ofNat (w - 1))).toNat = w - 1 := by
  change (BitVec.ofNat w (w - 1)).toNat = w - 1
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.sub_le w 1)
    (Nat.lt_pow_self (a := 2) (by decide))

private theorem trunc_lshr_top_bit {w : Nat} (hw : 0 < w) (x : BitVec w) :
    (x >>> (w - 1)).truncate 1 = BitVec.ofBool (x.slt (0 : BitVec w)) := by
  rw [bitvec_lshr_top hw]
  rw [show x.slt (0 : BitVec w) = x.msb by exact BitVec.slt_zero_eq_msb]
  cases h : x.msb
  · simp [h]
  · simp only [h, ↓reduceIte, BitVec.ofBool_true]
    exact BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt hw

private theorem trunc_ashr_top_bit {w : Nat} (hw : 0 < w) (x : BitVec w) :
    (x.sshiftRight (w - 1)).truncate 1 = BitVec.ofBool (x.slt (0 : BitVec w)) := by
  rw [bitvec_ashr_top hw]
  rw [show x.slt (0 : BitVec w) = x.msb by exact BitVec.slt_zero_eq_msb]
  cases h : x.msb
  · simp [h]
  · simp only [h, ↓reduceIte, BitVec.ofBool_true]
    apply BitVec.eq_of_toNat_eq
    simp [hw]

public theorem trunc_lshr_top_refines_icmp_slt {w : Nat} (h : 1 < w)
    (x : LLVM.Int w) (exact nsw nuw : Bool) :
    LLVM.Int.trunc (LLVM.Int.lshr x
      (.val (BitVec.ofInt w (Int.ofNat (w - 1)))) exact) 1 nsw nuw h ⊒
      LLVM.Int.icmp x (.val (BitVec.ofInt w 0)) .slt := by
  apply isRefinedBy_trans (trunc_flags_refine w 1 h _ nsw nuw)
  apply isRefinedBy_trans (LLVM.Int.trunc_mono _ _ h
    (lshr_exact_refine x (.val (BitVec.ofInt w (Int.ofNat (w - 1)))) exact))
  cases x with
  | poison => simp [LLVM.Int.trunc, LLVM.Int.lshr, LLVM.Int.icmp, Id.run]
  | val x =>
    have hlt : ¬w ≤ w - 1 := by omega
    have hmod : (w - 1) % 2 ^ w = w - 1 := Nat.mod_eq_of_lt
      (Nat.lt_of_le_of_lt (Nat.sub_le w 1)
        (Nat.lt_pow_self (a := 2) (by decide)))
    simp [LLVM.Int.trunc, LLVM.Int.lshr, LLVM.Int.icmp, LLVM.IntPred.eval,
      Id.run, BitVec.le_def, BitVec.ushiftRight_eq', hmod, hlt]
    rw [← BitVec.truncate_eq_setWidth, trunc_lshr_top_bit (by omega)]
    exact isRefinedBy_refl _

public theorem trunc_ashr_top_refines_icmp_slt {w : Nat} (h : 1 < w)
    (x : LLVM.Int w) (exact nsw nuw : Bool) :
    LLVM.Int.trunc (LLVM.Int.ashr x
      (.val (BitVec.ofInt w (Int.ofNat (w - 1)))) exact) 1 nsw nuw h ⊒
      LLVM.Int.icmp x (.val (BitVec.ofInt w 0)) .slt := by
  apply isRefinedBy_trans (trunc_flags_refine w 1 h _ nsw nuw)
  apply isRefinedBy_trans (LLVM.Int.trunc_mono _ _ h
    (ashr_exact_refine x (.val (BitVec.ofInt w (Int.ofNat (w - 1)))) exact))
  cases x with
  | poison => simp [LLVM.Int.trunc, LLVM.Int.ashr, LLVM.Int.icmp, Id.run]
  | val x =>
    have hlt : ¬w ≤ w - 1 := by omega
    have hmod : (w - 1) % 2 ^ w = w - 1 := Nat.mod_eq_of_lt
      (Nat.lt_of_le_of_lt (Nat.sub_le w 1)
        (Nat.lt_pow_self (a := 2) (by decide)))
    simp [LLVM.Int.trunc, LLVM.Int.ashr, LLVM.Int.icmp, LLVM.IntPred.eval,
      Id.run, BitVec.le_def, BitVec.sshiftRight_eq', hmod, hlt]
    rw [← BitVec.truncate_eq_setWidth, trunc_ashr_top_bit (by omega)]
    exact isRefinedBy_refl _

private theorem trunc_lshr_bit_eq {w c : Nat} (hc : c < w) (x : BitVec w) :
    (x >>> c).truncate 1 =
      BitVec.ofBool ((x &&& (1#w <<< c)) != (0 : BitVec w)) := by
  rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_one, BitVec.getLsbD_ushiftRight]
  simp only [Nat.add_zero]
  rw [show (1#w <<< c) = BitVec.twoPow w c by rfl, BitVec.and_twoPow]
  have hn : BitVec.twoPow w c ≠ 0#w := by
    intro hz
    have hzNat := congrArg BitVec.toNat hz
    simp [BitVec.toNat_twoPow_of_lt hc] at hzNat
  cases h : x.getLsbD c
  · simp [h]
  · simp only [h, ↓reduceIte]
    have hb : (BitVec.twoPow w c != (0 : BitVec w)) = true := bne_iff_ne.mpr hn
    change BitVec.ofBool true = BitVec.ofBool (BitVec.twoPow w c != (0 : BitVec w))
    rw [hb]

public theorem trunc_lshr_refines_bit_test {w : Nat} (h : 1 < w)
    (x : LLVM.Int w) (c : BitVec w) (exact nsw nuw : Bool) :
    LLVM.Int.trunc (LLVM.Int.lshr x (.val c) exact) 1 nsw nuw h ⊒
      LLVM.Int.icmp
        (LLVM.Int.and x (LLVM.Int.shl (.val (1 : BitVec w)) (.val c) false false))
        (.val (0 : BitVec w)) .ne := by
  apply isRefinedBy_trans (trunc_flags_refine w 1 h _ nsw nuw)
  apply isRefinedBy_trans (LLVM.Int.trunc_mono _ _ h
    (lshr_exact_refine x (.val c) exact))
  cases x with
  | poison => simp [LLVM.Int.trunc, LLVM.Int.lshr, LLVM.Int.shl, LLVM.Int.and,
      LLVM.Int.icmp, Id.run]
  | val x =>
    by_cases hc : c.toNat < w
    · have hnle : ¬w ≤ c.toNat := by omega
      simp [LLVM.Int.trunc, LLVM.Int.lshr, LLVM.Int.shl, LLVM.Int.and,
        LLVM.Int.icmp, LLVM.IntPred.eval, Id.run, BitVec.le_def, hc, hnle,
        trunc_lshr_bit_eq hc]
    · have hle : w ≤ c.toNat := by omega
      simp [LLVM.Int.trunc, LLVM.Int.lshr, LLVM.Int.shl, LLVM.Int.and,
        LLVM.Int.icmp, Id.run, BitVec.le_def, hle]

private theorem ofBool_bne_zero {w : Nat} (x : BitVec w) :
    BitVec.ofBool (x != (0 : BitVec w)) =
      if x = 0 then (0 : BitVec 1) else (1 : BitVec 1) := by
  by_cases h : x = 0
  · subst x
    simp
  · have hb : (x != (0 : BitVec w)) = true := bne_iff_ne.mpr h
    rw [hb]
    simp only [BitVec.ofBool_true]
    rw [if_neg h]

private theorem trunc_or_lshr_bit_eq {w c : Nat} (hw : 0 < w) (hc : c < w)
    (x : BitVec w) :
    ((x >>> c) ||| x).truncate 1 =
      BitVec.ofBool ((x &&& ((1#w <<< c) ||| 1#w)) != (0 : BitVec w)) := by
  rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_one, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight]
  simp only [Nat.add_zero]
  have hone : (1#w) = BitVec.twoPow w 0 := by
    simpa using (BitVec.twoPow_eq w 0).symm
  rw [BitVec.and_or_distrib_left,
    show (1#w <<< c) = BitVec.twoPow w c by rfl, hone,
    BitVec.and_twoPow, BitVec.and_twoPow]
  have hnc : BitVec.twoPow w c ≠ 0#w := by
    intro hz
    have hzNat := congrArg BitVec.toNat hz
    simp [BitVec.toNat_twoPow_of_lt hc] at hzNat
  have hn0 : BitVec.twoPow w 0 ≠ 0#w := by
    intro hz
    have hzNat := congrArg BitVec.toNat hz
    simp [BitVec.toNat_twoPow_of_lt hw] at hzNat
  rw [ofBool_bne_zero]
  cases hb : x.getLsbD c <;> cases hz : x.getLsbD 0 <;>
    simp [hb, hz, BitVec.or_eq_zero_iff, hnc, hn0]

public theorem trunc_or_lshr_refines_bit_test {w : Nat} (h : 1 < w)
    (x : LLVM.Int w) (c : BitVec w) (exact disjoint nsw nuw : Bool) :
    LLVM.Int.trunc
      (LLVM.Int.or (LLVM.Int.lshr x (.val c) exact) x disjoint)
      1 nsw nuw h ⊒
      LLVM.Int.icmp
        (LLVM.Int.and x (LLVM.Int.or
          (LLVM.Int.shl (.val (1 : BitVec w)) (.val c) false false)
          (.val (1 : BitVec w)) false))
        (.val (0 : BitVec w)) .ne := by
  apply isRefinedBy_trans (trunc_flags_refine w 1 h _ nsw nuw)
  apply isRefinedBy_trans (LLVM.Int.trunc_mono _ _ h
    (or_flags_refine w (LLVM.Int.lshr x (.val c) exact) x disjoint))
  apply isRefinedBy_trans (LLVM.Int.trunc_mono _ _ h
    (LLVM.Int.or_mono _ _ _ _ false
      (lshr_exact_refine x (.val c) exact) (isRefinedBy_refl x)))
  cases x with
  | poison => simp [LLVM.Int.trunc, LLVM.Int.lshr, LLVM.Int.shl, LLVM.Int.and,
      LLVM.Int.or, LLVM.Int.icmp, Id.run]
  | val x =>
    by_cases hc : c.toNat < w
    · have hnle : ¬w ≤ c.toNat := by omega
      simp [LLVM.Int.trunc, LLVM.Int.lshr, LLVM.Int.shl, LLVM.Int.and, LLVM.Int.or,
        LLVM.Int.icmp, LLVM.IntPred.eval, Id.run, BitVec.le_def, hc, hnle,
        trunc_or_lshr_bit_eq (by omega) hc]
    · have hle : w ≤ c.toNat := by omega
      simp [LLVM.Int.trunc, LLVM.Int.lshr, LLVM.Int.shl, LLVM.Int.and, LLVM.Int.or,
        LLVM.Int.icmp, Id.run, BitVec.le_def, hle]

public theorem bitreverse_iff {signedness : IntegerType.Signedness} (w : Nat)
    (x : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__bitreverse) () #[IntegerType.mk w signedness]
      #[.int w x] #[v] ↔ v = .int w (LLVM.Int.bitreverse x) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', Interp.pure_eq, Interp.ok.injEq, Prod.mk.injEq,
    Array.mk.injEq, List.cons.injEq, and_true]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public theorem ctpop_iff {signedness : IntegerType.Signedness} (w : Nat)
    (x : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__ctpop) () #[IntegerType.mk w signedness]
      #[.int w x] #[v] ↔ v = .int w (LLVM.Int.ctpop x) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', Interp.pure_eq, Interp.ok.injEq, Prod.mk.injEq,
    Array.mk.injEq, List.cons.injEq, and_true]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public theorem ctlz_bitreverse (x : LLVM.Int w) (flag : Bool) :
    LLVM.Int.ctlz (LLVM.Int.bitreverse x) flag = LLVM.Int.cttz x flag := by
  cases x <;> simp [LLVM.Int.ctlz, LLVM.Int.cttz, LLVM.Int.bitreverse, Id.run,
    BitVec.clz_eq_reverse_ctz]

public theorem cttz_bitreverse (x : LLVM.Int w) (flag : Bool) :
    LLVM.Int.cttz (LLVM.Int.bitreverse x) flag = LLVM.Int.ctlz x flag := by
  cases x <;> simp [LLVM.Int.ctlz, LLVM.Int.cttz, LLVM.Int.bitreverse, Id.run,
    BitVec.ctz_eq_reverse_clz]

public theorem ctpop_bitreverse (x : LLVM.Int w) :
    LLVM.Int.ctpop (LLVM.Int.bitreverse x) = LLVM.Int.ctpop x := by
  cases x <;> simp [LLVM.Int.ctpop, LLVM.Int.bitreverse, Id.run, BitVec.cpop_reverse]

public theorem bswap_iff {signedness : IntegerType.Signedness} (w : Nat)
    (x : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__bswap) () #[IntegerType.mk w signedness]
      #[.int w x] #[v] ↔ v = .int w (LLVM.Int.bswap x) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', Interp.pure_eq, Interp.ok.injEq, Prod.mk.injEq,
    Array.mk.injEq, List.cons.injEq, and_true]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public theorem fshl_iff {signedness : IntegerType.Signedness} (w : Nat)
    (x y c : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__fshl) () #[IntegerType.mk w signedness]
      #[.int w x, .int w y, .int w c] #[v] ↔
      v = .int w (LLVM.Int.fshl x y c) := by
  simp [InterpretsTo, RuntimeValue.ArrayConforms, interpretOp', Llvm.interpretOp']
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public theorem fshr_iff {signedness : IntegerType.Signedness} (w : Nat)
    (x y c : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__fshr) () #[IntegerType.mk w signedness]
      #[.int w x, .int w y, .int w c] #[v] ↔
      v = .int w (LLVM.Int.fshr x y c) := by
  simp [InterpretsTo, RuntimeValue.ArrayConforms, interpretOp', Llvm.interpretOp']
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

private theorem append_slices (x : BitVec w) (r : Nat) (hr : r ≤ w) :
    (x.extractLsb' (w - r) r ++ x.extractLsb' 0 (w - r)).cast (by omega) = x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_extractLsb', dite_eq_ite]
  split <;> rename_i h
  · simp [BitVec.getLsbD_eq_getElem, hi]
  · rw [BitVec.getLsbD_eq_getElem (by omega)]
    congr 1
    omega

private theorem rotateLeft_eq_append_slices (x : BitVec w) (r : Nat) (hr : r < w) :
    x.rotateLeft r =
      (x.extractLsb' 0 (w - r) ++ x.extractLsb' (w - r) r).cast (by omega) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_rotateLeft hi, Nat.mod_eq_of_lt hr,
    BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_extractLsb', dite_eq_ite]
  split <;> rename_i h
  · rw [BitVec.getLsbD_eq_getElem (by omega)]
  · simpa only [Nat.zero_add] using
      (BitVec.getLsbD_eq_getElem (x := x) (i := i - r) (by omega)).symm

private theorem cpop_rotateLeft (x : BitVec w) (r : Nat) :
    (x.rotateLeft r).cpop = x.cpop := by
  rcases w with _ | w
  · rfl
  let s := r % (w + 1)
  have hs : s < w + 1 := Nat.mod_lt _ (by omega)
  rw [← BitVec.rotateLeft_mod_eq_rotateLeft]
  rw [rotateLeft_eq_append_slices x s hs]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.cpop_cast, BitVec.toNat_cast, BitVec.toNat_cpop_append]
  have hx := congrArg (fun z => z.cpop.toNat) (append_slices x s (by omega))
  simp only [BitVec.cpop_cast, BitVec.toNat_cast, BitVec.toNat_cpop_append] at hx
  omega

private theorem rotateRight_eq_append_slices (x : BitVec w) (r : Nat) (hr : r < w) :
    x.rotateRight r =
      (x.extractLsb' 0 r ++ x.extractLsb' r (w - r)).cast (by omega) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_rotateRight hi, Nat.mod_eq_of_lt hr,
    BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_extractLsb', dite_eq_ite]
  split <;> rename_i h
  · simpa only [Nat.zero_add] using
      (BitVec.getLsbD_eq_getElem (x := x) (i := r + i) (by omega)).symm
  · simpa only [Nat.zero_add] using
      (BitVec.getLsbD_eq_getElem (x := x) (i := i - (w - r)) (by omega)).symm

private theorem cpop_rotateRight (x : BitVec w) (r : Nat) :
    (x.rotateRight r).cpop = x.cpop := by
  rcases w with _ | w
  · rfl
  let s := r % (w + 1)
  have hs : s < w + 1 := Nat.mod_lt _ (by omega)
  rw [← BitVec.rotateRight_mod_eq_rotateRight]
  rw [rotateRight_eq_append_slices x s hs]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.cpop_cast, BitVec.toNat_cast, BitVec.toNat_cpop_append]
  have hx := congrArg (fun z => z.cpop.toNat) (append_slices x (w + 1 - s) (by omega))
  simp only [BitVec.cpop_cast, BitVec.toNat_cast, BitVec.toNat_cpop_append] at hx
  have heq : w + 1 - (w + 1 - s) = s := by omega
  rw [heq] at hx
  omega

private theorem funnelLeft_self (x c : BitVec w) :
    ((x ++ x) <<< (c.toNat % w)).extractLsb' w w = x.rotateLeft c.toNat := by
  rcases w with _ | w
  · exact Subsingleton.elim _ _
  have hs : c.toNat % (w + 1) < w + 1 := Nat.mod_lt _ (by omega)
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_rotateLeft hi, BitVec.getElem_extractLsb',
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  by_cases h : i < c.toNat % (w + 1)
  · simp only [h, ↓reduceDIte, show ¬ w + 1 + i < c.toNat % (w + 1) by omega,
      decide_false, Bool.not_false, Bool.true_and,
      show w + 1 + i - c.toNat % (w + 1) < w + 1 by omega, ↓reduceIte]
    simp only [show w + 1 + i < (w + 1) + (w + 1) by omega, decide_true,
      Bool.true_and]
    rw [BitVec.getLsbD_eq_getElem (by omega)]
    congr 1
    omega
  · simp only [h, ↓reduceDIte, show ¬ w + 1 + i < c.toNat % (w + 1) by omega,
      decide_false, Bool.not_false, Bool.true_and,
      show ¬ w + 1 + i - c.toNat % (w + 1) < w + 1 by omega, ↓reduceIte]
    simp only [show w + 1 + i < (w + 1) + (w + 1) by omega, decide_true,
      Bool.true_and]
    rw [BitVec.getLsbD_eq_getElem (by omega)]
    congr 1
    omega

private theorem funnelRight_self (x c : BitVec w) :
    ((x ++ x) >>> (c.toNat % w)).truncate w = x.rotateRight c.toNat := by
  rcases w with _ | w
  · exact Subsingleton.elim _ _
  have hs : c.toNat % (w + 1) < w + 1 := Nat.mod_lt _ (by omega)
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_rotateRight hi]
  rw [BitVec.truncate_eq_setWidth, BitVec.getElem_setWidth_eq_decide_getElem]
  simp only [BitVec.getElem_ushiftRight]
  by_cases h : i < w + 1 - c.toNat % (w + 1)
  · simp only [h, ↓reduceDIte, show i < (w + 1) + (w + 1) by omega,
      decide_true, Bool.true_and, BitVec.getLsbD_append,
      show c.toNat % (w + 1) + i < w + 1 by omega, ↓reduceIte]
    rw [BitVec.getLsbD_eq_getElem (by omega)]
    rw [Bool.eq_iff_iff]
    simp
  · simp only [h, ↓reduceDIte, show i < (w + 1) + (w + 1) by omega,
      decide_true, Bool.true_and, BitVec.getLsbD_append,
      show ¬ c.toNat % (w + 1) + i < w + 1 by omega, ↓reduceIte]
    have hidx1 : c.toNat % (w + 1) + i - (w + 1) < w + 1 := by omega
    rw [BitVec.getLsbD_eq_getElem hidx1]
    have heq : c.toNat % (w + 1) + i - (w + 1) =
        i - (w + 1 - c.toNat % (w + 1)) := by omega
    have hbits := getElem_congr (c := x) (d := x) rfl heq (by omega)
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨_, hb⟩
      exact hbits ▸ hb
    · intro hb
      exact ⟨True.intro, hbits.symm ▸ hb⟩

public theorem ctpop_fshl_self {w : Nat} (x c : LLVM.Int w) :
    LLVM.Int.ctpop (LLVM.Int.fshl x x c) ⊒ LLVM.Int.ctpop x := by
  cases x <;> cases c <;>
    simp [LLVM.Int.ctpop, LLVM.Int.fshl, Id.run, funnelLeft_self, cpop_rotateLeft,
      LLVM.Int.isRefinedBy_iff]

public theorem ctpop_fshr_self {w : Nat} (x c : LLVM.Int w) :
    LLVM.Int.ctpop (LLVM.Int.fshr x x c) ⊒ LLVM.Int.ctpop x := by
  cases x <;> cases c <;>
    simp [LLVM.Int.ctpop, LLVM.Int.fshr, Id.run, funnelRight_self, cpop_rotateRight,
      LLVM.Int.isRefinedBy_iff]

private theorem joinBytes16 (x : BitVec 16) :
    x.extractLsb 15 8 ++ x.extractLsb 7 0 = x := by
  simpa [BitVec.extractLsb] using
    (BitVec.extractLsb'_append_extractLsb' (x := x) (w := 8) (len := 8))

private theorem joinBytes32 (x : BitVec 32) :
    x.extractLsb 31 24 ++ x.extractLsb 23 16 ++
      x.extractLsb 15 8 ++ x.extractLsb 7 0 = x := by
  simp only [BitVec.extractLsb, Nat.reduceSub, Nat.reduceAdd]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := x) (show 24 = 16 + 8 by omega)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := x) (show 16 = 8 + 8 by omega)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := x) (show 8 = 0 + 8 by omega)]
  simp

private theorem joinBytes64 (x : BitVec 64) :
    x.extractLsb 63 56 ++ x.extractLsb 55 48 ++
      x.extractLsb 47 40 ++ x.extractLsb 39 32 ++
      x.extractLsb 31 24 ++ x.extractLsb 23 16 ++
      x.extractLsb 15 8 ++ x.extractLsb 7 0 = x := by
  simp only [BitVec.extractLsb, Nat.reduceSub, Nat.reduceAdd]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := x) (show 56 = 48 + 8 by omega)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := x) (show 48 = 40 + 8 by omega)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := x) (show 40 = 32 + 8 by omega)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := x) (show 32 = 24 + 8 by omega)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := x) (show 24 = 16 + 8 by omega)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := x) (show 16 = 8 + 8 by omega)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := x) (show 8 = 0 + 8 by omega)]
  simp

private theorem cpop_bswap16BV (x : BitVec 16) :
    (LLVM.Int.bswap16BV x).cpop = x.cpop := by
  apply BitVec.eq_of_toNat_eq
  simp only [LLVM.Int.bswap16BV, BitVec.toNat_cpop_append]
  have hx := congrArg (fun z => z.cpop.toNat) (joinBytes16 x)
  simp only [BitVec.toNat_cpop_append] at hx
  omega

private theorem cpop_bswap32BV (x : BitVec 32) :
    (LLVM.Int.bswap32BV x).cpop = x.cpop := by
  apply BitVec.eq_of_toNat_eq
  simp only [LLVM.Int.bswap32BV, BitVec.toNat_cpop_append]
  have hx := congrArg (fun z => z.cpop.toNat) (joinBytes32 x)
  simp only [BitVec.toNat_cpop_append] at hx
  omega

private theorem cpop_bswap64BV (x : BitVec 64) :
    (LLVM.Int.bswap64BV x).cpop = x.cpop := by
  apply BitVec.eq_of_toNat_eq
  simp only [LLVM.Int.bswap64BV, BitVec.toNat_cpop_append]
  have hx := congrArg (fun z => z.cpop.toNat) (joinBytes64 x)
  simp only [BitVec.toNat_cpop_append] at hx
  omega

public theorem ctpop_bswap {w : Nat} (x : LLVM.Int w) :
    LLVM.Int.ctpop (LLVM.Int.bswap x) = LLVM.Int.ctpop x := by
  by_cases h16 : w = 16
  · subst w
    cases x <;> simp [LLVM.Int.ctpop, LLVM.Int.bswap, Id.run, pure, cpop_bswap16BV]
  · by_cases h32 : w = 32
    · subst w
      cases x <;> simp [LLVM.Int.ctpop, LLVM.Int.bswap, Id.run, pure, cpop_bswap32BV]
    · by_cases h64 : w = 64
      · subst w
        cases x <;> simp [LLVM.Int.ctpop, LLVM.Int.bswap, Id.run, pure, cpop_bswap64BV]
      · cases x <;> simp [LLVM.Int.ctpop, LLVM.Int.bswap, Id.run, h16, h32, h64]

/-- Scalar integer bitcasts of equal widths preserve the runtime value. -/
public theorem bitcast_int_iff {signedness : IntegerType.Signedness} (w : Nat)
    (x : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .bitcast) () #[IntegerType.mk w signedness]
      #[.int w x] #[v] ↔ v = .int w x := by
  have hResultType :
      (#[TypeAttr.of IntegerType (IntegerType.mk w signedness)][0]? : Option TypeAttr) =
        some (TypeAttr.of IntegerType (IntegerType.mk w signedness)) := by rfl
  have hType : TypeAttr.of IntegerType (IntegerType.mk w signedness) =
      ⟨.integerType (IntegerType.mk w signedness), by simp⟩ := by
    apply TypeAttr.inj.mpr
    exact integerType_of_val _
  simp only [InterpretsTo]
  constructor
  · rintro ⟨_, hi⟩
    have hv := hi .empty
    simp only [interpretOp', Llvm.interpretOp', hResultType] at hv
    rw [hType] at hv
    simp at hv
    exact hv.symm
  · rintro rfl
    constructor
    · simp
    · intro memory
      simp only [interpretOp', Llvm.interpretOp', hResultType]
      rw [hType]
      simp

private theorem byteType_of_val (t : LLVM.ByteType) :
    (TypeAttr.of LLVM.ByteType t).val = .byteType t := by
  rw [TypeAttr.of_val]
  exact (Attribute.byteType_eq_of t).symm

private theorem pointerType_of_val (t : LLVM.PointerType) :
    (TypeAttr.of LLVM.PointerType t).val = .llvmPointerType t := by
  rw [TypeAttr.of_val]
  exact (Attribute.llvmPointerType_eq_of t).symm

/-- Equal-width scalar integer-to-byte bitcasts preserve the integer bits and
    turn whole-value poison into a per-bit all-poison byte. -/
public theorem bitcast_int_byte_iff (w₁ w₂ : Nat)
    (x : LLVM.Int w₁) (v : RuntimeValue) :
    InterpretsTo (.llvm .bitcast) () #[LLVM.ByteType.mk w₂]
      #[.int w₁ x] #[v] ↔
      ∃ h : w₁ = w₂, v = .byte w₁ (LLVM.Byte.fromInt x) := by
  have hResultType :
      (#[TypeAttr.of LLVM.ByteType (LLVM.ByteType.mk w₂)][0]? : Option TypeAttr) =
        some (TypeAttr.of LLVM.ByteType (LLVM.ByteType.mk w₂)) := by rfl
  have hType : TypeAttr.of LLVM.ByteType (LLVM.ByteType.mk w₂) =
      ⟨.byteType (LLVM.ByteType.mk w₂), by simp⟩ := by
    apply TypeAttr.inj.mpr
    exact byteType_of_val _
  simp only [InterpretsTo]
  constructor
  · rintro ⟨_, hi⟩
    have hv := hi .empty
    simp only [interpretOp', Llvm.interpretOp', hResultType] at hv
    rw [hType] at hv
    by_cases h : w₁ = w₂
    · exact ⟨h, by simpa [h] using hv.symm⟩
    · simp [h] at hv
  · rintro ⟨rfl, rfl⟩
    constructor
    · simp
    · intro memory
      simp only [interpretOp', Llvm.interpretOp', hResultType]
      rw [hType]
      simp

/-- Equal-width scalar byte-to-integer bitcasts collapse any per-bit poison to
    whole-value integer poison. -/
public theorem bitcast_byte_int_iff {signedness : IntegerType.Signedness} (w₁ w₂ : Nat)
    (x : LLVM.Byte w₁) (v : RuntimeValue) :
    InterpretsTo (.llvm .bitcast) () #[IntegerType.mk w₂ signedness]
      #[.byte w₁ x] #[v] ↔ ∃ h : w₁ = w₂, v = .int w₁ x.toInt := by
  have hResultType :
      (#[TypeAttr.of IntegerType (IntegerType.mk w₂ signedness)][0]? : Option TypeAttr) =
        some (TypeAttr.of IntegerType (IntegerType.mk w₂ signedness)) := by rfl
  have hType : TypeAttr.of IntegerType (IntegerType.mk w₂ signedness) =
      ⟨.integerType (IntegerType.mk w₂ signedness), by simp⟩ := by
    apply TypeAttr.inj.mpr
    exact integerType_of_val _
  simp only [InterpretsTo]
  constructor
  · rintro ⟨_, hi⟩
    have hv := hi .empty
    simp only [interpretOp', Llvm.interpretOp', hResultType] at hv
    rw [hType] at hv
    by_cases h : w₁ = w₂
    · exact ⟨h, by simpa [h] using hv.symm⟩
    · simp [h] at hv
  · rintro ⟨rfl, rfl⟩
    constructor
    · simp
    · intro memory
      simp only [interpretOp', Llvm.interpretOp', hResultType]
      rw [hType]
      simp

/-- Equal-width scalar byte-to-byte bitcasts preserve every value and poison bit. -/
public theorem bitcast_byte_iff (w₁ w₂ : Nat) (x : LLVM.Byte w₁) (v : RuntimeValue) :
    InterpretsTo (.llvm .bitcast) () #[LLVM.ByteType.mk w₂]
      #[.byte w₁ x] #[v] ↔ ∃ h : w₁ = w₂, v = .byte w₁ x := by
  have hResultType :
      (#[TypeAttr.of LLVM.ByteType (LLVM.ByteType.mk w₂)][0]? : Option TypeAttr) =
        some (TypeAttr.of LLVM.ByteType (LLVM.ByteType.mk w₂)) := by rfl
  have hType : TypeAttr.of LLVM.ByteType (LLVM.ByteType.mk w₂) =
      ⟨.byteType (LLVM.ByteType.mk w₂), by simp⟩ := by
    apply TypeAttr.inj.mpr
    exact byteType_of_val _
  simp only [InterpretsTo]
  constructor
  · rintro ⟨_, hi⟩
    have hv := hi .empty
    simp only [interpretOp', Llvm.interpretOp', hResultType] at hv
    rw [hType] at hv
    by_cases h : w₁ = w₂
    · exact ⟨h, by simpa [h] using hv.symm⟩
    · simp [h] at hv
  · rintro ⟨rfl, rfl⟩
    constructor
    · simp
    · intro memory
      simp only [interpretOp', Llvm.interpretOp', hResultType]
      rw [hType]
      simp

/-- Same-address-space scalar pointer-to-pointer bitcasts preserve the modeled pointer. -/
public theorem bitcast_pointer_iff (ptrTy : LLVM.PointerType) (x : LLVM.Ptr)
    (v : RuntimeValue) :
    InterpretsTo (.llvm .bitcast) () #[ptrTy] #[.addr x] #[v] ↔ v = .addr x := by
  have hResultType :
      (#[TypeAttr.of LLVM.PointerType ptrTy][0]? : Option TypeAttr) =
        some (TypeAttr.of LLVM.PointerType ptrTy) := by rfl
  have hType : TypeAttr.of LLVM.PointerType ptrTy =
      ⟨.llvmPointerType ptrTy, by simp⟩ := by
    apply TypeAttr.inj.mpr
    exact pointerType_of_val _
  simp only [InterpretsTo]
  constructor
  · rintro ⟨_, hi⟩
    have hv := hi .empty
    simp only [interpretOp', Llvm.interpretOp', hResultType] at hv
    rw [hType] at hv
    simp at hv
    exact hv.symm
  · rintro rfl
    constructor
    · simp
    · intro memory
      simp only [interpretOp', Llvm.interpretOp', hResultType]
      rw [hType]
      simp

/-- A scalar pointer-to-byte bitcast exposes the modeled 64-bit address bits
    without consulting memory. -/
public theorem bitcast_pointer_byte_iff (w : Nat) (x : LLVM.Ptr) (v : RuntimeValue) :
    InterpretsTo (.llvm .bitcast) () #[LLVM.ByteType.mk w]
      #[.addr x] #[v] ↔ w = 64 ∧ v = .byte 64 x.toByte := by
  have hResultType :
      (#[TypeAttr.of LLVM.ByteType (LLVM.ByteType.mk w)][0]? : Option TypeAttr) =
        some (TypeAttr.of LLVM.ByteType (LLVM.ByteType.mk w)) := by rfl
  have hType : TypeAttr.of LLVM.ByteType (LLVM.ByteType.mk w) =
      ⟨.byteType (LLVM.ByteType.mk w), by simp⟩ := by
    apply TypeAttr.inj.mpr
    exact byteType_of_val _
  simp only [InterpretsTo]
  constructor
  · rintro ⟨_, hi⟩
    have hv := hi .empty
    simp only [interpretOp', Llvm.interpretOp', hResultType] at hv
    rw [hType] at hv
    by_cases h : w = 64
    · exact ⟨h, by simpa [h] using hv.symm⟩
    · simp [h] at hv
  · rintro ⟨rfl, rfl⟩
    constructor
    · simp
    · intro memory
      simp only [interpretOp', Llvm.interpretOp', hResultType]
      rw [hType]
      simp

/-- Scalar pointer-to-i64 conversion exposes the modeled address bits without
    consulting memory. -/
public theorem ptrtoint_iff {signedness : IntegerType.Signedness}
    (x : LLVM.Ptr) (v : RuntimeValue) :
    InterpretsTo (.llvm .ptrtoint) () #[IntegerType.mk 64 signedness]
      #[.addr x] #[v] ↔ v = .int 64 x.toInt := by
  have hResultType :
      (#[TypeAttr.of IntegerType (IntegerType.mk 64 signedness)][0]? : Option TypeAttr) =
        some (TypeAttr.of IntegerType (IntegerType.mk 64 signedness)) := by rfl
  have hType : TypeAttr.of IntegerType (IntegerType.mk 64 signedness) =
      ⟨.integerType (IntegerType.mk 64 signedness), by simp⟩ := by
    apply TypeAttr.inj.mpr
    exact integerType_of_val _
  simp only [InterpretsTo]
  constructor
  · rintro ⟨_, hi⟩
    have hv := hi .empty
    simp only [interpretOp', Llvm.interpretOp', hResultType] at hv
    rw [hType] at hv
    simp at hv
    exact hv.symm
  · rintro rfl
    constructor
    · simp
    · intro memory
      simp only [interpretOp', Llvm.interpretOp', hResultType]
      rw [hType]
      simp

/-- Converting the modeled pointer address through `Byte 64` does not change
    the whole-value integer representation. -/
public theorem ptr_toByte_toInt (x : LLVM.Ptr) : x.toByte.toInt = x.toInt := by
  cases x <;>
    simp [LLVM.Ptr.toByte, LLVM.Ptr.toInt, LLVM.Byte.toInt,
      LLVM.Byte.fromUInt64, LLVM.Byte.fromBitVec, LLVM.Byte.allPoison]

/-- Converting a byte through the whole-value integer poison model may lose
    information, but the resulting byte still refines the original per-bit byte. -/
public theorem byte_fromInt_toInt_refines {w : Nat} (x : LLVM.Byte w) :
    LLVM.Byte.fromInt x.toInt ⊒ x := by
  cases x with
  | mk val poison hp =>
    simp only [LLVM.Byte.toInt, LLVM.Byte.fromInt, LLVM.Byte.isRefinedBy]
    split <;> split <;> grind

private theorem bv_not_sext_not {s d : Nat} (hs : 0 < s) (h : s < d)
    (x : BitVec s) : ~~~((~~~x).signExtend d) = x.signExtend d := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_not, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_signExtend]
  by_cases his : i < s
  · simp [his]
  · simp [his, hs]

private theorem bv_not_zext_not_of_msb_true {s d : Nat} (_h : s < d)
    (x : BitVec s) (hx : x.msb = true) :
    ~~~((~~~x).zeroExtend d) = x.signExtend d := by
  rw [BitVec.signExtend_eq_not_setWidth_not_of_msb_true hx]

private theorem bv_not_trunc_not {s d : Nat} (h : d < s) (x : BitVec s) :
    ~~~((~~~x).truncate d) = x.truncate d := by
  simp only [BitVec.truncate_eq_setWidth]
  rw [BitVec.setWidth_not (by omega)]
  simp

/-- Complementing a sign extension of a complemented nonzero-width scalar
    equals sign-extending the original scalar. -/
public theorem invert_sext_not_refines {s d : Nat} (hs : 0 < s) (h : s < d)
    (x : LLVM.Int s) :
    LLVM.Int.xor (LLVM.Int.sext (LLVM.Int.xor x (.val (BitVec.ofInt s (-1)))) d h)
      (.val (BitVec.ofInt d (-1))) ⊒ LLVM.Int.sext x d h := by
  rw [show BitVec.ofInt s (-1) = BitVec.allOnes s by
    rw [BitVec.ofInt_neg]; exact BitVec.neg_one_eq_allOnes]
  rw [show BitVec.ofInt d (-1) = BitVec.allOnes d by
    rw [BitVec.ofInt_neg]; exact BitVec.neg_one_eq_allOnes]
  cases x <;> simp [LLVM.Int.xor, LLVM.Int.sext, Id.run,
    BitVec.xor_allOnes, bv_not_sext_not hs h, isRefinedBy_eq]

/-- With `nneg`, complementing a zero extension of a complemented scalar
    refines the corresponding sign extension.  The source is poison in the
    remaining sign case. -/
public theorem invert_zext_nneg_not_refines {s d : Nat}
    (hs : 0 < s) (h : s < d) (x : LLVM.Int s) :
    LLVM.Int.xor (LLVM.Int.zext (LLVM.Int.xor x (.val (BitVec.ofInt s (-1)))) d true h)
      (.val (BitVec.ofInt d (-1))) ⊒ LLVM.Int.sext x d h := by
  rw [show BitVec.ofInt s (-1) = BitVec.allOnes s by
    rw [BitVec.ofInt_neg]; exact BitVec.neg_one_eq_allOnes]
  rw [show BitVec.ofInt d (-1) = BitVec.allOnes d by
    rw [BitVec.ofInt_neg]; exact BitVec.neg_one_eq_allOnes]
  cases x with
  | poison => simp [LLVM.Int.xor, LLVM.Int.zext, LLVM.Int.sext, Id.run]
  | val x =>
    cases hx : x.msb
    · have hnot : (~~~x).msb = true := by
        simp [BitVec.msb, hs,
          show x.getMsbD 0 = false by simpa [BitVec.msb] using hx]
      simp [LLVM.Int.xor, LLVM.Int.zext, LLVM.Int.sext, Id.run,
        BitVec.xor_allOnes, hnot, isRefinedBy_eq]
    · have hnot : (~~~x).msb = false := by
        simp [BitVec.msb, hs,
          show x.getMsbD 0 = true by simpa [BitVec.msb] using hx]
      simp [LLVM.Int.xor, LLVM.Int.zext, LLVM.Int.sext, Id.run,
        BitVec.xor_allOnes, hnot, bv_not_zext_not_of_msb_true h x hx,
        isRefinedBy_eq]

/-- Complement commutes through truncation.  Any matched trunc nowrap flags
    may only make the source poison, so the unflagged direct trunc refines it. -/
public theorem invert_trunc_not_refines {s d : Nat} (h : d < s)
    (x : LLVM.Int s) (nsw nuw : Bool) :
    LLVM.Int.xor (LLVM.Int.trunc (LLVM.Int.xor x (.val (BitVec.ofInt s (-1))))
      d nsw nuw h) (.val (BitVec.ofInt d (-1))) ⊒
      LLVM.Int.trunc x d false false h := by
  rw [show BitVec.ofInt s (-1) = BitVec.allOnes s by
    rw [BitVec.ofInt_neg]; exact BitVec.neg_one_eq_allOnes]
  rw [show BitVec.ofInt d (-1) = BitVec.allOnes d by
    rw [BitVec.ofInt_neg]; exact BitVec.neg_one_eq_allOnes]
  apply isRefinedBy_trans (xor_refine_mono d
    (trunc_flags_refine s d h (LLVM.Int.xor x (.val (BitVec.allOnes s))) nsw nuw)
    (isRefinedBy_refl _))
  cases x <;> simp [LLVM.Int.xor, LLVM.Int.trunc, Id.run, BitVec.xor_allOnes,
    bv_not_trunc_not h, isRefinedBy_eq]

private theorem bv_sext_sext {s m d : Nat} (hsm : s < m) (_hmd : m < d)
    (x : BitVec s) : (x.signExtend m).signExtend d = x.signExtend d := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_signExtend]
  have hm : 0 < m := by omega
  by_cases him : i < m
  · by_cases his : i < s <;> simp [hi, him, his]
  · have hsi : ¬i < s := by omega
    simp [hi, him, hsi, BitVec.msb_signExtend, hm, show ¬m ≤ s by omega]

private theorem bv_setWidth_setWidth {s m d : Nat} (hdm : d < m) (x : BitVec s) :
    (x.setWidth m).setWidth d = x.setWidth d := by
  rw [BitVec.setWidth_setWidth]
  omega

private theorem bv_sext_trunc_lt {s m d : Nat} (hsm : s < m) (hds : d < s)
    (x : BitVec s) : (x.signExtend m).truncate d = x.truncate d := by
  simp only [BitVec.truncate_eq_setWidth]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getLsbD_eq_getElem (by omega)]
  rw [BitVec.getElem_signExtend (by omega)]
  simp [show i < s by omega]

private theorem bv_sext_trunc_gt {s m d : Nat} (_hsm : s < m) (_hsd : s < d)
    (hdm : d < m) (x : BitVec s) :
    (x.signExtend m).truncate d = x.signExtend d := by
  simp only [BitVec.truncate_eq_setWidth]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getLsbD_eq_getElem hi]
  rw [BitVec.getElem_signExtend (by omega), BitVec.getElem_signExtend hi]

private theorem bv_sext_trunc_eq {s m : Nat} (hsm : s < m) (x : BitVec s) :
    (x.signExtend m).truncate s = x := by
  simp only [BitVec.truncate_eq_setWidth]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getLsbD_eq_getElem hi]
  rw [BitVec.getElem_signExtend (by omega)]
  simp [hi]

private theorem bv_zext_sext {s m d : Nat} (hsm : s < m) (_hmd : m < d)
    (x : BitVec s) : (x.zeroExtend m).signExtend d = x.zeroExtend d := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · simp only [BitVec.zeroExtend_eq_setWidth]
    rw [BitVec.setWidth_setWidth]
    omega
  · rw [BitVec.msb_setWidth]
    have hge : s ≤ m - 1 := by omega
    simp [BitVec.getLsbD_of_ge x (m - 1) hge]

public theorem compose_trunc_refines {s m d : Nat} (hmd : d < m) (hsm : m < s)
    (x : LLVM.Int s) (innerNsw innerNuw outerNsw outerNuw : Bool) :
    LLVM.Int.trunc (LLVM.Int.trunc x m innerNsw innerNuw hsm)
        d outerNsw outerNuw hmd ⊒
      LLVM.Int.trunc x d false false (by omega) := by
  apply isRefinedBy_trans (trunc_flags_refine m d hmd _ outerNsw outerNuw)
  apply isRefinedBy_trans (trunc_refine_mono m d hmd
    (trunc_flags_refine s m hsm x innerNsw innerNuw))
  cases x <;> simp [LLVM.Int.trunc, Id.run, bv_setWidth_setWidth hmd]

public theorem compose_sext_refines {s m d : Nat} (hsm : s < m) (hmd : m < d)
    (x : LLVM.Int s) :
    LLVM.Int.sext (LLVM.Int.sext x m hsm) d hmd ⊒
      LLVM.Int.sext x d (by omega) := by
  cases x <;> simp [LLVM.Int.sext, Id.run, bv_sext_sext hsm hmd]

public theorem compose_zext_sext_refines {s m d : Nat} (hsm : s < m) (hmd : m < d)
    (x : LLVM.Int s) (nneg : Bool) :
    LLVM.Int.sext (LLVM.Int.zext x m nneg hsm) d hmd ⊒
      LLVM.Int.zext x d false (by omega) := by
  apply isRefinedBy_trans (LLVM.Int.sext_mono _ _ hmd
    (zext_flag_refines hsm x nneg))
  cases x <;> simp [LLVM.Int.sext, LLVM.Int.zext, Id.run, bv_zext_sext hsm hmd]

public theorem compose_zext_trunc_to_zext_refines {s m d : Nat}
    (hsm : s < m) (hsd : s < d) (hdm : d < m) (x : LLVM.Int s)
    (nneg nsw nuw : Bool) :
    LLVM.Int.trunc (LLVM.Int.zext x m nneg hsm) d nsw nuw hdm ⊒
      LLVM.Int.zext x d false hsd := by
  apply isRefinedBy_trans (trunc_flags_refine m d hdm _ nsw nuw)
  apply isRefinedBy_trans (trunc_refine_mono m d hdm (zext_flag_refines hsm x nneg))
  cases x <;> simp [LLVM.Int.trunc, LLVM.Int.zext, Id.run, bv_setWidth_setWidth hdm]

public theorem compose_zext_trunc_to_trunc_refines {s m d : Nat}
    (hsm : s < m) (hds : d < s) (x : LLVM.Int s) (nneg nsw nuw : Bool) :
    LLVM.Int.trunc (LLVM.Int.zext x m nneg hsm) d nsw nuw (by omega) ⊒
      LLVM.Int.trunc x d false false hds := by
  apply isRefinedBy_trans (trunc_flags_refine m d (by omega) _ nsw nuw)
  apply isRefinedBy_trans (trunc_refine_mono m d (by omega) (zext_flag_refines hsm x nneg))
  cases x <;> simp [LLVM.Int.trunc, LLVM.Int.zext, Id.run,
    bv_setWidth_setWidth (by omega : d < m)]

public theorem compose_zext_trunc_to_bitcast_refines {s m : Nat} (hsm : s < m)
    (x : LLVM.Int s) (nneg nsw nuw : Bool) :
    LLVM.Int.trunc (LLVM.Int.zext x m nneg hsm) s nsw nuw hsm ⊒ x := by
  apply isRefinedBy_trans (trunc_flags_refine m s hsm _ nsw nuw)
  apply isRefinedBy_trans (trunc_refine_mono m s hsm (zext_flag_refines hsm x nneg))
  cases x <;> simp [LLVM.Int.trunc, LLVM.Int.zext, Id.run, bv_setWidth_setWidth hsm]

public theorem compose_sext_trunc_to_sext_refines {s m d : Nat}
    (hsm : s < m) (hsd : s < d) (hdm : d < m) (x : LLVM.Int s)
    (nsw nuw : Bool) :
    LLVM.Int.trunc (LLVM.Int.sext x m hsm) d nsw nuw hdm ⊒
      LLVM.Int.sext x d hsd := by
  apply isRefinedBy_trans (trunc_flags_refine m d hdm _ nsw nuw)
  cases x <;> simp [LLVM.Int.trunc, LLVM.Int.sext, Id.run,
    bv_sext_trunc_gt hsm hsd hdm]

public theorem compose_sext_trunc_to_trunc_refines {s m d : Nat}
    (hsm : s < m) (hds : d < s) (x : LLVM.Int s) (nsw nuw : Bool) :
    LLVM.Int.trunc (LLVM.Int.sext x m hsm) d nsw nuw (by omega) ⊒
      LLVM.Int.trunc x d false false hds := by
  apply isRefinedBy_trans (trunc_flags_refine m d (by omega) _ nsw nuw)
  cases x <;> simp [LLVM.Int.trunc, LLVM.Int.sext, Id.run,
    bv_sext_trunc_lt hsm hds]

public theorem compose_sext_trunc_to_bitcast_refines {s m : Nat} (hsm : s < m)
    (x : LLVM.Int s) (nsw nuw : Bool) :
    LLVM.Int.trunc (LLVM.Int.sext x m hsm) s nsw nuw hsm ⊒ x := by
  apply isRefinedBy_trans (trunc_flags_refine m s hsm _ nsw nuw)
  cases x <;> simp [LLVM.Int.trunc, LLVM.Int.sext, Id.run, bv_sext_trunc_eq hsm]


private theorem odd_shift_low_bit {w : Nat} (hw : 0 < w) (c x : BitVec w)
    (hc : c.getLsbD 0 = true) :
    (c <<< x).truncate 1 = BitVec.ofBool (x == (0 : BitVec w)) := by
  rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_one, BitVec.getLsbD_shiftLeft']
  by_cases hx : x = 0
  · subst x
    have hc0 := BitVec.getElem_of_getLsbD_eq_true hc
    have hc0' : c[0] = true := by rw [hc0]; trivial
    simp [hw, hc0']
  · have hnat : x.toNat ≠ 0 := by
      intro h
      apply hx
      apply BitVec.eq_of_toNat_eq
      simpa using h
    have hpos : 0 < x.toNat := Nat.pos_of_ne_zero hnat
    have hbeq : (x == (0 : BitVec w)) = false := beq_eq_false_iff_ne.mpr hx
    simp [hw, hpos]
    have hz : BitVec.ofBool (x == (0 : BitVec w)) = (0 : BitVec 1) := by
      rw [hbeq]
      rfl
    exact hz.symm


private theorem shl_flags_refine_cast {w : Nat} (_hw : 1 < w) (c x : LLVM.Int w) (nsw nuw : Bool) :
    LLVM.Int.shl c x nsw nuw ⊒ LLVM.Int.shl c x false false := by
  cases c with
  | poison => simp [LLVM.Int.shl, isRefinedBy, Id.run]
  | val c =>
    cases x with
    | poison => simp [LLVM.Int.shl, isRefinedBy, Id.run]
    | val x =>
      have hmod : w % 2 ^ w = w := Nat.mod_eq_of_lt
        (Nat.lt_pow_self (a := 2) (by omega))
      by_cases hle : w ≤ x.toNat
      · cases nsw <;> cases nuw <;>
          simp [LLVM.Int.shl, isRefinedBy, Id.run, pure, BitVec.le_def, hmod, hle]
      · have hlt : x.toNat < w := by omega
        by_cases hs : (c <<< x.toNat).sshiftRight x.toNat = c
        <;> by_cases hu : (c <<< x.toNat) >>> x.toNat = c
        <;> cases nsw <;> cases nuw
        <;> simp [LLVM.Int.shl, isRefinedBy, Id.run, pure, BitVec.le_def,
          BitVec.sshiftRight_eq', BitVec.ushiftRight_eq', hmod, hle, hlt, hs, hu]

public theorem trunc_shl_odd_refines_icmp_eq_zero {w : Nat} (h : 1 < w)
    (c x : LLVM.Int w) (hc : ∀ cv, c = .val cv → cv.getLsbD 0 = true)
    (shlNsw shlNuw truncNsw truncNuw : Bool) :
    LLVM.Int.trunc (LLVM.Int.shl c x shlNsw shlNuw) 1 truncNsw truncNuw h ⊒
      LLVM.Int.icmp x (.val (0 : BitVec w)) .eq := by
  apply isRefinedBy_trans (trunc_flags_refine w 1 h _ truncNsw truncNuw)
  apply isRefinedBy_trans (LLVM.Int.trunc_mono _ _ h
    (shl_flags_refine_cast h c x shlNsw shlNuw))
  cases c with
  | poison => simp [LLVM.Int.trunc, LLVM.Int.shl, LLVM.Int.icmp, Id.run]
  | val c =>
    have hc' : c.getLsbD 0 = true := hc c rfl
    cases x with
    | poison => simp [LLVM.Int.trunc, LLVM.Int.shl, LLVM.Int.icmp, Id.run]
    | val x =>
      by_cases hxw : x.toNat < w
      · have hnle : ¬w ≤ x.toNat := by omega
        have hmod : w % 2 ^ w = w := Nat.mod_eq_of_lt
          (Nat.lt_pow_self (a := 2) (by omega))
        simpa [LLVM.Int.trunc, LLVM.Int.shl, LLVM.Int.icmp, LLVM.IntPred.eval,
          isRefinedBy, Id.run, pure, BitVec.le_def, hmod, hnle,
          BitVec.truncate_eq_setWidth, BitVec.shiftLeft_eq'] using
          odd_shift_low_bit (by omega) c x hc'
      · have hle : w ≤ x.toNat := by omega
        simp [LLVM.Int.trunc, LLVM.Int.shl, LLVM.Int.icmp, Id.run, BitVec.le_def, hle]

private theorem trunc_xor_bit_of_representable {w : Nat} (x y : BitVec w)
    (hrep : ((x ^^^ y).truncate 1).signExtend w = x ^^^ y ∨
      ((x ^^^ y).truncate 1).zeroExtend w = x ^^^ y) :
    (x ^^^ y).truncate 1 = BitVec.ofBool (x != y) := by
  rcases BitVec.eq_zero_or_eq_one ((x ^^^ y).truncate 1) with hq | hq
  · have hz : x ^^^ y = 0 := by
      rcases hrep with hs | hu
      · rw [← hs, hq]
        rw [BitVec.signExtend_eq_setWidth_of_msb_false (by simp)]
        simp
      · rw [← hu, hq]
        simp
    have hxy : x = y := BitVec.xor_eq_zero_iff.mp hz
    rw [hq, hxy]
    simp
  · have hz : x ^^^ y ≠ 0 := by
      intro hz
      rw [hz] at hq
      simp at hq
    have hxy : x ≠ y := by
      intro heq
      apply hz
      exact BitVec.xor_eq_zero_iff.mpr heq
    rw [hq, show (x != y) = true from bne_iff_ne.mpr hxy]
    rfl

public theorem trunc_xor_flags_refines_icmp_ne {w : Nat} (h : 1 < w)
    (x y : LLVM.Int w) (nsw nuw : Bool) (hflag : nsw = true ∨ nuw = true) :
    LLVM.Int.trunc (LLVM.Int.xor x y) 1 nsw nuw h ⊒ LLVM.Int.icmp x y .ne := by
  cases x with
  | poison => simp [LLVM.Int.trunc, LLVM.Int.xor, LLVM.Int.icmp, Id.run]
  | val x =>
    cases y with
    | poison => simp [LLVM.Int.trunc, LLVM.Int.xor, LLVM.Int.icmp, Id.run]
    | val y =>
      simp only [LLVM.Int.xor, LLVM.Int.trunc, LLVM.Int.icmp, LLVM.IntPred.eval, Id.run]
      let q := (x ^^^ y).truncate 1
      cases nsw <;> cases nuw
      all_goals simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true,
        decide_eq_true_eq, ite_false] at *
      · simp at hflag
      · change (if q.zeroExtend w ≠ x ^^^ y then LLVM.Int.poison else .val q) ⊒
          .val (BitVec.ofBool (x != y))
        by_cases hu : q.zeroExtend w ≠ x ^^^ y
        · simp [hu, isRefinedBy]
        · rw [if_neg hu]
          change q = BitVec.ofBool (x != y)
          simpa only [q] using trunc_xor_bit_of_representable x y
            (Or.inr (Classical.not_not.mp hu))
      · change (if q.signExtend w ≠ x ^^^ y then LLVM.Int.poison else .val q) ⊒
          .val (BitVec.ofBool (x != y))
        by_cases hs : q.signExtend w ≠ x ^^^ y
        · simp [hs, isRefinedBy]
        · rw [if_neg hs]
          change q = BitVec.ofBool (x != y)
          simpa only [q] using trunc_xor_bit_of_representable x y
            (Or.inl (Classical.not_not.mp hs))
      · change (if q.signExtend w ≠ x ^^^ y then LLVM.Int.poison
          else if q.zeroExtend w ≠ x ^^^ y then LLVM.Int.poison else .val q) ⊒
          .val (BitVec.ofBool (x != y))
        by_cases hs : q.signExtend w ≠ x ^^^ y
        · simp [hs, isRefinedBy]
        · by_cases hu : q.zeroExtend w ≠ x ^^^ y
          · simp [hs, hu, isRefinedBy]
          · rw [if_neg hs, if_neg hu]
            change q = BitVec.ofBool (x != y)
            simpa only [q] using trunc_xor_bit_of_representable x y
              (Or.inl (Classical.not_not.mp hs))

public theorem trunc_usub_sat_one_refines_icmp_eq_zero {w : Nat} (h : 1 < w)
    (x : LLVM.Int w) (nsw nuw : Bool) :
    LLVM.Int.trunc (LLVM.Int.usubSat (.val (BitVec.ofInt w 1)) x)
      1 nsw nuw h ⊒ LLVM.Int.icmp x (.val (BitVec.ofInt w 0)) .eq := by
  apply isRefinedBy_trans (trunc_flags_refine w 1 h _ nsw nuw)
  change LLVM.Int.trunc (LLVM.Int.usubSat (.val (1 : BitVec w)) x)
      1 false false h ⊒ LLVM.Int.icmp x (.val (0 : BitVec w)) .eq
  have hset : (1 : BitVec w).setWidth 1 = (1 : BitVec 1) :=
    BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by omega)
  cases x with
  | poison => simp [LLVM.Int.trunc, LLVM.Int.usubSat, LLVM.Int.icmp, Id.run]
  | val x =>
    by_cases hx : x = 0
    · subst x
      simp [LLVM.Int.trunc, LLVM.Int.usubSat, LLVM.Int.icmp, LLVM.IntPred.eval,
        BitVec.usubOverflow, Id.run, pure, isRefinedBy, show 0 < w by omega]
      exact hset
    · by_cases hover : BitVec.usubOverflow (1 : BitVec w) x = true
      · have hbeq : (x == (0 : BitVec w)) = false := beq_eq_false_iff_ne.mpr hx
        simp only [LLVM.Int.usubSat, Id.run]
        rw [hover]
        simp [LLVM.Int.trunc, LLVM.Int.icmp, LLVM.IntPred.eval, Id.run, pure,
          isRefinedBy]
        have hz : BitVec.ofBool (x == (0 : BitVec w)) = (0 : BitVec 1) := by
          rw [hbeq]
          rfl
        exact hz.symm
      · have hone : (1 : BitVec w).toNat = 1 := by simp [show 0 < w by omega]
        have hover' : ¬(1 : BitVec w).toNat < x.toNat := by
          simpa [BitVec.usubOverflow] using hover
        have hle : x.toNat ≤ 1 := by omega
        have hpos : 0 < x.toNat := by
          apply Nat.pos_of_ne_zero
          intro hz
          apply hx
          apply BitVec.eq_of_toNat_eq
          simpa using hz
        have hxnat : x.toNat = 1 := by omega
        have hxeq : x = (1 : BitVec w) := by
          apply BitVec.eq_of_toNat_eq
          omega
        subst x
        have h10 : (1 : BitVec w) ≠ 0 := by
          intro heq
          have := congrArg BitVec.toNat heq
          simp [show 0 < w by omega] at this
        simp [LLVM.Int.trunc, LLVM.Int.usubSat, LLVM.Int.icmp, LLVM.IntPred.eval,
          BitVec.usubOverflow, Id.run, pure, isRefinedBy,
          show 0 < w by omega]
        have hbeq : ((1 : BitVec w) == (0 : BitVec w)) = false :=
          beq_eq_false_iff_ne.mpr h10
        have hz : BitVec.ofBool ((1 : BitVec w) == (0 : BitVec w)) =
            (0 : BitVec 1) := by
          rw [hbeq]
          rfl
        exact hz.symm

public theorem usub_sat_iff {signedness : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__usub__sat) () #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔ v = .int w (LLVM.Int.usubSat x y) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', ne_eq, not_true_eq_false, ↓reduceDIte, LLVM.Int.cast_self,
    Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
    List.cons.injEq, and_true, TypeAttr.of_val]
  constructor
  · rintro ⟨_, hi⟩
    exact (hi .empty).symm
  · grind


end Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics
