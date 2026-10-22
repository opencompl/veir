import Veir.InstSimplify.CmpSelectSupport
import Init.Data.Nat.Power2.Bitwise
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify

theorem mul_scalar_cases {w : Nat} (x : LLVM.Int w) (m : BitVec w) (nsw nuw : Bool) :
    LLVM.Int.mul x (.val m) nsw nuw = .poison ∨
      ∃ v, x = .val v ∧ LLVM.Int.mul x (.val m) nsw nuw = .val (v*m) := by
  cases x with
  | poison => simp [LLVM.Int.mul, Id.run, pure]
  | val x =>
    by_cases hs : nsw = true ∧ x.smulOverflow m = true <;>
      by_cases hu : nuw = true ∧ x.umulOverflow m = true <;>
      simp [LLVM.Int.mul, hs, hu, Id.run, pure]

theorem udiv_scalar_cases {w : Nat} (x : LLVM.Int w) (d : BitVec w) (exact : Bool) :
    LLVM.Int.udiv x (.val d) exact = .poison ∨
      ∃ v, x = .val v ∧ LLVM.Int.udiv x (.val d) exact = .val (v/d) := by
  cases x with
  | poison => simp [LLVM.Int.udiv, Id.run, pure]
  | val x =>
    by_cases he : exact = true ∧ x%d ≠ 0#w <;> by_cases hd : d = 0#w <;>
      simp [LLVM.Int.udiv, he, hd, Id.run, pure]

theorem shl_scalar_cases {w : Nat} (x : LLVM.Int w) (s : BitVec w) (nsw nuw : Bool) :
    LLVM.Int.shl x (.val s) nsw nuw = .poison ∨
      ∃ v, x = .val v ∧ s.toNat < w ∧
        LLVM.Int.shl x (.val s) nsw nuw = .val (v <<< s) := by
  cases x with
  | poison => simp [LLVM.Int.shl, Id.run, pure]
  | val x =>
    by_cases hw : s.toNat ≥ w <;>
      by_cases hs : nsw = true ∧ (x <<< s).sshiftRight' s ≠ x <;>
      by_cases hu : nuw = true ∧ (x <<< s) >>> s ≠ x <;>
      (simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.sshiftRight_eq'] at hs hu) <;>
      simp [LLVM.Int.shl, BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_two_pow_self), hw, hs, hu, Id.run, pure] <;> omega

theorem lshr_scalar_cases {w : Nat} (x : LLVM.Int w) (s : BitVec w) (exact : Bool) :
    LLVM.Int.lshr x (.val s) exact = .poison ∨
      ∃ v, x = .val v ∧ s.toNat < w ∧
        LLVM.Int.lshr x (.val s) exact = .val (v >>> s) := by
  cases x with
  | poison => simp [LLVM.Int.lshr, Id.run, pure]
  | val x =>
    by_cases hw : s.toNat ≥ w <;>
      by_cases he : exact = true ∧ (x >>> s) <<< s ≠ x <;>
      (simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq'] at he) <;>
      simp [LLVM.Int.lshr, BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_two_pow_self), hw, he, Id.run, pure] <;> omega

theorem mul_udiv_bound {w : Nat} (x a b : BitVec w) (h : a.ule b = true) :
    ((x*a)/b).toNat ≤ x.toNat := by
  have hab : a.toNat ≤ b.toNat := of_decide_eq_true h
  simp only [BitVec.toNat_udiv, BitVec.toNat_mul]
  apply Nat.div_le_of_le_mul
  calc (x.toNat * a.toNat) % 2^w ≤ x.toNat * a.toNat := Nat.mod_le _ _
       _ ≤ x.toNat * b.toNat := Nat.mul_le_mul_left _ hab
       _ = b.toNat * x.toNat := Nat.mul_comm _ _

theorem mul_lshr_bound {w : Nat} (x a s : BitVec w)
    (hw : s.toNat < w) (h : a.ule (BitVec.twoPow w s.toNat) = true) :
    ((x*a) >>> s).toNat ≤ x.toNat := by
  have hab : a.toNat ≤ 2^s.toNat := by
    have := of_decide_eq_true h
    simpa only [BitVec.toNat_twoPow_of_lt hw] using this
  simp only [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul]
  apply Nat.div_le_of_le_mul
  calc (x.toNat * a.toNat) % 2^w ≤ x.toNat * a.toNat := Nat.mod_le _ _
       _ ≤ x.toNat * 2^s.toNat := Nat.mul_le_mul_left _ hab
       _ = 2^s.toNat * x.toNat := Nat.mul_comm _ _

theorem shl_udiv_bound {w : Nat} (x s b : BitVec w)
    (hw : s.toNat < w) (h : (BitVec.twoPow w s.toNat).ule b = true) :
    ((x <<< s)/b).toNat ≤ x.toNat := by
  have hab : 2^s.toNat ≤ b.toNat := by
    have := of_decide_eq_true h
    simpa only [BitVec.toNat_twoPow_of_lt hw] using this
  simp only [BitVec.toNat_udiv, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  apply Nat.div_le_of_le_mul
  calc (x.toNat * 2^s.toNat) % 2^w ≤ x.toNat * 2^s.toNat := Nat.mod_le _ _
       _ ≤ x.toNat * b.toNat := Nat.mul_le_mul_left _ hab
       _ = b.toNat * x.toNat := Nat.mul_comm _ _

theorem shift_twoPow {w : Nat} (bit : Nat) (s : BitVec w) :
    (BitVec.twoPow w bit <<< s) = BitVec.twoPow w (bit + s.toNat) := by
  rw [BitVec.shiftLeft_eq', BitVec.shiftLeft_eq_mul_twoPow, BitVec.twoPow_mul_twoPow_eq]

theorem twoPow_le_signmask {w : Nat} (bit : Nat) :
    (BitVec.twoPow w bit).toNat ≤ (BitVec.intMin w).toNat := by
  cases w with
  | zero => simp [Nat.mod_one]
  | succ w =>
    by_cases h : bit < w+1
    · rw [BitVec.toNat_twoPow_of_lt h, BitVec.toNat_intMin_of_pos (by omega)]
      simp only [Nat.add_sub_cancel]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    · rw [BitVec.toNat_twoPow_of_le (by omega)]
      omega

inductive ScaledCmpShape where
  | mulUdiv | mulLshr | shlUdiv

theorem mul_udiv_scalar_bound {w : Nat} (x : LLVM.Int w) (a b : BitVec w)
    (nsw nuw exact : Bool) (h : a.ule b = true) :
    LLVM.Int.udiv (LLVM.Int.mul x (.val a) nsw nuw) (.val b) exact = .poison ∨
    ∃ v r, x = .val v ∧
      LLVM.Int.udiv (LLVM.Int.mul x (.val a) nsw nuw) (.val b) exact = .val r ∧ r.toNat ≤ v.toNat := by
  rcases mul_scalar_cases x a nsw nuw with hp | ⟨v, hx, hm⟩
  · simp [hp, LLVM.Int.udiv, Id.run]
  · rcases udiv_scalar_cases (LLVM.Int.mul x (.val a) nsw nuw) b exact with hp | ⟨r, hr, hd⟩
    · exact Or.inl hp
    · rw [hm] at hr
      cases hr
      exact Or.inr ⟨v, (v*a)/b, hx, hd, mul_udiv_bound v a b h⟩

theorem mul_lshr_scalar_bound {w : Nat} (x : LLVM.Int w) (a b : BitVec w)
    (nsw nuw exact : Bool) (h : a.ule (BitVec.twoPow w b.toNat) = true) :
    LLVM.Int.lshr (LLVM.Int.mul x (.val a) nsw nuw) (.val b) exact = .poison ∨
    ∃ v r, x = .val v ∧
      LLVM.Int.lshr (LLVM.Int.mul x (.val a) nsw nuw) (.val b) exact = .val r ∧ r.toNat ≤ v.toNat := by
  rcases mul_scalar_cases x a nsw nuw with hp | ⟨v, hx, hm⟩
  · simp [hp, LLVM.Int.lshr, Id.run]
  · rcases lshr_scalar_cases (LLVM.Int.mul x (.val a) nsw nuw) b exact with hp | ⟨r, hr, hw, hd⟩
    · exact Or.inl hp
    · rw [hm] at hr
      cases hr
      exact Or.inr ⟨v, (v*a) >>> b, hx, hd, mul_lshr_bound v a b hw h⟩

theorem shl_udiv_scalar_bound {w : Nat} (x : LLVM.Int w) (a b : BitVec w)
    (nsw nuw exact : Bool) (h : (BitVec.twoPow w a.toNat).ule b = true) :
    LLVM.Int.udiv (LLVM.Int.shl x (.val a) nsw nuw) (.val b) exact = .poison ∨
    ∃ v r, x = .val v ∧
      LLVM.Int.udiv (LLVM.Int.shl x (.val a) nsw nuw) (.val b) exact = .val r ∧ r.toNat ≤ v.toNat := by
  rcases shl_scalar_cases x a nsw nuw with hp | ⟨v, hx, hw, hm⟩
  · simp [hp, LLVM.Int.udiv, Id.run]
  · rcases udiv_scalar_cases (LLVM.Int.shl x (.val a) nsw nuw) b exact with hp | ⟨r, hr, hd⟩
    · exact Or.inl hp
    · rw [hm] at hr
      cases hr
      exact Or.inr ⟨v, (v <<< a)/b, hx, hd, shl_udiv_bound v a b hw h⟩

theorem shift_zero_wrap_poison {w : Nat} (x s : BitVec w) (nsw nuw : Bool)
    (hx : x ≠ 0#w) (hf : nsw = true ∨ nuw = true) (hz : x <<< s = 0#w) :
    LLVM.Int.shl (.val x) (.val s) nsw nuw = .poison := by
  simp only [BitVec.shiftLeft_eq'] at hz
  rcases hf with hf | hf <;>
    simp [LLVM.Int.shl, BitVec.shiftLeft_eq', hz, hx, Ne.symm hx, hf, Id.run, pure]

theorem twoPow_ne_nonPower {w : Nat} (bit : Nat) (c : BitVec w)
    (hc : ¬c.toNat.isPowerOfTwo) (hz : c ≠ 0#w) : BitVec.twoPow w bit ≠ c := by
  intro he
  by_cases h : bit < w
  · apply hc
    refine ⟨bit, ?_⟩
    rw [← he, BitVec.toNat_twoPow_of_lt h]
  · have hge : w ≤ bit := by omega
    have ht := BitVec.toNat_twoPow_of_le hge
    have hn : (BitVec.twoPow w bit) = 0#w := BitVec.eq_of_toNat_eq (by simpa using ht)
    exact hz (he.symm.trans hn)

theorem power_shift_ne_nonPower {w : Nat} (bit : Nat) (s c : BitVec w) (nsw nuw : Bool)
    (hb : bit < w) (hc : ¬c.toNat.isPowerOfTwo)
    (hsafe : nsw = true ∨ nuw = true ∨ BitVec.twoPow w bit = 1#w ∨ c ≠ 0#w) :
    LLVM.Int.shl (.val (BitVec.twoPow w bit)) (.val s) nsw nuw = .poison ∨
    ∃ r, LLVM.Int.shl (.val (BitVec.twoPow w bit)) (.val s) nsw nuw = .val r ∧ r ≠ c := by
  rcases shl_scalar_cases (.val (BitVec.twoPow w bit)) s nsw nuw with hp | ⟨v,hv,hw,hr⟩
  · exact Or.inl hp
  · cases hv
    right
    refine ⟨_, hr, ?_⟩
    by_cases hcz : c ≠ 0#w
    · rw [shift_twoPow]
      exact twoPow_ne_nonPower _ c hc hcz
    · have hcz : c = 0#w := by simpa using hcz
      intro he
      have hz : (BitVec.twoPow w bit <<< s) = 0#w := he.trans hcz
      have hnz : BitVec.twoPow w bit ≠ 0#w := by
        intro hz
        have ht := congrArg BitVec.toNat hz
        simp only [BitVec.toNat_twoPow_of_lt hb, BitVec.toNat_ofNat, Nat.zero_mod] at ht
        exact (Nat.ne_of_gt (Nat.two_pow_pos bit)) ht
      rcases hsafe with hf | hf | h1 | hf
      · have hp := shift_zero_wrap_poison (BitVec.twoPow w bit) s nsw nuw hnz (Or.inl hf) hz
        rw [hr] at hp
        cases hp
      · have hp := shift_zero_wrap_poison (BitVec.twoPow w bit) s nsw nuw hnz (Or.inr hf) hz
        rw [hr] at hp
        cases hp
      · have ht := congrArg BitVec.toNat h1
        rw [BitVec.toNat_twoPow_of_lt hb, BitVec.toNat_one (by omega)] at ht
        have hb0 : bit = 0 := by simpa only [Nat.pow_eq_one, Nat.reduceEqDiff, false_or] using ht
        subst bit
        have ht := congrArg BitVec.toNat hz
        rw [shift_twoPow, Nat.zero_add, BitVec.toNat_twoPow_of_lt hw] at ht
        simp only [BitVec.toNat_ofNat, Nat.zero_mod] at ht
        exact (Nat.ne_of_gt (Nat.two_pow_pos s.toNat)) ht
      · exact hf hcz

inductive PowerShiftSafety where
  | noSignedWrap | noUnsignedWrap | baseOne | nonzeroRHS

end Veir.InstSimplify
