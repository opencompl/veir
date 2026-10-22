import Veir.InstSimplify.ArithmeticExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1168
private theorem divisor_pow_two {c w : Nat} (h : c ∣ 2^w) : ∃ k : Nat, c = 2^k := by
  induction w generalizing c with
  | zero =>
    have hc : c = 1 := Nat.eq_one_of_dvd_one (by simpa using h)
    exact ⟨0, hc⟩
  | succ w ih =>
    rw [Nat.pow_succ, Nat.mul_comm] at h
    obtain ⟨a,b,ha,hb,heq⟩ := Nat.dvd_mul.mp h
    have ha0 : a ≠ 0 := by intro h0; subst a; simp at ha
    have ha2 : a ≤ 2 := Nat.le_of_dvd (by decide) ha
    have ha12 : a = 1 ∨ a = 2 := by omega
    obtain ⟨k,hk⟩ := ih hb
    rcases ha12 with rfl | rfl
    · refine ⟨k, ?_⟩
      simp only [Nat.one_mul] at heq
      omega
    · refine ⟨k+1, ?_⟩
      rw [Nat.pow_succ, Nat.mul_comm]
      rw [← hk]
      exact heq.symm
private theorem not_pow_two_iff_not_divisor {c w : Nat} (hc : c < 2^w) :
    (¬∃ k : Nat, c = 2^k) ↔ ¬c ∣ 2^w := by
  constructor
  · intro hn hd
    exact hn (divisor_pow_two hd)
  · rintro hn ⟨k,rfl⟩
    have hk : k ≤ w := by
      by_cases h : k ≤ w
      · exact h
      · have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show w ≤ k by omega)
        omega
    exact hn (Nat.pow_dvd_pow 2 hk)
private theorem noUnsignedWrap_of_noSignedWrap (x c : BitVec w)
    (hs : ¬x.smulOverflow c) (he : (x*c)%c=0)
    (hc : c ≠ 0) (hnd : ¬c.toNat ∣ 2^w) : ¬x.umulOverflow c := by
  have hw : 0 < w := by
    by_cases h : 0 < w
    · exact h
    · have h0 : w = 0 := by omega
      subst w
      simp [BitVec.of_length_zero] at hc
  have hpdouble : (2^(w-1) : Int) + 2^(w-1) = 2^w := by
    exact_mod_cast Nat.two_pow_pred_add_two_pow_pred hw
  have hcpos : 0 < c.toNat := by
    have hcz : c.toNat ≠ 0 := by intro h; apply hc; apply BitVec.eq_of_toNat_eq; simpa using h
    omega
  have hrem := congrArg BitVec.toNat he
  simp only [BitVec.toNat_umod] at hrem
  change (x*c).toNat % c.toNat = 0 at hrem
  have hd : c.toNat ∣ (x*c).toNat := Nat.dvd_of_mod_eq_zero hrem
  have hdi : (c.toNat : Int) ∣ ((x*c).toNat : Int) := Int.natCast_dvd_natCast.mpr hd
  have hprod := BitVec.toInt_mul_of_not_smulOverflow hs
  have hx := BitVec.toInt_eq_msb_cond x
  have hcc := BitVec.toInt_eq_msb_cond c
  have hr := BitVec.toInt_eq_msb_cond (x*c)
  have hrlo := BitVec.le_toInt (x*c)
  have hrhi := BitVec.toInt_lt (x := x*c)
  have hrnat := (x*c).isLt
  have hxn := x.isLt
  have hcn := c.isLt
  have hp : (0 : Int) < 2^w := by exact Int.pow_pos (by decide)
  have hp2 : (0 : Int) < 2^(w-1) := by exact Int.pow_pos (by decide)
  have hhalf : (2^(w-1) : Int) ≤ 2^w := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) (show w-1 ≤ w by omega)
  norm_cast at hp hp2 hhalf hrlo hrhi
  by_cases hx0 : x = 0
  · subst x; simp [BitVec.umulOverflow]
  have hxpos : 0 < x.toNat := by
    have hxz : x.toNat ≠ 0 := by intro h; apply hx0; apply BitVec.eq_of_toNat_eq; simpa using h
    omega
  by_cases hcx : x.msb = true <;> by_cases hcy : c.msb = true
  · have hxneg : x.toInt < 0 := BitVec.toInt_neg_of_msb_true hcx
    have hcneg : c.toInt < 0 := BitVec.toInt_neg_of_msb_true hcy
    have hpos := Int.mul_pos_of_neg_of_neg hxneg hcneg
    have hrpos : 0 < (x*c).toNat := by
      by_cases hz : (x*c).toNat = 0
      · have hz' : x*c=0 := by apply BitVec.eq_of_toNat_eq; simpa using hz
        simp [hz'] at hprod
        omega
      · omega
    have hrmsb : (x*c).msb = false := by
      by_cases hm : (x*c).msb = true
      · have := BitVec.toInt_neg_of_msb_true hm; omega
      · simpa using hm
    simp only [hcy, Bool.true_eq, reduceIte] at hcc
    simp only [hrmsb, Bool.false_eq_true, reduceIte] at hr
    have hcle := Nat.le_of_dvd hrpos hd
    have hsign : (2^(w-1) : Int) ≤ c.toNat := by
      have hh := BitVec.toNat_ge_of_msb_true hcy
      exact_mod_cast hh
    simp only [Int.natCast_pow, Int.cast_ofNat_Int] at *
    omega
  · have hxneg : x.toInt < 0 := BitVec.toInt_neg_of_msb_true hcx
    have hcf : c.msb = false := by simp_all
    have hcint : c.toInt = c.toNat := BitVec.toInt_eq_toNat_of_msb hcf
    have hcp : 0 < c.toInt := by omega
    have hneg := Int.mul_neg_of_neg_of_pos hxneg hcp
    have hrmsb : (x*c).msb = true := by
      by_cases hm : (x*c).msb = true
      · exact hm
      · have := BitVec.toInt_nonneg_of_msb_false (by simpa using hm); omega
    simp only [hrmsb, reduceIte] at hr
    have hdprod : (c.toNat : Int) ∣ (x*c).toInt := by
      rw [hprod, hcint]
      exact Int.dvd_mul_left _ _
    have hdm := Int.dvd_sub hdi hdprod
    have hEq : ((x*c).toNat : Int) - (x*c).toInt = (2^w : Nat) := by omega
    rw [hEq] at hdm
    have hmi : (c.toNat : Int) ∣ (2^w : Nat) := hdm
    have hmn : c.toNat ∣ 2^w := Int.natCast_dvd_natCast.mp hmi
    exact False.elim (hnd hmn)
  · have hxf : x.msb = false := by simp_all
    have hxint : x.toInt = x.toNat := BitVec.toInt_eq_toNat_of_msb hxf
    have hcneg : c.toInt < 0 := BitVec.toInt_neg_of_msb_true hcy
    have hxp : 0 < x.toInt := by omega
    have hneg := Int.mul_neg_of_pos_of_neg hxp hcneg
    have hrmsb : (x*c).msb = true := by
      by_cases hm : (x*c).msb = true
      · exact hm
      · have := BitVec.toInt_nonneg_of_msb_false (by simpa using hm); omega
    simp only [hcy, hrmsb, reduceIte] at hcc hr
    have hmul : x.toInt*c.toInt ≤ c.toInt := by
      have hxone : 1 ≤ x.toInt := by omega
      have := Int.mul_le_mul_of_nonpos_right hxone (by omega : c.toInt ≤ 0)
      simpa using this
    have hrpos : 0 < (x*c).toNat := by simp only [Int.natCast_pow, Int.cast_ofNat_Int] at *; omega
    have hcle := Nat.le_of_dvd hrpos hd
    have hre : (x*c).toNat = c.toNat := by norm_cast at hr hcc; omega
    have hre' : (x*c).toInt = c.toInt := by rw [hre] at hr; omega
    have hcne : c.toInt ≠ 0 := by omega
    have hxe : x.toInt = 1 := by
      apply Int.eq_of_mul_eq_mul_right hcne
      simpa [hre'] using hprod.symm
    have hxn1 : x.toNat = 1 := by omega
    simp only [BitVec.umulOverflow, hxn1, Nat.one_mul, decide_eq_true_eq]
    omega
  · have hxf : x.msb = false := by simp_all
    have hcf : c.msb = false := by simp_all
    have hxint := BitVec.toInt_eq_toNat_of_msb hxf
    have hcint := BitVec.toInt_eq_toNat_of_msb hcf
    have hxnon : 0 ≤ x.toInt := by omega
    have hcnon : 0 ≤ c.toInt := by omega
    have hnon := Int.mul_nonneg hxnon hcnon
    have hrmsb : (x*c).msb = false := by
      by_cases hm : (x*c).msb = true
      · have := BitVec.toInt_neg_of_msb_true hm; omega
      · simpa using hm
    have hrint := BitVec.toInt_eq_toNat_of_msb hrmsb
    have hnat : (x*c).toNat = x.toNat*c.toNat := by
      rw [hxint,hcint,hrint] at hprod
      exact_mod_cast hprod
    simp only [BitVec.umulOverflow, decide_eq_true_eq]
    omega
private theorem noSignedWrap_of_noUnsignedWrap (x c : BitVec w)
    (hu : ¬x.umulOverflow c) (he : (x*c).smod c=0)
    (hc : c ≠ 0) (hnd : ¬c.toNat ∣ 2^w) : ¬x.smulOverflow c := by
  have hcpos : 0 < c.toNat := by
    have hcz : c.toNat ≠ 0 := by intro h; apply hc; apply BitVec.eq_of_toNat_eq; simpa using h
    omega
  have hcn := c.isLt
  have hxn := x.isLt
  have hw : 1 < w := by
    by_cases h : 1 < w
    · exact h
    · have hww : w = 0 ∨ w = 1 := by omega
      rcases hww with rfl | rfl
      · simp at hcn; omega
      · have hcone : c.toNat = 1 := by simp at hcn; omega
        simp [hcone] at hnd
  have hpdouble := Nat.two_pow_pred_add_two_pow_pred (show 0<w by omega)
  have hnat := BitVec.toNat_mul_of_not_umulOverflow hu
  have hrnat := (x*c).isLt
  have hrem := congrArg BitVec.toInt he
  simp only [BitVec.toInt_smod] at hrem
  have hz : (0 : BitVec w).toInt = 0 := by simp
  rw [hz] at hrem
  have hdi : c.toInt ∣ (x*c).toInt := Int.dvd_of_fmod_eq_zero hrem
  have hr := BitVec.toInt_eq_msb_cond (x*c)
  have hrlo := BitVec.le_toInt (x*c)
  have hrhi := BitVec.toInt_lt (x := x*c)
  by_cases hcy : c.msb = true
  · have hcH := BitVec.toNat_ge_of_msb_true hcy
    have hxlt : x.toNat < 2 := by
      by_cases hx2 : 2 ≤ x.toNat
      · have hm := Nat.mul_le_mul hx2 hcH
        omega
      · omega
    have hxx : x.toNat = 0 ∨ x.toNat = 1 := by omega
    rcases hxx with hxx | hxx
    · have hx0 : x = 0 := by apply BitVec.eq_of_toNat_eq; simpa using hxx
      subst x
      have hpow : (0 : Int) < 2^(w-1) := Int.pow_pos (by decide)
      simp [BitVec.smulOverflow]; omega
    · have hx1 : x = 1 := by
        apply BitVec.eq_of_toNat_eq
        simpa [BitVec.toNat_one (show 0<w by omega)] using hxx
      have hxint : x.toInt = 1 := by rw [hx1]; simp [BitVec.toInt_one, hw]
      have hl := BitVec.le_toInt c
      have hh := BitVec.toInt_lt (x := c)
      simp only [BitVec.smulOverflow, hxint, Int.one_mul, Bool.or_eq_true, decide_eq_true_eq, not_or]
      omega
  · have hcf : c.msb = false := by simp_all
    have hcint := BitVec.toInt_eq_toNat_of_msb hcf
    by_cases hcx : x.msb = true
    · have hxH := BitVec.toNat_ge_of_msb_true hcx
      have hc2 : 2 ≤ c.toNat := by
        by_cases hc1 : c.toNat = 1
        · simp [hc1] at hnd
        · omega
      have hm := Nat.mul_le_mul hxH hc2
      omega
    · have hxf : x.msb = false := by simp_all
      have hxint := BitVec.toInt_eq_toNat_of_msb hxf
      by_cases hrm : (x*c).msb = true
      · simp only [hrm, reduceIte] at hr
        rw [hcint] at hdi
        have hprodDiv : (c.toNat : Int) ∣ ((x*c).toNat : Int) := by
          rw [hnat, Int.natCast_mul]
          exact Int.dvd_mul_left _ _
        have hdm := Int.dvd_sub hprodDiv hdi
        have hEq : ((x*c).toNat : Int) - (x*c).toInt = (2^w : Nat) := by omega
        rw [hEq] at hdm
        exact False.elim (hnd (Int.natCast_dvd_natCast.mp hdm))
      · have hrf : (x*c).msb = false := by simpa using hrm
        have hrint := BitVec.toInt_eq_toNat_of_msb hrf
        have heq : x.toInt*c.toInt = (x*c).toInt := by
          rw [hxint,hcint,hrint,hnat]
          simp
        simp only [BitVec.smulOverflow, heq, Bool.or_eq_true, decide_eq_true_eq, not_or]
        omega
private theorem udiv_mul_cancel (x y : BitVec w) (h : ¬x.umulOverflow y) (hy : y ≠ 0) : (x*y)/y=x := by
  apply BitVec.eq_of_toNat_eq
  have hy' : 0 < y.toNat := by
    have : y.toNat ≠ 0 := by intro h; apply hy; apply BitVec.eq_of_toNat_eq; simpa using h
    omega
  simp only [BitVec.toNat_udiv, BitVec.toNat_mul_of_not_umulOverflow h]
  exact Nat.mul_div_cancel x.toNat hy'
private theorem sdiv_mul_cancel (x y : BitVec w) (h : ¬x.smulOverflow y) (hy : y ≠ 0) : (x*y).sdiv y=x := by
  have hy' : y.toInt ≠ 0 := by intro he; apply hy; apply BitVec.eq_of_toInt_eq; simpa using he
  have hs : (x*y).sdiv y = BitVec.ofInt w ((x*y).toInt.tdiv y.toInt) := by
    apply BitVec.eq_of_toInt_eq
    simp only [BitVec.toInt_sdiv, BitVec.toInt_ofInt]
  rw [hs, BitVec.toInt_mul_of_not_smulOverflow h, Int.mul_tdiv_cancel _ hy', BitVec.ofInt_toInt]
/-- The computable non-divisor guard is exactly the source non-power-of-two test,
    after the earlier zero-divisor case has been handled. -/
theorem guard_equivalent_to_source (c : BitVec w) :
    (c ≠ 0 ∧ ¬∃ k : Nat, c.toNat = 2^k) ↔ (c ≠ 0 ∧ ¬c.toNat ∣ 2^w) := by
  rw [not_pow_two_iff_not_divisor c.isLt]

private theorem refines_udiv (x : LLVM.Int w) (c : BitVec w) (nu : Bool)
    (hc : c ≠ 0) (hnd : ¬c.toNat ∣ 2^w) :
    RuntimeValue.int w (LLVM.Int.udiv (LLVM.Int.mul x (.val c) true nu) (.val c) true) ⊒ .int w x := by
  cases x <;> simp [LLVM.Int.mul, LLVM.Int.udiv, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  grind [noUnsignedWrap_of_noSignedWrap, udiv_mul_cancel]

/-- udiv exact (mul nsw X,C),C → X for a non-power-of-two divisor. -/
def pattern_udiv (n : Int) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty n
      let mul ← MatchProg.operation (.llvm .mul) #[x,c] #[ty] (fun p => p.nsw)
      let _ ← MatchProg.root (.llvm .udiv) #[mul.res[0]!,c] #[ty] (fun p => p.exact)
      MatchProg.matchNative ty (fun t => match t.val with
        | .integerType it => (BitVec.ofInt it.bitwidth n != 0) &&
            !decide ((BitVec.ofInt it.bitwidth n).toNat ∣ 2^it.bitwidth)
        | _ => false)
      return x)
    pure (fun x => x)

theorem pattern_udiv_valid (n : Int) : Pattern.Valid (pattern_udiv n) := by
  simp only [pattern_udiv, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc mp mv hp hm rp rv he hr hca hg
  obtain rfl := matched_bit_constant_eq _ cp n cv hc hca
  obtain rfl := (mul_iff w mp x _ mv).mp hm
  obtain ⟨hu,rfl⟩ := (udiv_iff w rp _ _ rv).mp hr
  change ((BitVec.ofInt w n != 0) && !decide ((BitVec.ofInt w n).toNat ∣ 2^w)) = true at hg
  have hg' : BitVec.ofInt w n ≠ 0 ∧ ¬(BitVec.ofInt w n).toNat ∣ 2^w := by simpa using hg
  rw [hp,he]
  exact refines_udiv _ _ _ hg'.1 hg'.2

private theorem refines_sdiv (x : LLVM.Int w) (c : BitVec w) (ns : Bool)
    (hc : c ≠ 0) (hnd : ¬c.toNat ∣ 2^w) :
    RuntimeValue.int w (LLVM.Int.sdiv (LLVM.Int.mul x (.val c) ns true) (.val c) true) ⊒ .int w x := by
  cases x <;> simp [LLVM.Int.mul, LLVM.Int.sdiv, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  grind [noSignedWrap_of_noUnsignedWrap, sdiv_mul_cancel]

/-- sdiv exact (mul nuw X,C),C → X for a non-power-of-two divisor. -/
def pattern_sdiv (n : Int) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty n
      let mul ← MatchProg.operation (.llvm .mul) #[x,c] #[ty] (fun p => p.nuw)
      let _ ← MatchProg.root (.llvm .sdiv) #[mul.res[0]!,c] #[ty] (fun p => p.exact)
      MatchProg.matchNative ty (fun t => match t.val with
        | .integerType it => (BitVec.ofInt it.bitwidth n != 0) &&
            !decide ((BitVec.ofInt it.bitwidth n).toNat ∣ 2^it.bitwidth)
        | _ => false)
      return x)
    pure (fun x => x)

theorem pattern_sdiv_valid (n : Int) : Pattern.Valid (pattern_sdiv n) := by
  simp only [pattern_sdiv, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc mp mv hp hm rp rv he hr hca hg
  obtain rfl := matched_bit_constant_eq _ cp n cv hc hca
  obtain rfl := (mul_iff w mp x _ mv).mp hm
  obtain ⟨hu,rfl⟩ := (sdiv_iff w rp _ _ rv).mp hr
  change ((BitVec.ofInt w n != 0) && !decide ((BitVec.ofInt w n).toNat ∣ 2^w)) = true at hg
  have hg' : BitVec.ofInt w n ≠ 0 ∧ ¬(BitVec.ofInt w n).toNat ∣ 2^w := by simpa using hg
  rw [hp,he]
  exact refines_sdiv _ _ _ hg'.1 hg'.2
end Veir.InstSimplify.IS1168
