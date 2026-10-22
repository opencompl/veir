import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem ctlz_lshr_negative_refines (w : Nat) (a : BitVec w) (ha : a.msb = true)
    (x : LLVM.Int w) (exact zp : Bool) :
    RuntimeValue.int w (LLVM.Int.ctlz (LLVM.Int.lshr (.val a) x exact) zp) ⊒ .int w x := by
  cases x with
  | poison => simp [LLVM.Int.lshr, LLVM.Int.ctlz, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    have hc : LLVM.Int.lshr (.val a) (.val x) exact = .poison ∨
        LLVM.Int.lshr (.val a) (.val x) exact = .val (a >>> x) := by
      simp only [LLVM.Int.lshr, Id.run, pure]
      repeat' split <;> simp_all
      all_goals grind
    rcases hc with hc | hc
    · rw [hc]
      simp [LLVM.Int.ctlz, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    · have hs : x.toNat < w := by
        by_cases hlt : x.toNat < w
        · exact hlt
        · have hg : BitVec.ofNat w w ≤ x := by
            simp only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_two_pow_self]
            omega
          have he := hc
          simp [LLVM.Int.lshr, hg, Id.run, pure] at he
      have hbit : (a >>> x).getLsbD (w-1-x.toNat) = true := by
        simp only [BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight]
        rw [show x.toNat + (w-1-x.toNat) = w-1 by omega]
        simpa only [← BitVec.msb_eq_getLsbD_last] using ha
      have hn : (a >>> x) ≠ 0#w := by intro he; simp [he] at hbit
      rw [hc]
      have hf : LLVM.Int.ctlz (.val (a >>> x)) zp = .val x := by
        simp only [LLVM.Int.ctlz, Id.run, pure]
        rw [if_neg (by intro h; exact hn h.2)]
        exact congrArg LLVM.Int.val (clz_negative_lshr a x ha hs)
      rw [hf]
      exact RuntimeValue.isRefinedBy_refl _

/-- Source m_Negative matches any signed-negative APInt, not only all-ones. -/
def IS7002 (n : Int) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← matchBitConstant ty n
    MatchProg.matchNative ty (fun t => match t.val with | .integerType t => (BitVec.ofInt t.bitwidth n).msb | _ => false)
    let x ← MatchProg.value ty
    let shifted ← MatchProg.operation (.llvm .lshr) #[a,x] #[ty]
    let _ ← MatchProg.root (.llvm .intr__ctlz) shifted.res #[ty]
    return x)
  pure (fun x => x)
theorem IS7002_valid (n : Int) : Pattern.Valid (IS7002 n) := by
  simp only [IS7002, matchBitConstant]
  provePuddleValid
  rintro ⟨w,s⟩ cp cv ci
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x
  rintro sp sv si rp rv ri hc hn
  obtain rfl := matched_bit_constant_eq _ _ _ _ ci hc
  have hn : (BitVec.ofInt w n).msb = true := by simpa [TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of] using hn
  obtain rfl := (lshr_iff _ _ _ _ _).mp si
  obtain rfl := (ctlz_iff _ _ _ _).mp ri
  exact ctlz_lshr_negative_refines _ _ hn _ _ _
end Veir.InstSimplify
