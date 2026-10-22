import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem cttz_shl_one_refines (w : Nat) (x : LLVM.Int w) (nsw nuw zp : Bool) :
    RuntimeValue.int w (LLVM.Int.cttz (LLVM.Int.shl (.val (1#w)) x nsw nuw) zp) ⊒ .int w x := by
  cases x with
  | poison => simp [LLVM.Int.shl, LLVM.Int.cttz, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    have hc : LLVM.Int.shl (.val (1#w)) (.val x) nsw nuw = .poison ∨
        LLVM.Int.shl (.val (1#w)) (.val x) nsw nuw = .val (1#w <<< x) := by
      simp only [LLVM.Int.shl, Id.run, pure]
      repeat' split <;> simp_all
      all_goals grind
    rcases hc with hc | hc
    · rw [hc]
      simp [LLVM.Int.cttz, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    · have hs : x.toNat < w := by
        by_cases hlt : x.toNat < w
        · exact hlt
        · have hg : BitVec.ofNat w w ≤ x := by
            simp only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_two_pow_self]
            omega
          have he := hc
          simp [LLVM.Int.shl, hg, Id.run, pure] at he
      have hbit : (1#w <<< x).getLsbD x.toNat = true := by
        simp [BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft, hs, show 0 < w by omega]
      have hn : (1#w <<< x) ≠ 0#w := by
        intro he; simp [he] at hbit
      rw [hc]
      have hnn : (1#w <<< x.toNat) ≠ 0#w := hn
      have hctzn : (1#w <<< x.toNat).ctz = x := ctz_one_shift x hs
      have hf : LLVM.Int.cttz (.val (1#w <<< x)) zp = .val x := by
        simp only [LLVM.Int.cttz, Id.run, pure]
        rw [if_neg (by intro h; exact hnn h.2)]
        exact congrArg LLVM.Int.val hctzn
      rw [hf]
      exact RuntimeValue.isRefinedBy_refl _

def IS6996 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let one ← matchBitConstant ty 1
    let x ← MatchProg.value ty
    let shifted ← MatchProg.operation (.llvm .shl) #[one,x] #[ty]
    let _ ← MatchProg.root (.llvm .intr__cttz) shifted.res #[ty]
    return x)
  pure (fun x => x)
theorem IS6996_valid : Pattern.Valid IS6996 := by
  simp only [IS6996, matchBitConstant]
  provePuddleValid
  rintro ⟨w,s⟩ cp cv ci
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x
  rintro sp sv si rp rv ri hc
  obtain rfl := matched_bit_constant_eq _ _ _ _ ci hc
  obtain rfl := (shl_iff _ _ _ _ _).mp si
  obtain rfl := (cttz_iff _ _ _ _).mp ri
  exact cttz_shl_one_refines _ _ _ _ _
end Veir.InstSimplify
