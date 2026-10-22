import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
def IS7188 (swap : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x ← MatchProg.value ty
    let z ← matchBitConstant ty (-1)
    let _ ← MatchProg.root (.llvm Llvm.intr__uadd__sat) (if swap then #[z,x] else #[x,z]) #[ty]
    return z)
  pure (fun x => x)
theorem IS7188_valid (swap : Bool) : Pattern.Valid (IS7188 swap) := by
  cases swap
  all_goals
    simp only [IS7188, Bool.false_eq_true, ↓reduceIte, matchBitConstant]
    provePuddleValid
    rintro ⟨w,s⟩
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x
    rintro cp cv ci rp rv ri hc
    obtain rfl := matched_bit_constant_eq _ _ _ _ ci hc
    first
    | obtain rfl := (uaddSat_iff _ _ _ _ _).mp ri
    cases x with
    | poison => simp [LLVM.Int.uaddSat, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val x =>
      by_cases hx : x = 0
      · subst x
        simp [LLVM.Int.uaddSat, const_negOne, BitVec.uaddOverflow,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure, Nat.not_le.mpr (BitVec.isLt _)]
      · have hxnat : x.toNat > 0 := by
          have : x.toNat ≠ 0 := by
            intro hzero
            apply hx
            apply BitVec.eq_of_toNat_eq
            simpa using hzero
          omega
        have hpow := Nat.two_pow_pos w
        have hleft : 2^w ≤ x.toNat + (BitVec.allOnes w).toNat := by
          simp only [BitVec.toNat_allOnes]; omega
        have hright : 2^w ≤ (BitVec.allOnes w).toNat + x.toNat := by omega
        simp [LLVM.Int.uaddSat, const_negOne, BitVec.uaddOverflow,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure, (by simpa only [BitVec.toNat_allOnes] using hleft), (by simpa only [BitVec.toNat_allOnes] using hright)]
end Veir.InstSimplify
