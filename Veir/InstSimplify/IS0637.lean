import Veir.InstSimplify.LogicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS0637

/-- Scalar LLVM `add nuw X, -1` simplifies to the all-ones operand. -/
def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty (-1)
      let _ ← MatchProg.root (.llvm .add) #[x,c] #[ty] (fun p => p.nuw)
      return c)
    pure (fun x => x)

theorem pattern_valid : Pattern.Valid pattern := by
  simp only [pattern, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hp hi hz
  obtain rfl := matched_bit_constant_eq _ cp (-1) cv hc hz
  obtain rfl := (add_iff w p x _ v).mp hi
  have negone : BitVec.ofInt w (-1) = BitVec.allOnes w := by
    rw [BitVec.ofInt_neg]
    simp [BitVec.neg_one_eq_allOnes]
  have noOverflow (a : BitVec w) (h : a.uaddOverflow (BitVec.allOnes w) = false) : a = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.uaddOverflow] at h
    have := Nat.two_pow_pos w
    simp
    omega
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.add, isRefinedBy, Id.run, pure, hp, negone]
  grind

end Veir.InstSimplify.IS0637
