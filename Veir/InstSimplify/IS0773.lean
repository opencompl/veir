import Veir.InstSimplify.LogicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS0773

/-- Scalar LLVM `sub nuw 0, X` simplifies to zero. -/
def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty (0)
      let _ ← MatchProg.root (.llvm .sub) #[c,x] #[ty] (fun p => p.nuw)
      return c)
    pure (fun x => x)

theorem pattern_valid : Pattern.Valid pattern := by
  simp only [pattern, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hp hi hz
  obtain rfl := matched_bit_constant_eq _ cp (0) cv hc hz
  obtain rfl := (sub_iff w p _ x v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.sub, isRefinedBy, Id.run, pure, hp]
  all_goals grind [BitVec.uaddOverflow, BitVec.usubOverflow, BitVec.toNat_ofInt, BitVec.toNat_ofNat]

end Veir.InstSimplify.IS0773
