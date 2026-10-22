import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
def IS7216 (signed : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x ← MatchProg.value ty
    let z ← matchBitConstant ty 0
    let _ ← MatchProg.root (.llvm (if signed then Llvm.intr__ssub__sat else .intr__usub__sat)) #[x,z] #[ty]
    return x)
  pure (fun x => x)
theorem IS7216_valid (signed : Bool) : Pattern.Valid (IS7216 signed) := by
  cases signed
  all_goals
    simp only [IS7216, Bool.false_eq_true, ↓reduceIte, matchBitConstant]
    provePuddleValid
    rintro ⟨w,s⟩
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x
    rintro cp cv ci rp rv ri hc
    obtain rfl := matched_bit_constant_eq _ _ _ _ ci hc
    first
    | obtain rfl := (ssubSat_iff _ _ _ _ _).mp ri
    | obtain rfl := (usubSat_iff _ _ _ _ _).mp ri
    cases x <;> simp [LLVM.Int.saddSat, LLVM.Int.uaddSat, LLVM.Int.ssubSat, LLVM.Int.usubSat,
      BitVec.saddOverflow_eq, BitVec.ssubOverflow_eq, BitVec.uaddOverflow, BitVec.usubOverflow, Nat.not_le.mpr (BitVec.isLt _),
      RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
end Veir.InstSimplify
