import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
/-- Both data operands have the same constant APInt; any shift including poison is allowed. -/
def IS7489 (left : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← matchBitConstant ty (-1)
    let b ← matchBitConstant ty (-1)
    let c ← MatchProg.value ty
    let _ ← MatchProg.root (.llvm (match left with | true => Llvm.intr__fshl | false => .intr__fshr)) #[a,b,c] #[ty]
    return a)
  pure (fun a => a)
theorem IS7489_valid (left : Bool) : Pattern.Valid (IS7489 left) := by
  cases left
  all_goals
    simp only [IS7489, matchBitConstant]
    provePuddleValid
    rintro ⟨w,s⟩ ap av ai bp bv bi
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro c
    rintro rp rv ri ha hb
    obtain rfl := matched_bit_constant_eq _ _ _ _ ai ha
    obtain rfl := matched_bit_constant_eq _ _ _ _ bi hb
    first
    | obtain rfl := (fshl_iff _ _ _ _ _ _).mp ri
    | obtain rfl := (fshr_iff _ _ _ _ _ _).mp ri
    cases c with
    | poison => simp [LLVM.Int.fshl, LLVM.Int.fshr, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    | val c =>
      simp [LLVM.Int.fshl, LLVM.Int.fshr, RuntimeValue.isRefinedBy, isRefinedBy, Id.run,
        const_negOne, funnel_left_ones, funnel_right_ones, BitVec.extractLsb'_zero]
end Veir.InstSimplify
