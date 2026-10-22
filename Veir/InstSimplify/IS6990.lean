import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- The outer abs may independently poison on INT_MIN; retaining the earlier abs refines it. -/
def IS6990 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x ← MatchProg.value ty
    let inner ← MatchProg.operation (.llvm .intr__abs) #[x] #[ty]
    let _ ← MatchProg.root (.llvm .intr__abs) inner.res #[ty]
    return inner.res[0]!)
  pure (fun x => x)
theorem IS6990_valid : Pattern.Valid IS6990 := by
  simp only [IS6990]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x
  rintro ip iv ii
  obtain rfl := (abs_iff _ _ _ _).mp ii
  rintro rp rv ri
  obtain rfl := (abs_iff _ _ _ _).mp ri
  cases x with
  | poison => simp [LLVM.Int.abs, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
  | val x =>
    by_cases hi : ip.is_int_min_poison = true ∧ x = BitVec.intMin w
    · simp [LLVM.Int.abs, hi, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
    · by_cases ho : rp.is_int_min_poison = true ∧ (if x.msb then -x else x) = BitVec.intMin w
      · simp [LLVM.Int.abs, hi, ho, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
      · simpa [LLVM.Int.abs, hi, ho, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure] using abs_bits_idem x
end Veir.InstSimplify
