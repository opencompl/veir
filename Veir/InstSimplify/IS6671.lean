import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- Pinned LLVM IS6671: cancellation of two identical bit permutations. -/
def IS6671 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x ← MatchProg.value ty
    let inner ← MatchProg.operation (.llvm .intr__bitreverse) #[x] #[ty]
    let _ ← MatchProg.root (.llvm .intr__bitreverse) inner.res #[ty]
    return x)
  pure (fun x => x)

theorem IS6671_valid : Pattern.Valid IS6671 := by
  simp only [IS6671]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x
  rintro ip iv ii
  obtain rfl := (bitreverse_iff _ _ _ _).mp ii
  rintro rp rv ri
  obtain rfl := (bitreverse_iff _ _ _ _).mp ri
  cases x <;> simp [LLVM.Int.bitreverse, BitVec.reverse_reverse_eq, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
end Veir.InstSimplify
