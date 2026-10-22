import Veir.InstSimplify.LogicSupport
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS2078
def pattern : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let p ← matchPoison ty
    let _ ← MatchProg.root (.llvm .and) #[x,p] #[ty]
    return p) pure (fun x => x)
theorem valid : Pattern.Valid pattern := by
  simp only [pattern,matchPoison]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x pp pv hp
  obtain rfl := (poison_iff _ _ _).mp hp
  intro rp rv hr
  obtain rfl := (and_iff _ _ _ _ _).mp hr
  cases x <;> simp [LLVM.Int.and, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
end Veir.InstSimplify.IS2078
