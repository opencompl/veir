import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
/-- Integer min/max idempotence, all four scalar intrinsic operations. -/
def IS7066 (kind : MinMaxKind) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x ← MatchProg.value ty
    let _ ← MatchProg.root (.llvm kind.op) #[x,x] #[ty]
    return x)
  pure (fun x => x)
theorem IS7066_valid (kind : MinMaxKind) : Pattern.Valid (IS7066 kind) := by
  cases kind <;> simp only [IS7066, MinMaxKind.op] <;> provePuddleValid
  all_goals
    rintro ⟨w,s⟩
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    intro x
    rintro rp rv ri
    first
    | obtain rfl := (smax_iff _ _ _ _ _).mp ri
    | obtain rfl := (smin_iff _ _ _ _ _).mp ri
    | obtain rfl := (umax_iff _ _ _ _ _).mp ri
    | obtain rfl := (umin_iff _ _ _ _ _).mp ri
    cases x <;>
    simp [MinMaxKind.eval, LLVM.Int.smax, LLVM.Int.smin, LLVM.Int.umax, LLVM.Int.umin,
      RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
end Veir.InstSimplify
