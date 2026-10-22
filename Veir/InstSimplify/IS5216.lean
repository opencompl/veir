import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- Pinned upstream i1 select rule IS5216, including commuted bitwise and short circuit select forms. -/
def IS5216  : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let c0 ← matchIntConstant ty 0
    let _ ← MatchProg.root (.llvm .select) #[x,x,c0] #[ty]
    return x)
  pure (fun x => x)

theorem IS5216_valid  : Pattern.Valid (IS5216 ) := by
  simp only [IS5216, matchIntConstant]
  provePuddleValid
  rintro _ ⟨w,s⟩ rfl hw
  have : w = 1 := by simpa using hw
  subst w
  try simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x
  rintro c0p c0v c0h c0i
  obtain rfl := (matched_constant_iff _ _ _ c0h _).mp c0i
  rintro rp rv ri
  obtain rfl := (select_iff _ _ _ _ _ _).mp ri
  rcases int1_cases x with rfl | rfl | rfl <;>
    all_goals simp [LLVM.Int.select, LLVM.Int.and, LLVM.Int.or, LLVM.Int.xor, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
end Veir.InstSimplify
