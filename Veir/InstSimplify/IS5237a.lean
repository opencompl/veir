import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
/-- Pinned upstream scalar integer rule; arbitrary result/operand width. -/
def IS5237a : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let c ← MatchProg.value cty
    let p ← matchPoison ty
    let x ← MatchProg.value ty
    let _ ← MatchProg.root (.llvm .select) #[c,p,x] #[ty]
    return x)
  pure
  (fun x => x)

theorem IS5237a_valid : Pattern.Valid IS5237a := by
  simp only [IS5237a, matchIntConstant, matchPoison]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ _ ⟨cw,cs⟩ rfl hc
  have : cw = 1 := by simpa using hc
  subst cw
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro c pp pv pi
  obtain rfl := (poison_iff _ _ _).mp pi
  intro x rp rv ri
  obtain rfl := (select_iff _ _ _ _ _ _).mp ri
  rcases int1_cases c with rfl | rfl | rfl <;> cases x <;> simp [LLVM.Int.select, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
end Veir.InstSimplify
