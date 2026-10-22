import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
/-- Pinned upstream scalar integer rule; arbitrary result/operand width. -/
def IS5137 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let c ← matchIntConstant cty 1
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let _ ← MatchProg.root (.llvm .select) #[c,x,y] #[ty]
    return x)
  pure
  (fun x => x)

theorem IS5137_valid : Pattern.Valid IS5137 := by
  simp only [IS5137, matchIntConstant, matchPoison]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ _ ⟨cw,cs⟩ rfl hc
  have : cw = 1 := by simpa using hc
  subst cw
  rintro cp cv ch ci
  obtain rfl := (matched_constant_iff _ _ _ ch _).mp ci
  intro x y rp rv ri
  obtain rfl := (select_iff _ _ _ _ _ _).mp ri
  cases x <;> cases y <;> simp [LLVM.Int.select, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
end Veir.InstSimplify
