import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
/-- Pinned upstream scalar integer rule; arbitrary result/operand width. -/
def IS5126 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let c ← matchPoison cty
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let _ ← MatchProg.root (.llvm .select) #[c,x,y] #[ty]
    return ty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun x => x)

theorem IS5126_valid : Pattern.Valid IS5126 := by
  simp only [IS5126, matchIntConstant, matchPoison]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ _ ⟨cw,cs⟩ rfl hc
  have : cw = 1 := by simpa using hc
  subst cw
  rintro cp cv ci
  obtain rfl := (poison_iff _ _ _).mp ci
  intro x y rp rv ri
  obtain rfl := (select_iff _ _ _ _ _ _).mp ri
  refine ⟨.int w .poison, ?_, ?_⟩
  · exact (poison_iff _ _ _).mpr rfl
  · simp [LLVM.Int.select, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
end Veir.InstSimplify
