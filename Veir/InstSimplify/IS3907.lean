import Veir.InstSimplify.CmpSelectSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
/-- Pinned upstream scalar integer rule; arbitrary result/operand width. -/
def IS3907 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let p ← matchPoison ty
    let _ ← MatchProg.root (.llvm .icmp) #[x,p] #[cty]
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun x => x)

theorem IS3907_valid : Pattern.Valid IS3907 := by
  simp only [IS3907, matchIntConstant, matchPoison]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ _ ⟨cw,cs⟩ rfl hc
  have : cw = 1 := by simpa using hc
  subst cw
  intro x pp pv pi
  obtain rfl := (poison_iff _ _ _).mp pi
  intro rp rv ri
  obtain rfl := (icmp_iff _ _ _ _ _).mp ri
  refine ⟨.int 1 .poison, ?_, ?_⟩
  · exact (poison_iff _ _ _).mpr rfl
  · cases x <;> simp [LLVM.Int.icmp, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
end Veir.InstSimplify
