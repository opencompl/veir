import Veir.InstSimplify.MiscSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
/-- An index-free GEP retains the modeled pointer and its object identity. -/
def IS5317 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := LLVM.PointerType) (fun _ => true)
    let p ← MatchProg.value ty
    let r ← MatchProg.root (.llvm .getelementptr) #[p] #[ty]
    MatchProg.matchNative r.properties (fun p => p.rawConstantIndices.values == #[])
    return p)
  pure (fun p => p)
theorem IS5317_valid : Pattern.Valid IS5317 := by
  simp only [IS5317]
  provePuddleValid
  rintro ⟨⟩
  simp only [RuntimeValue.Conforms.llvmPointerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro p
  rintro rp rv ri h
  have h : rp.rawConstantIndices.values = #[] := by simpa using h
  obtain rfl := (gep_no_indices_iff rp h p rv).mp ri
  cases p <;> simp [RuntimeValue.isRefinedBy, isRefinedBy]
end Veir.InstSimplify
