import Veir.InstSimplify.GEPZeroSchema
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
/-- Every nonempty static all-zero GEP, including arbitrary array/struct nesting, preserves its pointer. -/
def IS5335_static : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := LLVM.PointerType)
    let p ← MatchProg.value ty
    let _ ← MatchProg.root (.llvm .getelementptr) #[p] #[ty]
      (fun props => !props.rawConstantIndices.values.isEmpty &&
        props.rawConstantIndices.values.all (· == 0))
    return p)
  pure (fun p => p)

theorem IS5335_static_valid : Pattern.Valid IS5335_static := by
  simp only [IS5335_static]
  provePuddleValid
  rintro ⟨⟩
  simp only [RuntimeValue.Conforms.llvmPointerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro p rp rv hnonzero hzero hi
  have hz : ∀ index ∈ rp.rawConstantIndices.values, index = 0 := by
    simpa only [Array.all_eq_true', beq_iff_eq] using hzero
  exact gep_all_zero_static_refines rp hz p rv hi
/-- Scalar source family for every finite dynamic arity and every zero integer literal payload. -/
def IS5335 (payloads : List Int) : Pattern OpCode := gepAllZeroFamily payloads

theorem IS5335_valid (payloads : List Int) : Pattern.Valid (IS5335 payloads) :=
  gepAllZeroFamily_valid payloads

end Veir.InstSimplify
