import Veir.Passes.ArithCanonicalize.SelectMinMaxSupport

/-! Pinned `SelectCmpIUleToMaxUI`, with the exact `slt` predicate guard. -/
namespace Veir.ArithCanonicalize.TD042

open Veir Veir.Puddle Veir.Data Veir.ArithCanonicalize.SelectSupport
open Veir.ArithCanonicalize.SelectMinMaxSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let cmp ← MatchProg.operation (.arith .cmpi) #[a, b] #[boolTy]
        (fun p => p.predicate == .ule)
      let _ ← MatchProg.root (.arith .select) #[cmp.res[0]!, b, a] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let props ← CreateProg.property (.arith .maxui) ()
      CreateProg.operation (.arith .maxui) #[a, b] #[ty] props)
    (fun result => result)

theorem pattern_valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ ⟨bw, s⟩ boolTy hType hWidth a b cmpProp cmpVal hPred hCmp rootProp result hResult
  cases hType
  cases boolTy with
  | mk n sign =>
    dsimp at hWidth
    subst n
    obtain rfl := (cmpi_iff _ _ _ _ _).mp hCmp
    obtain rfl := (select_iff _ _ _ _ _).mp hResult
    refine ⟨.int w (LLVM.Int.umax a b), ?_, ?_⟩
    · exact (maxui_iff _ _ _ _).mpr rfl
    · simpa [hPred] using select_ule_umax_inverse a b

end Veir.ArithCanonicalize.TD042
