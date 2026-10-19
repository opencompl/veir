import Veir.Passes.ArithCanonicalize.SelectSupport

/-! Pinned `select(cmpi ne, a, b)` fold, for both arm orders. -/
namespace Veir.ArithCanonicalize.F174b

open Veir Veir.Puddle Veir.Data Veir.ArithCanonicalize.SelectSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let cmp ← MatchProg.operation (.arith .cmpi) #[a, b] #[boolTy]
        (fun p => p.predicate == .ne)
      let _ ← MatchProg.root (.arith .select) #[cmp.res[0]!, a, b] #[ty]
      return a)
    pure
    (fun a => a)

theorem valid : Pattern.Valid pattern := by
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
    simpa [hPred] using select_ne_true_arm a b

def pattern_swapped : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let cmp ← MatchProg.operation (.arith .cmpi) #[a, b] #[boolTy]
        (fun p => p.predicate == .ne)
      let _ ← MatchProg.root (.arith .select) #[cmp.res[0]!, b, a] #[ty]
      return b)
    pure
    (fun b => b)

theorem valid_swapped : Pattern.Valid pattern_swapped := by
  simp only [pattern_swapped]
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
    simpa [hPred] using select_ne_true_arm_swapped a b

end Veir.ArithCanonicalize.F174b
