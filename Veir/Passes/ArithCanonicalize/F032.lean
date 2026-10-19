import Veir.Passes.ArithCanonicalize.F032Support

/-! Both operand orders of `(a * b) / b -> a` for signed division with `nsw`. -/

namespace Veir.ArithCanonicalize.F032

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let mul ← MatchProg.operation (.arith .muli) #[a, b] #[ty]
      MatchProg.matchNative mul.properties (fun props => props.attr.nsw)
      let _ ← MatchProg.root (.arith .divsi) #[mul.res[0]!, b] #[ty]
      return a)
    pure
    (fun a => a)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ a b mulProp mulVal hinterpMul divProp divVal hinterpDiv hnsw
  obtain rfl := (muli_iff _ _ _ _ _).mp hinterpMul
  obtain ⟨hUB, rfl⟩ := (divsi_iff _ _ _ _ _).mp hinterpDiv
  simpa [hnsw] using Veir.ArithCanonicalize.signed_mul_div_refines
    w a b mulProp.attr.nuw divProp.exact (by simpa [hnsw] using hUB)

def pattern_commuted : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let mul ← MatchProg.operation (.arith .muli) #[b, a] #[ty]
      MatchProg.matchNative mul.properties (fun props => props.attr.nsw)
      let _ ← MatchProg.root (.arith .divsi) #[mul.res[0]!, b] #[ty]
      return a)
    pure
    (fun a => a)

theorem valid_commuted : Pattern.Valid pattern_commuted := by
  simp only [pattern_commuted]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ a b mulProp mulVal hinterpMul divProp divVal hinterpDiv hnsw
  obtain rfl := (muli_iff _ _ _ _ _).mp hinterpMul
  obtain ⟨hUB, rfl⟩ := (divsi_iff _ _ _ _ _).mp hinterpDiv
  simpa [hnsw] using Veir.ArithCanonicalize.signed_mul_div_comm_refines
    w a b mulProp.attr.nuw divProp.exact (by simpa [hnsw] using hUB)

end Veir.ArithCanonicalize.F032
