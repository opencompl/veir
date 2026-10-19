import Veir.Passes.ArithCanonicalize.SelectSupport

/-! `select(c, poison, x) -> x`; fully poisoned integer values are materialized
     in VeIR as `llvm.mlir.poison`. -/
namespace Veir.ArithCanonicalize.F171

open Veir Veir.Puddle Veir.Data Veir.ArithCanonicalize.SelectSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let condTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let c ← MatchProg.value condTy
      let x ← MatchProg.value ty
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let _ ← MatchProg.root (.arith .select) #[c, poison.res[0]!, x] #[ty]
      return x)
    pure
    (fun x => x)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ ⟨cw, s⟩ condTy hType hWidth c hConforms x pProps pVal hPoison rootProps result hResult
  cases hType
  obtain ⟨cond, rfl⟩ := RuntimeValue.Conforms.integerType.mp hConforms
  cases condTy with
  | mk n sign =>
    dsimp at hWidth
    subst n
    obtain rfl := (poison_iff _ _).mp hPoison
    obtain rfl := (select_iff _ _ _ _ _).mp hResult
    exact poison_true_arm cond x

end Veir.ArithCanonicalize.F171
