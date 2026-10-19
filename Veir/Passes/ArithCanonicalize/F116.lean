import Veir.Passes.ArithCanonicalize.SelectSupport

/-! Upstream `arith.maxsi(x, x) -> x`. -/
namespace Veir.ArithCanonicalize.F116

open Veir Veir.Puddle Veir.Data Veir.ArithCanonicalize.SelectSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .maxsi) #[x, x] #[ty]
      return x)
    pure
    (fun x => x)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x prop v h
  obtain rfl := (maxsi_iff _ _ _ _).mp h
  exact maxsi_self x

end Veir.ArithCanonicalize.F116
