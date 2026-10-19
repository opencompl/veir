import Veir.Passes.ArithCanonicalize.SelectSupport

/-! Upstream `arith.minsi(x, x) -> x`. -/
namespace Veir.ArithCanonicalize.F124

open Veir Veir.Puddle Veir.Data Veir.ArithCanonicalize.SelectSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .minsi) #[x, x] #[ty]
      return x)
    pure
    (fun x => x)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x prop v h
  obtain rfl := (minsi_iff _ _ _ _).mp h
  exact minsi_self x

end Veir.ArithCanonicalize.F124
