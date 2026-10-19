import Veir.Passes.ArithCanonicalize.ShiftSupport

/-! `arith.shrsi(x, 0) -> x`. -/

namespace Veir.ArithCanonicalize.F076

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let zero ← matchConstant ty 0
      let _ ← MatchProg.root (.arith .shrsi) #[x, zero] #[ty]
      return x)
    pure
    (fun x => x)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern, matchConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x cstProp val propzero hinterpCst
  obtain rfl := (constant_iff _ _ _).mp hinterpCst
  intro opProp result hinterpOp
  obtain rfl := (shrsi_iff _ _ _ _ _).mp hinterpOp
  simpa [propzero] using ashr_zero_count_refines w x opProp.exact

end Veir.ArithCanonicalize.F076
