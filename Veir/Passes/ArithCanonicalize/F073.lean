import Veir.Passes.ArithCanonicalize.ShiftSupport

/-! `arith.shrui(0, x) -> 0`. -/

namespace Veir.ArithCanonicalize.F073

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let zero ← matchConstant ty 0
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .shrui) #[zero, x] #[ty]
      return zero)
    pure
    (fun zero => zero)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern, matchConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ cstProp cstVal propzero hinterpCst x
  obtain rfl := (constant_iff _ _ _).mp hinterpCst
  intro opProp result hinterpOp
  obtain rfl := (shrui_iff _ _ _ _ _).mp hinterpOp
  simpa [propzero] using lshr_zero_value_refines w x opProp.exact

end Veir.ArithCanonicalize.F073
