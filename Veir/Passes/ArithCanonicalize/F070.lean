import Veir.Passes.ArithCanonicalize.ShiftSupport

/-! `arith.shli(0, x) -> 0`. -/

namespace Veir.ArithCanonicalize.F070

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let zero ← matchConstant ty 0
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .shli) #[zero, x] #[ty]
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
  obtain rfl := (shli_iff _ _ _ _ _).mp hinterpOp
  simpa [propzero] using shl_zero_value_refines w x opProp.attr.nsw opProp.attr.nuw

end Veir.ArithCanonicalize.F070
