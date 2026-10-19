import Veir.Passes.ArithCanonicalize.RemainderSupport

/-! `arith.remui(0, x) -> 0`. -/

namespace Veir.ArithCanonicalize.F047a

open Veir
open Veir.Puddle
open Veir.Data
open Veir.ArithPuddle

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let zero ← matchConstant ty 0
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .remui) #[zero, x] #[ty]
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
  intro _ remVal hinterpRem
  obtain ⟨_, rfl⟩ := (remui_iff _ _ _ _).mp hinterpRem
  simpa [propzero] using urem_zero_refines w x

end Veir.ArithCanonicalize.F047a
