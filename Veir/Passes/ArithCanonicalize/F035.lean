import Veir.Passes.ArithCanonicalize.DivisionSupport

/-! `arith.ceildivui(0, x) -> 0`; zero division is undefined. -/

namespace Veir.ArithCanonicalize.F035

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let zero ← matchConstant ty 0
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .ceildivui) #[zero, x] #[ty]
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
  intro divProp divVal hinterpDiv
  obtain ⟨_, rfl⟩ := (Veir.ArithCanonicalize.ceildivui_iff _ _ _ _).mp hinterpDiv
  simpa [propzero] using Veir.ArithCanonicalize.uceil_zero_refines w x

end Veir.ArithCanonicalize.F035
