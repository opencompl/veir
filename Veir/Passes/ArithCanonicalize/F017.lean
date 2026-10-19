import Veir.Dialects.Arith.Puddle

/-! `arith.muli(x, 1) -> x` from the pinned Arith fold hook. -/

namespace Veir.ArithCanonicalize.F017

open Veir
open Veir.Puddle
open Veir.Data
open Veir.ArithPuddle

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let one ← matchConstant ty 1
      let _ ← MatchProg.root (.arith .muli) #[x, one] #[ty]
      return x)
    pure
    (fun x => x)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern, matchConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x cstProp val propone hinterpCst
  obtain rfl := (constant_iff _ _ _).mp hinterpCst
  intro mulProp val hinterpMul
  obtain rfl := (muli_iff _ _ _ _ _).mp hinterpMul
  grind [mul_one_refines]

end Veir.ArithCanonicalize.F017
