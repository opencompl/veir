import Veir.Dialects.Arith.Puddle

/-! `arith.subi(x, 0) -> x` from the pinned Arith fold hook. -/

namespace Veir.ArithCanonicalize.F011

open Veir
open Veir.Puddle
open Veir.Data
open Veir.ArithPuddle

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let zero ← matchConstant ty 0
      let _ ← MatchProg.root (.arith .subi) #[x, zero] #[ty]
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
  intro subProp val hinterpSub
  obtain rfl := (subi_iff _ _ _ _ _).mp hinterpSub
  grind [sub_zero_refines]

end Veir.ArithCanonicalize.F011
