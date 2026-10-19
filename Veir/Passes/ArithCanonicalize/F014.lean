import Veir.Dialects.Arith.Puddle

/-! `arith.subi(a, arith.subi(a, b)) -> b`. -/

namespace Veir.ArithCanonicalize.F014

open Veir
open Veir.Puddle
open Veir.Data
open Veir.ArithPuddle

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let inner ← MatchProg.operation (.arith .subi) #[a, b] #[ty]
      let _ ← MatchProg.root (.arith .subi) #[a, inner.res[0]!] #[ty]
      return b)
    pure
    (fun b => b)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ a b innerProp innerVal hinterpInner
  obtain rfl := (subi_iff _ _ _ _ _).mp hinterpInner
  intro outerProp outerVal hinterpOuter
  obtain rfl := (subi_iff _ _ _ _ _).mp hinterpOuter
  grind [sub_sub_cancel_refines]

end Veir.ArithCanonicalize.F014
