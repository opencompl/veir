import Veir.Dialects.Arith.Puddle

/-! `arith.subi(arith.addi(a, b), a) -> b`. -/

namespace Veir.ArithCanonicalize.F013

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
      let add ← MatchProg.operation (.arith .addi) #[a, b] #[ty]
      let _ ← MatchProg.root (.arith .subi) #[add.res[0]!, a] #[ty]
      return b)
    pure
    (fun b => b)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ a b addProp addVal hinterpAdd
  obtain rfl := (addi_iff _ _ _ _ _).mp hinterpAdd
  intro subProp subVal hinterpSub
  obtain rfl := (subi_iff _ _ _ _ _).mp hinterpSub
  grind [sub_add_cancel_left_refines]

end Veir.ArithCanonicalize.F013
