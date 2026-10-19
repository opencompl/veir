import Veir.Dialects.Arith.Puddle

/-! `arith.addi(b, arith.subi(a, b)) -> a`. -/

namespace Veir.ArithCanonicalize.F003

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
      let sub ← MatchProg.operation (.arith .subi) #[a, b] #[ty]
      let _ ← MatchProg.root (.arith .addi) #[b, sub.res[0]!] #[ty]
      return a)
    pure
    (fun a => a)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ a b subProp subVal hinterpSub
  obtain rfl := (subi_iff _ _ _ _ _).mp hinterpSub
  intro addProp addVal hinterpAdd
  obtain rfl := (addi_iff _ _ _ _ _).mp hinterpAdd
  grind [add_sub_cancel_comm_refines]

end Veir.ArithCanonicalize.F003
