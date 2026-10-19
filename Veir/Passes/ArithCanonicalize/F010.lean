import Veir.Dialects.Arith.Puddle

/-! `arith.subi(x, x) -> 0` from the pinned Arith fold hook. -/

namespace Veir.ArithCanonicalize.F010

open Veir
open Veir.Puddle
open Veir.Data
open Veir.ArithPuddle

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .subi) #[x, x] #[ty]
      return ty)
    (fun ty => createConstant ty 0)
    (fun zero => zero)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern, createConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x subProp val hinterpSub
  obtain rfl := (subi_iff _ _ _ _ _).mp hinterpSub
  simp only [IsTypeAttr.cast?_of, Option.bind_some]
  refine ⟨.int w (.val 0), ?_, sub_self_refines _ _ _ _⟩
  apply (constant_iff _ _ _).mpr
  simp [IntegerAttr.ofInt, IntegerAttr.normalizeValue]

end Veir.ArithCanonicalize.F010
