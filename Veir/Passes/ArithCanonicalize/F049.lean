import Veir.Passes.ArithCanonicalize.RemainderSupport

/-! `arith.remsi(x, 1) -> 0`. -/

namespace Veir.ArithCanonicalize.F049

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
      let _ ← MatchProg.root (.arith .remsi) #[x, one] #[ty]
      return (ty, x))
    (fun (ty, _) => createConstant ty 0)
    (fun zero => zero)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern, matchConstant, createConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x cstProp val propone hinterpCst
  obtain rfl := (constant_iff _ _ _).mp hinterpCst
  intro _ remVal hinterpRem
  obtain ⟨_, rfl⟩ := (remsi_iff _ _ _ _).mp hinterpRem
  simp only [IsTypeAttr.cast?_of, Option.bind_some]
  refine ⟨.int w (.val 0), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    simp [IntegerAttr.ofInt, IntegerAttr.normalizeValue]
  · simpa [propone] using srem_one_refines w x

end Veir.ArithCanonicalize.F049
