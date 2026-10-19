import Veir.Passes.ArithCanonicalize.ExtendedFoldSupport

/-! `arith.subui_extended(x, x) -> (0, false)`. -/

namespace Veir.ArithCanonicalize.F008

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize Veir.ArithCanonicalize.ExtendedSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let carryTy ← MatchProg.type (Attr := IntegerType)
        (fun t => t == IntegerType.signless 1)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .subui_extended)
        #[x, x] #[ty, carryTy]
      return (ty, carryTy))
    (fun (ty, carryTy) => do
      let zero ← createConstant ty 0
      let falseFlag ← createConstant carryTy 0
      return (zero, falseFlag))
    (fun (zero, flag) => #[zero, flag])

theorem valid : Pattern.Valid pattern := by
  unfold pattern createConstant
  provePuddleValid
  rintro ⟨w, s⟩ carryTy ⟨cw, t⟩ hTy hSign x hx _ v0 v1 hi
  cases hTy
  cases hSign
  obtain ⟨xv, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  obtain ⟨rfl, rfl⟩ := (subui_extended_iff _ _ _ _ _).mp hi
  simp only [IsTypeAttr.cast?_of, Option.bind_some]
  refine ⟨.int w (.val 0), ?_, .int 1 (.val 0), ?_, ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    simp [IntegerAttr.ofInt, IntegerAttr.normalizeValue]
  · apply (constant_iff _ _ _).mpr
    simp [IntegerAttr.ofInt, IntegerAttr.normalizeValue]
  · exact (usub_self_extended_refines w xv).1
  · exact (usub_self_extended_refines w xv).2

end Veir.ArithCanonicalize.F008
