import Veir.Passes.ArithCanonicalize.ExtendedFoldSupport

/-! `arith.addui_extended(x, 0) -> (x, false)`. -/

namespace Veir.ArithCanonicalize.F005

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize Veir.ArithCanonicalize.ExtendedSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let carryTy ← MatchProg.type (Attr := IntegerType)
        (fun t => t == IntegerType.signless 1)
      let x ← MatchProg.value ty
      let zero ← matchConstant ty 0
      let _ ← MatchProg.root (.arith .addui_extended)
        #[x, zero] #[ty, carryTy]
      return (carryTy, x))
    (fun (carryTy, x) => do
      let falseFlag ← createConstant carryTy 0
      return (x, falseFlag))
    (fun (x, flag) => #[x, flag])

theorem valid : Pattern.Valid pattern := by
  unfold pattern matchConstant createConstant
  provePuddleValid
  rintro ⟨w, s⟩ carryTy ⟨cw, t⟩ hTy hSign x hx c vc hc0 hc _ v0 v1 hi
  cases hTy
  cases hSign
  obtain ⟨xv, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain ⟨rfl, rfl⟩ := (addui_extended_iff _ _ _ _ _).mp hi
  simp only [IsTypeAttr.cast?_of, Option.bind_some]
  refine ⟨.int 1 (.val 0), ?_, ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    simp [IntegerAttr.ofInt, IntegerAttr.normalizeValue]
  · simpa [hc0] using (uadd_zero_extended_refines w xv).1
  · simpa [hc0] using (uadd_zero_extended_refines w xv).2

end Veir.ArithCanonicalize.F005
