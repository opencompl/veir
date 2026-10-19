import Veir.Passes.ArithCanonicalize.ExtendedMoreSupport
import Veir.Passes.ArithCanonicalize.ConstSupport

/-! Pinned `mului_extended(x, 1) -> (x, 0)`. -/
namespace Veir.ArithCanonicalize.F022

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
  Veir.ArithCanonicalize Veir.ArithCanonicalize.ExtendedSupport
  Veir.ArithCanonicalize.ExtendedMoreSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let one ← matchConstant ty 1
      let _ ← MatchProg.root (.arith .mului_extended) #[x, one] #[ty, ty]
      return (ty, x))
    (fun (ty, x) => do
      let zero ← createConstant ty 0
      return (x, zero))
    (fun (x, zero) => #[x, zero])

theorem valid : Pattern.Valid pattern := by
  unfold pattern matchConstant createConstant
  provePuddleValid
  rintro ⟨w, s⟩ x hx c vc hOne hConst rootProps v0 v1 hResult
  obtain ⟨xv, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  obtain rfl := (constant_iff _ _ _).mp hConst
  obtain ⟨rfl, rfl⟩ := (mului_extended_iff _ _ _ _ _).mp hResult
  simp only [IsTypeAttr.cast?_of, Option.bind_some]
  refine ⟨.int w (.val (BitVec.ofInt w (IntegerAttr.ofInt 0
    (IntegerType.mk w s)).value)), ?_, ?_, ?_⟩
  · exact (constant_iff _ _ _).mpr rfl
  · simpa [hOne] using (umul_one xv).1
  · have hz : BitVec.ofInt w (IntegerAttr.ofInt 0 (IntegerType.mk w s)).value = 0 := by
      simpa using ofInt_ofInt (IntegerType.mk w s) 0
    simpa [hOne, hz] using (umul_one xv).2

end Veir.ArithCanonicalize.F022
