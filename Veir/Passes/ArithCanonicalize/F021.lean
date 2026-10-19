import Veir.Passes.ArithCanonicalize.ExtendedMoreSupport

/-! Pinned `mului_extended(x, 0) -> (0, 0)`. -/
namespace Veir.ArithCanonicalize.F021

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
  Veir.ArithCanonicalize.ExtendedSupport
  Veir.ArithCanonicalize.ExtendedMoreSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let zero ← matchConstant ty 0
      let _ ← MatchProg.root (.arith .mului_extended) #[x, zero] #[ty, ty]
      return zero)
    pure
    (fun zero => #[zero, zero])

theorem valid : Pattern.Valid pattern := by
  unfold pattern matchConstant
  provePuddleValid
  rintro ⟨w, s⟩ x hx c vc hZero hConst rootProps v0 v1 hResult
  obtain ⟨xv, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  obtain rfl := (constant_iff _ _ _).mp hConst
  obtain ⟨rfl, rfl⟩ := (mului_extended_iff _ _ _ _ _).mp hResult
  simpa [hZero] using umul_zero xv

end Veir.ArithCanonicalize.F021
