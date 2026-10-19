import Veir.Passes.ArithCanonicalize.SelectSupport

/-! Pinned fold `select(cond, true, false) -> cond` at signless i1. -/
namespace Veir.ArithCanonicalize.F173

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
  Veir.ArithCanonicalize.SelectSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
        (fun t => t.bitwidth = 1 && t.signedness == .signless)
      let cond ← MatchProg.value ty
      let one ← matchConstant ty 1
      let zero ← matchConstant ty 0
      let _ ← MatchProg.root (.arith .select) #[cond, one, zero] #[ty]
      return cond)
    pure
    (fun cond => cond)

theorem valid : Pattern.Valid pattern := by
  unfold pattern matchConstant
  provePuddleValid
  rintro ty ⟨w, sign⟩ rfl hWidth hSign cond hCond
    pOne vOne hOne hOneInterp pZero vZero hZero hZeroInterp
    rootProps result hResult
  dsimp at hWidth hSign
  have hw := hWidth
  subst w
  obtain ⟨c, rfl⟩ := RuntimeValue.Conforms.integerType.mp hCond
  obtain rfl := (constant_iff _ _ _).mp hOneInterp
  obtain rfl := (constant_iff _ _ _).mp hZeroInterp
  obtain rfl := (select_iff _ _ _ _ _).mp hResult
  simpa [hOne, hZero] using select_bool_identity c

end Veir.ArithCanonicalize.F173
