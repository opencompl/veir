import Veir.Dialects.Arith.Puddle

namespace Veir.ArithCanonicalize.TD013

open Veir Veir.Puddle Veir.Data

/-- Scalar instance of upstream `SubILHSSubConstantRHS` with exact intersected overflow flags. -/
def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c0 ← MatchProg.operation (.arith .constant) #[] #[ty]
      let c1 ← MatchProg.operation (.arith .constant) #[] #[ty]

      let inner ← MatchProg.operation (.arith .subi)
        #[x, c0.res[0]!] #[ty]
      let root ← MatchProg.root (.arith .subi)
        #[c1.res[0]!, inner.res[0]!] #[ty]
      return (ty, x, c0.properties, c1.properties, inner.properties, root.properties))
    (fun (ty, x, c0, c1, p0, p1) => do
      let (newConst, flags) ← CreateProg.applyNative (ty, c0, c1, p0, p1)
        (fun (ty, c0, c1, p0, p1) => do
          let some intTy := ty.cast? IntegerType | none
          some ({ value := IntegerAttr.ofInt (c0.value.value + c1.value.value) intTy },
            { attr := { nsw := p0.attr.nsw && p1.attr.nsw,
                        nuw := p0.attr.nuw && p1.attr.nuw } }))
      let c ← CreateProg.operation (.arith .constant) #[] #[ty] newConst
      let replacement ← CreateProg.operation (.arith .subi)
        #[c.res[0]!, x] #[ty] flags
      return replacement)
    (fun result => result)

private def v4 (n : Nat) : LLVM.Int 4 := .val (BitVec.ofNat 4 n)

/-- Source is a defined value while the exact upstream replacement is poison. -/
theorem merged_nsw_counterexample :
    (LLVM.Int.sub (v4 7) (LLVM.Int.sub (v4 1) (v4 1) true false) true false) = v4 7 ∧
    (LLVM.Int.sub (v4 8) (v4 1) true false) = .poison := by
  decide


open Veir.ArithPuddle

/-- An exact scalar Puddle match witnesses failure of semantic preservation. -/
theorem not_preservesSemantics : ¬ pattern.PreservesSemantics := by
  unfold pattern
  unfoldPuddleBuilder
  simpPuddleSemantics
  refine ⟨IntegerType.signless 4, .int 4 (v4 1), ?_,
    { value := IntegerAttr.ofInt 1 (IntegerType.signless 4) }, .int 4 (v4 1), ?_,
    { value := IntegerAttr.ofInt 7 (IntegerType.signless 4) }, .int 4 (v4 7), ?_,
    { attr := { nsw := true, nuw := false } }, .int 4 (v4 0), ?_,
    { attr := { nsw := true, nuw := false } }, .int 4 (v4 7), ?_, ?_⟩
  · decide
  · apply (constant_iff _ _ _).mpr
    decide
  · apply (constant_iff _ _ _).mpr
    decide
  · apply (subi_iff _ _ _ _ _).mpr
    decide
  · apply (subi_iff _ _ _ _ _).mpr
    decide
  · have hcast : (TypeAttr.of IntegerType (IntegerType.signless 4)).cast? IntegerType =
        some (IntegerType.signless 4) := by decide
    simp only [hcast]
    intro h
    rcases h with ⟨value, hconst, targetValue, htarget, href⟩
    have hc := (constant_iff _ _ _).mp hconst
    subst value
    have ht := (subi_iff _ _ _ _ _).mp htarget
    subst targetValue
    let folded := IntegerAttr.ofInt
      ((IntegerAttr.ofInt 1 (IntegerType.signless 4)).value +
       (IntegerAttr.ofInt 7 (IntegerType.signless 4)).value)
      (IntegerType.signless 4)
    change RuntimeValue.int 4 (v4 7) ⊒
      .int 4 (LLVM.Int.sub (.val (BitVec.ofInt 4 folded.value)) (v4 1) true false) at href
    have hp : LLVM.Int.sub (.val (BitVec.ofInt 4 folded.value)) (v4 1) true false =
        .poison := by decide
    rw [hp] at href
    simpa [v4, RuntimeValue.isRefinedBy, isRefinedBy] using href

/-- Upstream flag intersection produces a non-valid Puddle rewrite. -/
theorem pattern_not_valid : ¬ Pattern.Valid pattern := by
  intro h
  exact not_preservesSemantics h.refines

end Veir.ArithCanonicalize.TD013
