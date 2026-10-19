import Veir.Dialects.Arith.Puddle

namespace Veir.ArithCanonicalize.TD001

open Veir Veir.Puddle Veir.Data

/-- The scalar `AddIAddConstant` rewrite, including upstream's intersection of
    the two overflow flag sets. -/
def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c0 ← MatchProg.operation (.arith .constant) #[] #[ty]
      let inner ← MatchProg.operation (.arith .addi) #[x, c0.res[0]!] #[ty]
      let c1 ← MatchProg.operation (.arith .constant) #[] #[ty]
      let root ← MatchProg.root (.arith .addi) #[inner.res[0]!, c1.res[0]!] #[ty]
      return (ty, x, c0.properties, c1.properties, inner.properties, root.properties))
    (fun (ty, x, c0, c1, p0, p1) => do
      let (newConst, flags) ← CreateProg.applyNative (ty, c0, c1, p0, p1)
        (fun (ty, c0, c1, p0, p1) => do
          let some intTy := ty.cast? IntegerType | none
          some ({ value := IntegerAttr.ofInt (c0.value.value + c1.value.value) intTy },
            { attr := { nsw := p0.attr.nsw && p1.attr.nsw,
                        nuw := p0.attr.nuw && p1.attr.nuw } }))
      let c ← CreateProg.operation (.arith .constant) #[] #[ty] newConst
      let add ← CreateProg.operation (.arith .addi) #[x, c.res[0]!] #[ty] flags
      return add)
    (fun result => result)

/-- At i4, the source computes `1 + (-8) + (-1) = -8` without overflow.
    The folded constant is `7`, and `1 + 7` has signed overflow. -/
theorem merged_nsw_counterexample :
    LLVM.Int.add
      (LLVM.Int.add (.val (1#4)) (.val (8#4)) true false)
      (.val (15#4)) true false = .val (8#4) ∧
    LLVM.Int.add (.val (1#4)) (.val (7#4)) true false = .poison := by
  decide

open Veir.ArithPuddle

private def v4 (n : Nat) : LLVM.Int 4 := .val (BitVec.ofNat 4 n)

theorem not_preservesSemantics : ¬ pattern.PreservesSemantics := by
  unfold pattern
  unfoldPuddleBuilder
  simpPuddleSemantics
  refine ⟨IntegerType.signless 4, .int 4 (v4 1), ?_,
    { value := IntegerAttr.ofInt 8 (IntegerType.signless 4) }, .int 4 (v4 8), ?_,
    { attr := { nsw := true, nuw := false } }, .int 4 (v4 9), ?_,
    { value := IntegerAttr.ofInt 15 (IntegerType.signless 4) }, .int 4 (v4 15), ?_,
    { attr := { nsw := true, nuw := false } }, .int 4 (v4 8), ?_, ?_⟩
  · decide
  · apply (constant_iff _ _ _).mpr
    decide
  · apply (addi_iff _ _ _ _ _).mpr
    decide
  · apply (constant_iff _ _ _).mpr
    decide
  · apply (addi_iff _ _ _ _ _).mpr
    decide
  · have hcast : (TypeAttr.of IntegerType (IntegerType.signless 4)).cast? IntegerType =
        some (IntegerType.signless 4) := by decide
    simp only [hcast]
    intro h
    rcases h with ⟨value, hconst, target, hadd, href⟩
    have hc := (constant_iff _ _ _).mp hconst
    subst value
    have ha := (addi_iff _ _ _ _ _).mp hadd
    subst target
    let folded := IntegerAttr.ofInt
      ((IntegerAttr.ofInt 8 (IntegerType.signless 4)).value +
       (IntegerAttr.ofInt 15 (IntegerType.signless 4)).value)
      (IntegerType.signless 4)
    change RuntimeValue.int 4 (v4 8) ⊒
      .int 4 (LLVM.Int.add (v4 1) (.val (BitVec.ofInt 4 folded.value)) true false) at href
    have hp : LLVM.Int.add (v4 1) (.val (BitVec.ofInt 4 folded.value)) true false =
        .poison := by decide
    rw [hp] at href
    simpa [v4, RuntimeValue.isRefinedBy, isRefinedBy] using href

/-- The upstream flag-intersection rewrite is not a valid Puddle pattern. -/
theorem pattern_not_valid : ¬ Pattern.Valid pattern := by
  intro h
  exact not_preservesSemantics h.refines

end Veir.ArithCanonicalize.TD001
