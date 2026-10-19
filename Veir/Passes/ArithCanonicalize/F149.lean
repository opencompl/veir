import Veir.Passes.ArithCanonicalize.CastCounterexampleSupport

/-! Pinned nested `trunci` fold, preserving outer overflow flags. -/
namespace Veir.ArithCanonicalize.F149

open Veir Veir.Puddle Veir.Data
open Veir.ArithCanonicalize.CastCounterexampleSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let sourceTy ← MatchProg.type (Attr := IntegerType)
      let middleTy ← MatchProg.type (Attr := IntegerType)
      let resultTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value sourceTy
      let inner ← MatchProg.operation (.arith .trunci) #[x] #[middleTy]
      let root ← MatchProg.root (.arith .trunci) #[inner.res[0]!] #[resultTy]
      return (sourceTy, resultTy, x, root.properties))
    (fun (sourceTy, resultTy, x, overflow) =>
      CreateProg.operation (.arith .trunci) #[x] #[resultTy] overflow)
    (fun result => result)

/-- With `nsw` on the outer operation, the intermediate truncation changes
    which sign extension the overflow check compares against. -/
theorem nsw_counterexample :
    LLVM.Int.trunc
      (LLVM.Int.trunc (.val (255#16)) 8 false false (by decide))
      4 true false (by decide) = .val (15#4) ∧
    LLVM.Int.trunc (.val (255#16)) 4 true false (by decide) = .poison := by
  decide

theorem not_preservesSemantics : ¬ pattern.PreservesSemantics := by
  unfold pattern
  unfoldPuddleBuilder
  simpPuddleSemantics
  refine ⟨IntegerType.signless 16, IntegerType.signless 8,
    IntegerType.signless 4, .int 16 (.val (255#16)), ?_,
    { attr := { nsw := false, nuw := false } },
    .int 8 (.val (255#8)), ?_,
    { attr := { nsw := true, nuw := false } },
    .int 4 (.val (15#4)), ?_, ?_⟩
  · decide
  · apply (trunci_iff 16 8 (by decide) _ _ _).mpr
    decide
  · apply (trunci_iff 8 4 (by decide) _ _ _).mpr
    decide
  · intro target htarget href
    have ht := (trunci_iff 16 4 (by decide) _ _ _).mp htarget
    subst target
    have hp : LLVM.Int.trunc (.val (255#16)) 4 true false (by decide) = .poison := by decide
    rw [hp] at href
    simpa [RuntimeValue.isRefinedBy, isRefinedBy] using href

theorem pattern_not_valid : ¬ Pattern.Valid pattern := by
  intro h
  exact not_preservesSemantics h.refines

end Veir.ArithCanonicalize.F149
