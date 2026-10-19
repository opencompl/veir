import Veir.Passes.ArithCanonicalize.CastCounterexampleSupport

/-! Pinned `TruncIShrSIToTrunciShrUI`, including exact and truncation flags. -/
namespace Veir.ArithCanonicalize.TD057

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize.CastCounterexampleSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let wide ← MatchProg.type (Attr := IntegerType)
      let narrow ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value wide
      let shiftOp ← MatchProg.operation (.arith .constant) #[] #[wide]
      let shift := shiftOp.res[0]!
      let _ ← MatchProg.matchNative (wide, narrow, shiftOp.properties)
        (fun (wide, narrow, p) =>
          match wide.cast? IntegerType, narrow.cast? IntegerType with
          | some w, some n => w.bitwidth > n.bitwidth &&
              (Int.ofNat (w.bitwidth - n.bitwidth) == p.value.value)
          | _, _ => false)
      let shr ← MatchProg.operation (.arith .shrsi) #[x, shift] #[wide]
      let root ← MatchProg.root (.arith .trunci) #[shr.res[0]!] #[narrow]
      return (wide, narrow, x, shift, shr.properties, root.properties))
    (fun (wide, narrow, x, shift, exact, overflow) => do
      let exact' ← CreateProg.applyNative exact (fun (p : ExactProperties) => some p)
      let shr ← CreateProg.operation (.arith .shrui) #[x, shift] #[wide] exact'
      CreateProg.operation (.arith .trunci) #[shr.res[0]!] #[narrow] overflow)
    (fun result => result)

/-- Source is defined at -1, while the rewritten truncation is poison.
    The upstream rule retains the truncation's `nsw` bit. -/
theorem nsw_counterexample :
    LLVM.Int.trunc
      (LLVM.Int.ashr (.val (252#8)) (.val (4#8)) false)
      4 true false (by decide) = .val (15#4) ∧
    LLVM.Int.trunc
      (LLVM.Int.lshr (.val (252#8)) (.val (4#8)) false)
      4 true false (by decide) = .poison := by
  decide

theorem not_preservesSemantics : ¬ pattern.PreservesSemantics := by
  unfold pattern
  unfoldPuddleBuilder
  simpPuddleSemantics
  refine ⟨IntegerType.signless 8, IntegerType.signless 4,
    .int 8 (.val (252#8)), ?_,
    { value := IntegerAttr.ofInt 4 (IntegerType.signless 8) },
    .int 8 (.val (4#8)), ?_,
    { exact := false }, .int 8 (.val (255#8)), ?_,
    { attr := { nsw := true, nuw := false } },
    .int 4 (.val (15#4)), ?_, ?_, ?_⟩
  · decide
  · apply (constant_iff _ _ _).mpr
    decide
  · apply (shrsi_iff _ _ _ _ _).mpr
    decide
  · apply (trunci_iff 8 4 (by decide) _ _ _).mpr
    decide
  · decide
  · intro h
    simp only [Option.bind] at h
    rcases h with ⟨shifted, hshr, target, htrunc, href⟩
    have hs := (shrui_iff _ _ _ _ _).mp hshr
    subst shifted
    have ht := (trunci_iff 8 4 (by decide) _ _ _).mp htrunc
    subst target
    have hp : LLVM.Int.trunc
        (LLVM.Int.lshr (.val (252#8)) (.val (4#8)) false)
        4 true false (by decide) = .poison := by decide
    rw [hp] at href
    simpa [RuntimeValue.isRefinedBy, isRefinedBy] using href

theorem pattern_not_valid : ¬ Pattern.Valid pattern := by
  intro h
  exact not_preservesSemantics h.refines

end Veir.ArithCanonicalize.TD057
