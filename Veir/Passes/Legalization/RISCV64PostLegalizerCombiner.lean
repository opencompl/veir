module

public import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Canonicalize
import Veir.Passes.Legalization.CombinerHelper
import Veir.Passes.Legalization.RISCV64LegalizerInfo
import Veir.PatternRewriter.Puddle.Execution

/-!
# RISC-V 64 Post-Legalizer Combiner

This file implements the combines that run on the legalized gMIR of RISC-V 64. They preserve
legality, so the result is still legal gMIR.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/lib/Target/RISCV/GISel/RISCVPostLegalizerCombiner.cpp
-/

namespace Veir

public section

def PostLegalizerCombinerRISCV64Pass : Pass OpCode :=
  { name := "postlegalizer-combiner-riscv64"
    description := "Combine legalized gMIR operations for RISC-V 64."
    run := fun _ ctx _ _ => do
      -- The combines come before `sub_to_add`, which would otherwise rewrite the subtractions
      -- some of them match.
      let pattern := RewritePattern.GreedyRewritePattern <|
        (combines ++ selectCombines riscv64LegalizerInfo).map (·.run) ++
        #[(sub_to_add riscv64LegalizerInfo).run, redundant_and.run, commutativeConstantRHS]
      match RewritePattern.applyInContext pattern ctx with
      | none => throw "Error while applying the post-legalizer combines"
      | some ctx => pure ctx }

end

end Veir
