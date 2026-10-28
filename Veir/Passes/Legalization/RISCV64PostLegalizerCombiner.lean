module

public import Veir.Pass
import Veir.PatternRewriter.Driver
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
      let pattern := RewritePattern.GreedyRewritePattern
        #[(sub_to_add riscv64LegalizerInfo).run, commutativeConstantRHS]
      -- Folding legalized gMIR can produce constants of illegal width, which isel cannot select.
      match RewritePattern.applyInContext pattern ctx (fold := false) with
      | none => throw "Error while applying the post-legalizer combines"
      | some ctx => pure ctx }

end

end Veir
