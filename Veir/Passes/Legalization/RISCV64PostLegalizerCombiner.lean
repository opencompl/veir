module

public import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Canonicalize
import Veir.Passes.Legalization.CombinerHelper
import Veir.Passes.Legalization.RISCV64LegalizerInfo
import Veir.PatternRewriter.Puddle.Execution

/-!
# RISC-V 64 Post-Legalizer Combiner

This file implements the combines that run on the legalized gMIR of RISC-V 64.
These maintain the legality and only run at -O1 and above.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/lib/Target/RISCV/GISel/RISCVPostLegalizerCombiner.cpp
-/

namespace Veir

public section

def RISCV64PostLegalizerCombinerPass : Pass OpCode :=
  { name := "postlegalizer-combiner-riscv64"
    description := "Combine legalized gMIR operations for RISC-V 64."
    run := fun _ ctx _ _ => do
      let pattern := RewritePattern.GreedyRewritePattern
        #[(sub_to_add riscv64LegalizerInfo).run, commutativeConstantRHS]
      match RewritePattern.applyInContext pattern ctx with
      | none => throw "error while applying the post-legalizer combines"
      | some ctx => pure ctx }

end

end Veir
