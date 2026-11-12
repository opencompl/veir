module

public import Veir.Pass
public import Veir.Passes.CheckedDriver
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

/-- The Puddle patterns of the pass, in the order it tries them. The combines come before
`sub_to_add`, which would otherwise rewrite the subtractions some of them match. -/
def postLegalizerPatterns : Array (Puddle.Pattern OpCode) :=
  combinePatterns ++ selectPatterns riscv64LegalizerInfo ++
    #[sub_to_add_pattern riscv64LegalizerInfo, redundant_and_pattern] ++ redundantAndSelectPatterns

/-- The pass: the Puddle patterns, all proved valid, through the module-filtered driver.
`commutativeConstantRHS` is unproven, so not run. Its soundness is
`PostLegalizerCombinerRISCV64Pass.run_sound`. -/
def PostLegalizerCombinerRISCV64Pass.run : PurePass :=
  checkedFunctionsPass "postlegalizer-combiner-riscv64"
    (RewritePattern.GreedyRewritePattern (postLegalizerPatterns.map fun rule => rule.compile.run))

def PostLegalizerCombinerRISCV64Pass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) :=
  ExceptT.mk (pure (PostLegalizerCombinerRISCV64Pass.run ctx op))

def PostLegalizerCombinerRISCV64Pass : Pass OpCode :=
  { name := "postlegalizer-combiner-riscv64"
    description := "Combine legalized gMIR operations for RISC-V 64."
    run := fun _ => PostLegalizerCombinerRISCV64Pass.impl }

end

end Veir
