module

public import Veir.Pass
public import Veir.Passes.StrictDriver
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
def postLegalizerStrictPatterns : Array (Puddle.Pattern OpCode) :=
  combinePatterns ++ selectPatterns riscv64LegalizerInfo ++
    #[sub_to_add_pattern riscv64LegalizerInfo, redundant_and_pattern] ++ redundantAndSelectPatterns

/-- The strict pass: the Puddle patterns, all proved valid, through the module-filtered driver;
`commutativeConstantRHS` is not run. Its soundness is
`PostLegalizerCombinerRISCV64Pass.runStrict_sound`. -/
def PostLegalizerCombinerRISCV64Pass.runStrict : PurePass :=
  strictFunctionsPass "postlegalizer-combiner-riscv64"
    (RewritePattern.GreedyRewritePattern (postLegalizerStrictPatterns.map fun rule => rule.compile.run))

def PostLegalizerCombinerRISCV64Pass.impl (strict : Bool) (ctx : WfIRContext OpCode)
    (op : OperationPtr) (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) :=
  if strict then ExceptT.mk (pure (PostLegalizerCombinerRISCV64Pass.runStrict ctx op)) else do
    let pattern := RewritePattern.GreedyRewritePattern <|
      (combines ++ selectCombines riscv64LegalizerInfo).map (·.run) ++
      #[(sub_to_add riscv64LegalizerInfo).run, redundant_and.run] ++
      redundant_and_select.map (·.run) ++ #[commutativeConstantRHS]
    match RewritePattern.applyToFunctions pattern ctx op with
    | none => throw "Error while applying the post-legalizer combines"
    | some ctx => pure ctx

def PostLegalizerCombinerRISCV64Pass : Pass OpCode :=
  { name := "postlegalizer-combiner-riscv64"
    description := "Combine legalized gMIR operations for RISC-V 64."
    options := .ofList [
      ("strict", { description := "Only apply the combines proved to refine the module.",
                   defaultValue := false })]
    run := fun options =>
      PostLegalizerCombinerRISCV64Pass.impl ((options.get? "strict").getD false) }

end

end Veir
