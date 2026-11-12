module

public import Veir.Pass
public import Veir.PatternRewriter.Basic
public import Veir.Passes.StrictDriver
import Veir.Passes.Legalization.CombinerHelper
import Veir.PatternRewriter.Puddle.Execution

/-!
# RISC-V 64 Pre-Legalizer Combiner

The combines that run on gMIR before RISC-V 64 legalization, as LLVM's
`RISCVPreLegalizerCombiner`.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/lib/Target/RISCV/GISel/RISCVPreLegalizerCombiner.cpp
-/

namespace Veir

public section

/-! ## `llvm.intr.assume`
  An assume only adds UB, so dropping it is always a refinement.
-/
def dropAssumeLocal (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  if op.getOpType! ctx.raw ≠ .llvm .intr__assume then return (ctx, none)
  some (ctx, some (#[], #[]))

def dropAssume := RewritePattern.fromLocalRewrite dropAssumeLocal

/-- The strict pass: the Puddle combines, all proved valid, through the module-filtered driver.
Its soundness is `PreLegalizerCombinerRISCV64Pass.runStrict_sound`. -/
def PreLegalizerCombinerRISCV64Pass.runStrict : PurePass :=
  strictFunctionsPass "prelegalizer-combiner-riscv64"
    (RewritePattern.GreedyRewritePattern (preLegalizerPatterns.map fun rule => rule.compile.run))

def PreLegalizerCombinerRISCV64Pass.impl (strict : Bool) (ctx : WfIRContext OpCode)
    (op : OperationPtr) (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) :=
  if strict then ExceptT.mk (pure (PreLegalizerCombinerRISCV64Pass.runStrict ctx op)) else do
    -- `dropAssume` is unproven, so not run: `#[dropAssume] ++ preLegalizerCombines.map (·.run)`.
    let pattern := RewritePattern.GreedyRewritePattern (preLegalizerCombines.map (·.run))
    match RewritePattern.applyToFunctions pattern ctx op with
    | none => throw "Error while applying the pre-legalizer combines"
    | some ctx => pure ctx

def PreLegalizerCombinerRISCV64Pass : Pass OpCode :=
  { name := "prelegalizer-combiner-riscv64"
    description := "Combine gMIR operations for RISC-V 64 before legalization."
    options := .ofList [
      ("strict", { description := "Only apply the combines proved to refine the module.",
                   defaultValue := false })]
    run := fun options =>
      PreLegalizerCombinerRISCV64Pass.impl ((options.get? "strict").getD false) }

end

end Veir
