module

public import Veir.Pass
public import Veir.PatternRewriter.Basic
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

def PreLegalizerCombinerRISCV64Pass : Pass OpCode :=
  { name := "prelegalizer-combiner-riscv64"
    description := "Combine gMIR operations for RISC-V 64 before legalization."
    run := fun _ ctx op _ => do
      let pattern := RewritePattern.GreedyRewritePattern <|
        #[dropAssume] ++ preLegalizerCombines.map (·.run)
      match RewritePattern.applyToFunctions pattern ctx op with
      | none => throw "Error while applying the pre-legalizer combines"
      | some ctx => pure ctx }

end

end Veir
