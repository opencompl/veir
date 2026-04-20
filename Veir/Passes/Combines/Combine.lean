import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.RISCVMatching

namespace Veir

/-!
  This file replicates LLVM's pre- and post-legalization GlobalISel combines.
-/

/-! # Lowering Patterns -/

set_option warn.sorry false in
/-- riscv.add x 0 -> x -/
def right_identity_zero_add (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs) := matchRISCVAdd op rewriter.ctx | return rewriter
  let .opResult rhsOp := rhs | none
  let some (cstOp, cst) := matchRISCVLi rhsOp.op rewriter.ctx | return rewriter
  let c := cst.value.value.toNat
  let rewriter ← rewriter.replaceValue (op.getResult 0) lhs sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-! # Pass implementation -/

def RISCVCombines.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[right_identity_zero_add]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ctx

public def RISCVCombines : Pass OpCode :=
  { name := "riscv-combine"
    description :=
      "GlobalISel RISCV combines"
    run := RISCVCombines.impl }
