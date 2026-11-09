module

public import Veir.PatternRewriter.Basic
public import Veir.Interpreter.Refinement.Basic
public import Veir.Interfaces.RegionKindInterfaces
public import Veir.IRNesting
public import Veir.Verifier

namespace Veir

/-- Every live operation on the worklist belongs to the module. -/
@[expose] public def PatternRewriter.Worklist.RootedIn (worklist : PatternRewriter.Worklist)
    (moduleOp : OperationPtr) (ctx : WfIRContext OpCode) : Prop :=
  ∀ op, some op ∈ worklist.stack → op.InBounds ctx.raw → op.RootedAt moduleOp ctx

/-- Guarantees needed to continue a traversal after one successful rewrite. -/
public structure RewritePattern.ModuleStepResult (moduleOp : OperationPtr) (ctx : WfIRContext OpCode)
    (worklist : PatternRewriter.Worklist) (after : PatternRewriter OpCode) : Prop where
  refines : moduleOp.isModuleRefinedByCTree ctx moduleOp after.ctx
  verified : after.ctx.Verified moduleOp
  code : moduleOp.getOpType! after.ctx.raw = .builtin .module
  detached : moduleOp.getParent! after.ctx.raw = none
  containers : ∀ op : OperationPtr, op.InBounds ctx.raw → 0 < op.getNumRegions! ctx.raw →
    op.RootedAt moduleOp ctx → op.InBounds after.ctx.raw ∧ 0 < op.getNumRegions! after.ctx.raw ∧
      op.RootedAt moduleOp after.ctx
  queued : after.worklist.RootedIn moduleOp after.ctx
  noAction : after.hasDoneAction = false → (after.ctx, after.worklist) = (ctx, worklist)

/-- A single dispatch on an eligible operation preserves the module and the worklist scope. -/
public structure RewritePattern.CorrectStepInModule (pattern : RewritePattern OpCode) : Prop where
  step : ∀ {before after : PatternRewriter OpCode} {moduleOp op : OperationPtr} {region : RegionPtr}
    (bound : op.InBounds before.ctx.raw),
    moduleOp.getOpType! before.ctx.raw = .builtin .module → before.ctx.Verified moduleOp →
    op.RootedAt moduleOp before.ctx → op.getParentRegion! before.ctx.raw = some region →
    region.hasSSADominance before.ctx → op.getNumRegions! before.ctx.raw = 0 →
    before.worklist.RootedIn moduleOp before.ctx → pattern before op bound = some after →
    RewritePattern.ModuleStepResult moduleOp before.ctx before.worklist after

end Veir
