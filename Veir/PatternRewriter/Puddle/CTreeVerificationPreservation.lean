module

public import Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.PatternRewriter.Puddle.Execution
public import Veir.Verifier
public import Veir.Dominance.Basic

public section
namespace Veir.Puddle.CTree

/--
Trusted preservation of verification after a successful compiled rewrite.

We currently assume that whenever a Puddle rewrite is executed successfully, the
resulting module is verified. This is currently an axiom because we miss the necessary
infrastructure in VeIR to prove this property.
-/
axiom Pattern.Valid.compile_preservesVerified
    {rule : Veir.Puddle.Pattern OpCode} (valid : Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root moduleOp : OperationPtr} {region : RegionPtr}
    (rootIn : root.InBounds rewriter.ctx.raw)
    (moduleCode : moduleOp.getOpType! rewriter.ctx.raw = .builtin .module)
    (sourceVerified : rewriter.ctx.Verified moduleOp)
    (rootRooted : root.RootedAt moduleOp rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (rootSSA : region.hasSSADominance rewriter.ctx)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (run : rule.compile.run rewriter root rootIn = some result) :
    result.ctx.Verified moduleOp

end Veir.Puddle.CTree
