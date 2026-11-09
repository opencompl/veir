module

public import Veir.PatternRewriter.Basic

namespace Veir.Puddle

/-- Placement policy shared with the standard pattern rewriter. -/
public abbrev rootEligible {OpInfo : Type} [HasOpInfo OpInfo]
    (ctx : WfIRContext OpInfo) (op : OperationPtr) : Bool :=
  op.getNumRegions! ctx.raw == 0 && (op.getParentRegion! ctx.raw).any (·.hasSSADominance ctx)

end Veir.Puddle
