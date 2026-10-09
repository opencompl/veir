module

public import Veir.IR.OpInfo
public import Veir.Dialects.Builtin.OpInfo

/-!
Region isolation scope queries for verification and transformations.
-/

namespace Veir

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/--
Find the region that establishes the nearest `IsolatedFromAbove` scope around
`region`, or `none` when no enclosing operation is isolated. The returned
region is one of the isolated operation's direct regions; different regions of
the same isolated operation are separate scopes.
-/
partial def RegionPtr.nearestIsolatedScope?
    (region : RegionPtr) (ctx : IRContext OpInfo) : Option RegionPtr := do
  let parentOp ← region.getParent! ctx
  if HasOpInfo.isIsolatedFromAbove (parentOp.getOpType! ctx) then
    return region
  let parentRegion ← parentOp.getParentRegion! ctx
  parentRegion.nearestIsolatedScope? ctx

/--
Find the nearest region whose owning operation is known to be isolated from
above or is unregistered. Transformations use this scope to avoid introducing
captures across boundaries whose isolation requirements are unknown.

Different regions of the same operation remain separate scopes; return `none`
when no boundary encloses `region`. Verification uses `nearestIsolatedScope?`
instead, so existing captures in unregistered operations remain legal.
-/
partial def RegionPtr.nearestPossiblyIsolatedScope?
    [HasDialect OpInfo Builtin]
    (region : RegionPtr) (ctx : IRContext OpInfo) : Option RegionPtr := do
  let parentOp ← region.getParent! ctx
  let opType := parentOp.getOpType! ctx
  if HasOpInfo.isIsolatedFromAbove opType ||
      toDialect? Builtin opType == some .unregistered then
    return region
  let parentRegion ← parentOp.getParentRegion! ctx
  parentRegion.nearestPossiblyIsolatedScope? ctx

end

end Veir
