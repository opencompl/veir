module

public import Veir.Pass
import Veir.Rewriter.WfRewriter

/-!
  # Constant uniquing

  Deduplicate constant-like operations and hoist the survivors to the top of
  their scope.

  The scope of a constant is the nearest enclosing `IsolatedFromAbove` region.
-/

namespace Veir
namespace UniqueConstants

structure Key where
  /-- The constant's opcode together with the properties holding its value. -/
  kind : OpKind OpCode
  resultType : TypeAttr
  scope : RegionPtr
deriving DecidableEq, BEq, Hashable

/--
Find the region that establishes the nearest `IsolatedFromAbove` scope around
`region`. As in MLIR's `getInsertionRegion`, a top-level operation (one not
nested in any region) also establishes a scope, so this returns `none` only
when `region` itself is detached from any operation.
-/
partial def scopeOf? (region : RegionPtr) (ctx : IRContext OpCode) :
    Option RegionPtr := do
  let parentOp ← (region.get! ctx).parent
  if HasOpInfo.isIsolatedFromAbove (parentOp.get! ctx).opType then
    return region
  let some parentRegion := parentOp.getParentRegion! ctx | return region
  scopeOf? parentRegion ctx

/-- Unique and hoist every constant-like operation nested under `top`. -/
public def run (ctx : WfIRContext OpCode) (top : OperationPtr) :
    WfIRContext OpCode := Id.run do
  let mut ctx := ctx
  let mut canonical : Std.HashMap Key OperationPtr := {}
  let mut hoisted : Std.HashSet OperationPtr := {}
  for op in top.nestedOps ctx.raw do
    let opType := op.getOpType! ctx.raw
    if !opType.isConstantLike then continue
    let scope := (scopeOf? (op.getParentRegion! ctx.raw).get! ctx.raw).get!
    let key : Key := {
      kind := ⟨opType, op.getProperties! ctx.raw opType⟩
      resultType := (op.getResult 0 : ValuePtr).getType! ctx.raw
      scope }
    if let some existing := canonical[key]? then
      ctx := WfRewriter.replaceOp! ctx op existing
      continue
    canonical := canonical.insert key op
    hoisted := hoisted.insert op
    let entry := (scope.get! ctx.raw).firstBlock.get!
    let opData := op.get! ctx.raw
    let inPlace :=
      (entry.get! ctx.raw).firstOp == some op ||
      (opData.parent == some entry && opData.prev.any hoisted.contains)
    if !inPlace then
      ctx := WfRewriter.detachOp! ctx op
      ctx := WfRewriter.insertOp! ctx op (InsertPoint.atStart! entry ctx.raw)
  return ctx

end UniqueConstants
end Veir
