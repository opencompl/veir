module

public import Veir.Pass
import Veir.Rewriter.WfRewriter
import Veir.Interfaces.RegionIsolationInterfaces

/-!
  # Constant uniquing

  Deduplicate constant-like operations and hoist the survivors to the top of
  their scope.

  The scope of a constant is the nearest enclosing region whose owner is
  `IsolatedFromAbove` or unregistered, since hoisting out of an unregistered
  operation could introduce an illegal capture. Constants with no such scope
  are left alone.
-/

namespace Veir
namespace UniqueConstants

structure Key where
  /-- The constant's opcode together with the properties holding its value. -/
  kind : OpKind OpCode
  resultType : TypeAttr
  scope : RegionPtr
deriving DecidableEq, BEq, Hashable

/-- Unique and hoist every constant-like operation nested under `top`. -/
public def run (ctx : WfIRContext OpCode) (top : OperationPtr) :
    WfIRContext OpCode := Id.run do
  let mut ctx := ctx
  let mut canonical : Std.HashMap Key OperationPtr := {}
  let mut hoisted : Std.HashSet OperationPtr := {}
  for op in top.nestedOps ctx.raw do
    let opType := op.getOpType! ctx.raw
    if !opType.isConstantLike then continue
    let some scope :=
        (op.getParentRegion! ctx.raw).get!.nearestPossiblyIsolatedScope? ctx.raw
      | continue
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
