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

/--
The constant-like operations nested (at any depth) under `op`, in program
order, appended to `acc`. `op` itself is not included.
-/
partial def nestedConstantOps (op : OperationPtr) (ctx : IRContext OpCode)
    (acc : Array OperationPtr := #[]) : Array OperationPtr := Id.run do
  let mut acc := acc
  for region in op.getRegions! ctx do
    let mut block? := region.getFirstBlock! ctx
    while let some block := block? do
      let mut inner? := block.getFirstOp! ctx
      while let some inner := inner? do
        if (inner.getOpType! ctx).isConstantLike then
          acc := acc.push inner
        acc := nestedConstantOps inner ctx acc
        inner? := inner.getNextOp! ctx
      block? := block.getNextBlock! ctx
  return acc

/-- Unique and hoist every constant-like operation nested under `top`. -/
public def run (ctx : WfIRContext OpCode) (top : OperationPtr) :
    WfIRContext OpCode := Id.run do
  let mut ctx := ctx
  let mut canonical : Std.HashMap Key OperationPtr := {}
  let mut lastHoisted : Std.HashMap RegionPtr OperationPtr := {}
  for op in nestedConstantOps top ctx.raw do
    let opType := op.getOpType! ctx.raw
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
    let ip := match lastHoisted[scope]? with
      | some last =>
        match last.getNextOp! ctx.raw with
        | some next => .before next
        | none => .atEnd (last.getParent! ctx.raw).get!
      | none => InsertPoint.atStart! (scope.getFirstBlock! ctx.raw).get! ctx.raw
    lastHoisted := lastHoisted.insert scope op
    if ip ≠ .before op then
      ctx := WfRewriter.detachOp! ctx op
      ctx := WfRewriter.insertOp! ctx op ip
  return ctx

end UniqueConstants
end Veir
