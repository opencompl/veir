import Mlir.Core.Basic
import Mlir.Core.WellFormed
import Mlir.Rewriter.Basic

namespace Mlir

theorem OperationPtr.setProperties_WellFormed (op: OperationPtr) (ctx: IRContext) (inBounds: op.InBounds ctx) (newValue: UInt64)
    (hctx : IRContext.WellFormed ctx) :
    (op.setProperties ctx newValue inBounds).WellFormed := by
  sorry

theorem Rewriter.createOp_WellFormed (ctx: IRContext) (opType: Nat)
    (numResults: Nat) (operands: Array ValuePtr) (numRegions: Nat) (properties: UInt64)
    (insertionPoint: Option InsertPoint)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds ctx)
    (hins : insertionPoint.maybe InsertPoint.InBounds ctx)
    (hx : ctx.FieldsInBounds)
    (hctx : IRContext.WellFormed ctx)
    (newCtx : IRContext) (newOp : OperationPtr) :
    Rewriter.createOp ctx opType numResults operands numRegions properties insertionPoint hoper hins hx = some (newCtx, newOp) →
    newCtx.WellFormed := by
  intros heq
  constructor
  case inBounds =>
    sorry
  case valueUseDefChains =>
    sorry
  case blockUseDefChains =>
    sorry
  case opChain =>
    sorry
  case blockChain =>
    sorry
  case operations =>
    sorry
  case blocks =>
    sorry
  case regions =>
    sorry
