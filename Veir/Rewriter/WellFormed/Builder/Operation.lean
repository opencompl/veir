import Veir.IR.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.Basic

namespace Veir

set_option warn.sorry false in
theorem OperationPtr.setProperties_WellFormed (op: OperationPtr) (ctx: IRContext) (inBounds: op.InBounds ctx) (newValue: UInt64)
    (hctx : IRContext.WellFormed ctx) :
    (op.setProperties ctx newValue inBounds).WellFormed := by
  sorry

set_option warn.sorry false in
theorem Rewriter.createOp_WellFormed (ctx: IRContext) (opType: Nat)
    (resultTypes: Array MlirType) (operands: Array ValuePtr) (numRegions: Nat) (properties: UInt64)
    (insertionPoint: Option InsertPoint)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds ctx)
    hregions
    (hins : insertionPoint.maybe InsertPoint.InBounds ctx)
    (hx : ctx.FieldsInBounds)
    (hctx : IRContext.WellFormed ctx)
    (newCtx : IRContext) (newOp : OperationPtr) :
    Rewriter.createOp ctx opType resultTypes operands regions properties insertionPoint hoper hregions hins hx = some (newCtx, newOp) →
    newCtx.WellFormed := by
  intros heq
  constructor
  case inBounds =>
    sorry
  case valueDefUseChains =>
    sorry
  case blockDefUseChains =>
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
