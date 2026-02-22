import Veir.IR.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.Basic

namespace Veir

variable {dT : Type} [HasProperties dT]

set_option warn.sorry false in
theorem OperationPtr.setProperties_WellFormed (op: OperationPtr) (ctx: IRContext dT)
    (inBounds: op.InBounds ctx) (newValue : HasProperties.propertiesOf opType) propEq
    (hctx : IRContext.WellFormed ctx) :
    (op.setProperties ctx newValue inBounds propEq).WellFormed := by
  sorry

set_option warn.sorry false in
theorem Rewriter.createOp_WellFormed (ctx: IRContext dT) (opType: dT)
    (resultTypes: Array TypeAttr) (operands: Array ValuePtr) (numRegions: Nat)
    (properties: HasProperties.propertiesOf opType)
    (insertionPoint: Option InsertPoint)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds ctx)
    hblockOper
    hregions
    (hins : insertionPoint.maybe InsertPoint.InBounds ctx)
    (hx : ctx.FieldsInBounds)
    (hctx : IRContext.WellFormed ctx)
    (newCtx : IRContext dT) (newOp : OperationPtr) :
    Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties insertionPoint hoper hblockOper hregions hins hx = some (newCtx, newOp) →
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
