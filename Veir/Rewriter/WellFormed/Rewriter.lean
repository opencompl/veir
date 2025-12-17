import Veir.Rewriter.WellFormed.Rewriter.Operation
import Veir.Rewriter.WellFormed.Rewriter.Value

namespace Veir

theorem Rewriter.replaceOp?_WellFormed (ctx : IRContext) (wf : ctx.WellFormed)
    (oldOp newOp : OperationPtr)
    (oldIn : oldOp.InBounds ctx)
    (newIn : newOp.InBounds ctx)
    (ctxIn : ctx.FieldsInBounds)
    (hpar : (oldOp.get ctx).parent.isSome = true)
    (newCtx : IRContext) :
    Rewriter.replaceOp? ctx oldOp newOp oldIn newIn ctxIn hpar = some newCtx →
    newCtx.WellFormed := by
  sorry

theorem BlockPtr.operationList_Rewriter_replaceOp
    (hWf : BlockPtr.operationList blockPtr ctx ctxWellFormed blockInBounds = array)
    (hnewCtx : Rewriter.replaceOp? ctx oldOp newOp oldIn newIn ctxIn hpar = some newCtx) :
      BlockPtr.operationList blockPtr newCtx ctxWellFormed' blockInBounds' =
      if blockPtr = blockPtr' then
        array.erase op
      else
        array := by
  sorry

end Veir
