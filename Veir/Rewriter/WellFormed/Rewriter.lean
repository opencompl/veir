import Veir.Rewriter.WellFormed.Rewriter.Operation
import Veir.Rewriter.WellFormed.Rewriter.Value

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}

set_option warn.sorry false in
theorem Rewriter.replaceOp?_WellFormed (ctx : IRContext OpInfo) (wf : ctx.WellFormed)
    (oldOp newOp : OperationPtr)
    (oldIn : oldOp.InBounds ctx)
    (newIn : newOp.InBounds ctx)
    (ctxIn : ctx.FieldsInBounds)
    (hpar : (oldOp.get ctx).parent.isSome = true)
    (newCtx : IRContext OpInfo) :
    Rewriter.replaceOp? ctx oldOp newOp oldIn newIn ctxIn hpar = some newCtx →
    newCtx.WellFormed := by
  sorry

set_option warn.sorry false in
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
