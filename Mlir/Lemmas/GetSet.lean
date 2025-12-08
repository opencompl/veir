import Mlir.Core.Basic
import Mlir.Core.Fields
import Mlir.UseDefChain

namespace Mlir

attribute [local grind cases] ValuePtr OpOperandPtr GenericPtr BlockOperandPtr OpResultPtr BlockArgumentPtr
attribute [local grind] OpOperandPtr.setNextUse OpOperandPtr.setBack OpOperandPtr.setOwner OpOperandPtr.setValue OpOperandPtr.set
attribute [local grind] OpOperandPtrPtr.set
attribute [local grind] ValuePtr.getFirstUse! ValuePtr.getFirstUse ValuePtr.setFirstUse
attribute [local grind] OpResultPtr.get! OpResultPtr.setFirstUse OpResultPtr.set
attribute [local grind] BlockArgumentPtr.get! BlockArgumentPtr.setFirstUse BlockArgumentPtr.set
attribute [local grind] OperationPtr.setOperands OperationPtr.setResults OperationPtr.pushResult
attribute [local grind] BlockPtr.get!
attribute [local grind] Option.maybe

setup_grind_for_basic_proofs

attribute [local grind] OpOperandPtr.get! BlockOperandPtr.get! OpResultPtr.get! BlockArgumentPtr.get! OperationPtr.get!

variable {operation operation' : OperationPtr}
variable {block block' : BlockPtr}
variable {rg rg' : RegionPtr}
variable {opOperand opOperand' : OpOperandPtr}
variable {opOperandPtr opOperandPtr' : OpOperandPtrPtr}
variable {blockOperand blockOperand' : BlockOperandPtr}
variable {value value' : ValuePtr}


@[simp, grind =>]
theorem OperationPtr.get!_OperationPtr_setParentWithCheck
    (heq : operation'.setParentWithCheck ctx parent h' = some newCtx) :
    operation.get! newCtx =
    if operation' = operation then
      { operation.get! ctx with parent := some parent }
    else
      operation.get! ctx
    := by
  unfold OperationPtr.setParentWithCheck at heq
  grind


@[simp, grind =]
theorem OperationPtr.getNumResults_OpOperandPtr_setBack :
    OperationPtr.getNumResults op (OpOperandPtr.setBack operandPtr ctx h₁ v) hop =
    OperationPtr.getNumResults op ctx (by grind) := by
  grind

@[simp, grind =>]
theorem OpOperandPtr.get!_OperationPtr_setParentWithCheck (res : OpOperandPtr)
    (heq : operation.setParentWithCheck ctx h' newNext = some newCtx) :
    res.get! newCtx = res.get! ctx := by
  grind [OperationPtr.setParentWithCheck]


@[simp, grind =]
theorem ValuePtr.get_OpOperandPtr_pushResult(arg : BlockArgumentPtr)
    (h : arg.InBounds (operation.pushResult ctx newResult hop)) :
    arg.get (operation.pushResult ctx newResult hop) h = arg.get ctx := by
  grind


@[simp, grind =>]
theorem BlockArgumentPtr.get!_OperationPtr_setParentWithCheck (res : BlockArgumentPtr)
    (heq : operation.setParentWithCheck ctx h' newNext = some newCtx) :
    res.get! newCtx = res.get! ctx  := by
  grind [OperationPtr.setParentWithCheck]


@[simp, grind =>]
theorem RegionPtr.get!_OperationPtr_setParentWithCheck (rg : RegionPtr)
    (heq : operation.setParentWithCheck ctx h' newNext = some newCtx) :
    rg.get! newCtx = rg.get! ctx  := by
  grind [OperationPtr.setParentWithCheck]

@[simp, grind =>]
theorem BlockArgumentPtr.get_OperationPtr_setParentWithCheck (res : BlockArgumentPtr) (h : res.InBounds ctx)
    (heq : operation.setParentWithCheck ctx h' newNext = some newCtx) :
    res.get newCtx (by grind) = res.get ctx := by
  grind [OperationPtr.setParentWithCheck]


@[simp, grind =>]
theorem OpResultPtr.get!_OperationPtr_setParentWithCheck (res : OpResultPtr)
    (heq : operation.setParentWithCheck ctx h' newNext = some newCtx) :
    res.get! newCtx = res.get! ctx := by
  grind [OperationPtr.setParentWithCheck]
