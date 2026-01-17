import Veir.IR.Basic
import Veir.IR.Fields
import Veir.Rewriter.LinkedList.Basic

/-
 - The getters we consider are:
 - * IRContext.topLevelOp
 - * BlockPtr.get! optionally replaced by the following special cases:
 -   * Block.firstUse
 -   * Block.prev
 -   * Block.next
 -   * Block.parent
 -   * Block.firstOp
 -   * Block.lastOp
 - * OperationPtr.get! optionally replaced by the following special cases:
 -   * Operation.prev
 -   * Operation.next
 -   * Operation.parent
 -   * Operation.opType
 -   * Operation.attrs
 -   * Operation.properties
 - * OperationPtr.getNumResults!
 - * OpResultPtr.get!
 - * OperationPtr.getNumOperands!
 - * OpOperandPtr.get! optionally replaced by the following special case:
 - * OperationPtr.getNumSuccessors!
 - * BlockOperandPtr.get!
 - * OperationPtr.getNumRegions!
 - * OperationPtr.getRegion!
 - * BlockOperandPtrPtr.get!
 - * BlockPtr.getNumArguments!
 - * BlockArgumentPtr.get!
 - * RegionPtr.get! optionally replaced by the following special cases:
 -   * firstBlock
 -   * lastBlock
 -   * parent
 - * ValuePtr.getFirstUse!
 - * ValuePtr.getType!
 - * OpOperandPtrPtr.get!
 -/
namespace Veir

variable {op op' operation operation' : OperationPtr}
variable {block block' : BlockPtr}
variable {rg rg' : RegionPtr}
variable {opOperand opOperand' : OpOperandPtr}
variable {opOperandPtr opOperandPtr' : OpOperandPtrPtr}
variable {blockOperand blockOperand' : BlockOperandPtr}
variable {value value' : ValuePtr}

/- OpOperandPtr.removeFromCurrent -/
attribute [local grind] OpOperandPtr.removeFromCurrent

@[simp, grind =]
theorem IRContext.topLevelOp_OpOperandPtr_removeFromCurrent :
    (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).topLevelOp =
    ctx.topLevelOp := by
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.properties!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).properties =
    (operation.get! ctx).properties := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumResults! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumResults! ctx := by
  grind

@[grind =]
theorem OpResultPtr.get!_OpOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.get! ctx).back = .valueFirstUse (.opResult opResult) then
      { opResult.get! ctx with firstUse := (opOperand'.get! ctx).nextUse }
    else
      opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumOperands! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumOperands! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.get!_OpOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    { opOperand.get! ctx with
        back :=
          if (opOperand'.get! ctx).nextUse = some opOperand then
            (opOperand'.get! ctx).back
          else
            (opOperand.get! ctx).back
        nextUse :=
          if (opOperand'.get! ctx).back = .operandNextUse opOperand then
            (opOperand'.get! ctx).nextUse
          else
            (opOperand.get! ctx).nextUse
    } := by
  simp [removeFromCurrent]
  split
  · split
    · grind
    · split
      · grind
      · -- TODO: Why doesn't 'grind' work here?
        simp only [get!_OpOperandPtrPtr_set, ite_eq_right_iff]
        grind
  · split
    · grind
    · split
      · grind
      · simp [OpOperandPtr.get!_OpOperandPtr_setBack]
        split
        · grind
        · simp only [get!_OpOperandPtrPtr_set, ite_eq_right_iff]
          grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumSuccessors! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OpOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumRegions! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getRegion! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OpOperandPtr_removeFromCurrent {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OpOperandPtr_removeFromCurrent {block : BlockPtr} {hop} :
    block.getNumArguments! (opOperand'.removeFromCurrent ctx newOperands hop) =
    block.getNumArguments! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.get!_OpOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.get! ctx).back = .valueFirstUse (.blockArgument blockArg) then
      { blockArg.get! ctx with firstUse := (opOperand'.get! ctx).nextUse }
    else
      blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpOperandPtr_removeFromCurrent {region : RegionPtr} :
    region.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    region.get! ctx := by
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_OpOperandPtr_removeFromCurrent {value : ValuePtr} :
    value.getFirstUse! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.get! ctx).back = .valueFirstUse value then
      (opOperand'.get! ctx).nextUse
    else
      value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OpOperandPtr_removeFromCurrent {value : ValuePtr} :
    value.getType! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_OpOperandPtr_removeFromCurrent {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    if opOperandPtr = (opOperand'.get! ctx).back then
      (opOperand'.get! ctx).nextUse
    else
      opOperandPtr.get! ctx := by
  grind

/- OpOperandPtr.insertIntoCurrent -/
attribute [local grind] OpOperandPtr.insertIntoCurrent

@[simp, grind =]
theorem IRContext.topLevelOp_OpOperandPtr_insertIntoCurrent :
    (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).topLevelOp =
    ctx.topLevelOp := by
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.properties!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).properties =
    (operation.get! ctx).properties := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumResults! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumResults! ctx := by
  grind

@[grind =]
theorem OpResultPtr.get!_OpOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.get! ctx).value = (.opResult opResult) then
      { opResult.get! ctx with firstUse := opOperand' }
    else
      opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumOperands! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumOperands! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.get!_OpOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    { opOperand.get! ctx with
        back :=
          if (opOperand'.get! ctx).value.getFirstUse! ctx = some opOperand then
            .operandNextUse opOperand'
          else if opOperand' = opOperand then
            .valueFirstUse ((opOperand'.get! ctx).value)
          else
            (opOperand.get! ctx).back
        nextUse :=
          if opOperand' = opOperand then
            (opOperand'.get! ctx).value.getFirstUse! ctx
          else
            (opOperand.get! ctx).nextUse
    } := by
  simp only [insertIntoCurrent]
  by_cases h: opOperand = opOperand'
  · grind
  · simp only [← get!_eq_get, ← ValuePtr.getFirstUse!_eq_getFirstUse, ValuePtr.getFirstUse!_OpOperandPtr_setBack]
    split
    · rename_i h₁
      simp only [← get!_eq_get, ← ValuePtr.getFirstUse!_eq_getFirstUse, ValuePtr.getFirstUse!_OpOperandPtr_setBack] at h₁
      simp only [get!_ValuePtr_setFirstUse]
      simp only [OpOperandPtr.get!_OpOperandPtr_setNextUse, h, ↓reduceIte]
      simp only [get!_OpOperandPtr_setBack, h, ↓reduceIte]
      simp only [Ne.symm h, ↓reduceIte]
      simp only [h₁, reduceCtorEq, ↓reduceIte]
    · rename_i ptr h₁
      simp only [← get!_eq_get, ← ValuePtr.getFirstUse!_eq_getFirstUse, ValuePtr.getFirstUse!_OpOperandPtr_setBack] at h₁
      simp [h₁]
      by_cases heq: ptr = opOperand
      · grind
      · simp only [Ne.symm h, ↓reduceIte, heq]
        simp only [get!_OpOperandPtr_setBack, Ne.symm heq, ↓reduceIte, get!_ValuePtr_setFirstUse]
        simp only [get!_OpOperandPtr_setNextUse, h, ↓reduceIte]
        simp only [get!_OpOperandPtr_setBack]
        --grind    -- Why does 'grind' not work here?
        simp only [h, ↓reduceIte]

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumSuccessors! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OpOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumRegions! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getRegion! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OpOperandPtr_insertIntoCurrent {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} {hop} :
    block.getNumArguments! (opOperand'.insertIntoCurrent ctx newOperands hop) =
    block.getNumArguments! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.get!_OpOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.get! ctx).value = (.blockArgument blockArg) then
      { blockArg.get! ctx with firstUse := opOperand' }
    else
      blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpOperandPtr_insertIntoCurrent {region : RegionPtr} :
    region.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    region.get! ctx := by
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_OpOperandPtr_insertIntoCurrent {value : ValuePtr} :
    value.getFirstUse! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.get! ctx).value = value then
      some opOperand'
    else
      value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OpOperandPtr_insertIntoCurrent {value : ValuePtr} :
    value.getType! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_OpOperandPtr_insertIntoCurrent {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    if opOperandPtr = .operandNextUse opOperand' then
      (opOperand'.get! ctx).value.getFirstUse! ctx
    else if opOperandPtr = .valueFirstUse ((opOperand'.get! ctx).value) then
      some opOperand'
    else
      opOperandPtr.get! ctx := by
  grind

section BlockOperandPtr.removeFromCurrent

attribute [local grind] BlockOperandPtr.removeFromCurrent

@[simp, grind =]
theorem IRContext.topLevelOp_BlockOperandPtr_removeFromCurrent :
    (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).topLevelOp =
    ctx.topLevelOp := by
  grind

@[grind =]
theorem BlockPtr.firstUse!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).firstUse =
    if (blockOperand'.get! ctx).back = .blockFirstUse block then
      (blockOperand'.get! ctx).nextUse
    else
      (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.properties!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).properties =
    (operation.get! ctx).properties := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumResults! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumOperands! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumSuccessors! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    operation.getNumSuccessors! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.get!_BlockOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.get! (blockOperand'.removeFromCurrent ctx hblockOperand' ctxInBounds) =
    { blockOperand.get! ctx with
        back :=
          if (blockOperand'.get! ctx).nextUse = some blockOperand then
            (blockOperand'.get! ctx).back
          else
            (blockOperand.get! ctx).back
        nextUse :=
          if (blockOperand'.get! ctx).back = .blockOperandNextUse blockOperand then
            (blockOperand'.get! ctx).nextUse
          else
            (blockOperand.get! ctx).nextUse
    } := by
  simp [removeFromCurrent]
  split
  · split
    · grind
    · split
      · grind
      · -- TODO: Why doesn't 'grind' work here?
        simp only [get!_BlockOperandPtrPtr_set, ite_eq_right_iff]
        grind
  · split
    · grind
    · split
      · grind
      · simp only [get!_BlockOperandPtr_setBack]
        split
        · grind
        · simp only [get!_BlockOperandPtrPtr_set, ite_eq_right_iff]
          grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumRegions! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getRegion! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) i =
    operation.getRegion! ctx i := by
  grind

@[grind =]
theorem BlockOperandPtrPtr.get!_BlockOperandPtr_removeFromCurrent {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    if blockOperandPtr = (blockOperand'.get! ctx).back then
      (blockOperand'.get! ctx).nextUse
    else
      blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} {hop} :
    block.getNumArguments! (blockOperand'.removeFromCurrent ctx newOperands hop) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockOperandPtr_removeFromCurrent {region : RegionPtr} :
    region.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockOperandPtr_removeFromCurrent {value : ValuePtr} :
    value.getFirstUse! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockOperandPtr_removeFromCurrent {value : ValuePtr} :
    value.getType! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockOperandPtr_removeFromCurrent {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    opOperandPtr.get! ctx := by
  grind

end BlockOperandPtr.removeFromCurrent

section BlockOperandPtr.insertIntoCurrent

attribute [local grind] BlockOperandPtr.insertIntoCurrent

@[simp, grind =]
theorem IRContext.topLevelOp_BlockOperandPtr_insertIntoCurrent :
    (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).topLevelOp =
    ctx.topLevelOp := by
  grind

@[grind =]
theorem BlockPtr.firstUse!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).firstUse =
    if (blockOperand'.get! ctx).value = block then
      some blockOperand'
    else
      (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.properties!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).properties =
    (operation.get! ctx).properties := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumResults! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumOperands! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumSuccessors! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    operation.getNumSuccessors! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    { blockOperand.get! ctx with
        back :=
          if ((blockOperand'.get! ctx).value.get! ctx).firstUse = some blockOperand then
            .blockOperandNextUse blockOperand'
          else if blockOperand' = blockOperand then
            .blockFirstUse ((blockOperand'.get! ctx).value)
          else
            (blockOperand.get! ctx).back
        nextUse :=
          if blockOperand' = blockOperand then
            ((blockOperand'.get! ctx).value.get! ctx).firstUse
          else
            (blockOperand.get! ctx).nextUse
    } := by
  simp only [insertIntoCurrent]
  by_cases h: blockOperand = blockOperand'
  · grind
  · simp only [← get!_eq_get, ← BlockPtr.get!_eq_get, BlockPtr.get!_BlockOperandPtr_setBack]
    split
    · rename_i h₁
      simp only [← get!_eq_get, ← BlockPtr.get!_eq_get, BlockPtr.get!_BlockOperandPtr_setBack] at h₁
      simp only [get!_BlockPtr_setFirstUse, get!_BlockOperandPtr_setNextUse, h, ↓reduceIte,
        get!_BlockOperandPtr_setBack]
      simp only [Ne.symm h, ↓reduceIte]
      simp only [h₁, reduceCtorEq, ↓reduceIte]
    · rename_i ptr h₁
      simp only [← get!_eq_get, ← BlockPtr.get!_eq_get, BlockPtr.get!_BlockOperandPtr_setBack] at h₁
      simp [h₁]
      by_cases heq: ptr = blockOperand
      · grind
      · simp only [Ne.symm h, ↓reduceIte, heq]
        simp only [get!_BlockOperandPtr_setBack, Ne.symm heq, ↓reduceIte, get!_BlockPtr_setFirstUse]
        simp only [get!_BlockOperandPtr_setNextUse, h, ↓reduceIte]
        simp only [get!_BlockOperandPtr_setBack]
        --grind    -- Why does 'grind' not work here?
        simp only [h, ↓reduceIte]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumRegions! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getRegion! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) i =
    operation.getRegion! ctx i := by
  grind

@[grind =]
theorem BlockOperandPtrPtr.get!_BlockOperandPtr_insertIntoCurrent {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    if blockOperandPtr = .blockOperandNextUse blockOperand' then
      ((blockOperand'.get! ctx).value.get! ctx).firstUse
    else if blockOperandPtr = .blockFirstUse ((blockOperand'.get! ctx).value) then
      some blockOperand'
    else
      blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} {hop} :
    block.getNumArguments! (blockOperand'.insertIntoCurrent ctx newOperands hop) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockOperandPtr_insertIntoCurrent {region : RegionPtr} :
    region.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockOperandPtr_insertIntoCurrent {value : ValuePtr} :
    value.getFirstUse! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockOperandPtr_insertIntoCurrent {value : ValuePtr} :
    value.getType! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockOperandPtr_insertIntoCurrent {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    opOperandPtr.get! ctx := by
  grind

end BlockOperandPtr.insertIntoCurrent

/- OperationPtr.linkBetween -/
section linkBetween
attribute [local grind] OperationPtr.linkBetween

@[simp, grind =]
theorem IRContext.topLevelOp_OperationPtr_linkBetween :
    (op'.linkBetween ctx prev next selfIn prevIn nextIn).topLevelOp =
    ctx.topLevelOp := by
  -- TODO: Why does grind need an explicit unfold here?
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_linkBetween {block : BlockPtr} :
    block.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    block.get! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[grind =]
theorem OperationPtr.prev!_OperationPtr_linkBetween {operation : OperationPtr} :
    (operation.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn)).prev =
    if operation = next then
      some op'
    else if operation = op' then
      prev
    else
      (operation.get! ctx).prev := by
  simp only [OperationPtr.linkBetween]
  grind

@[grind =]
theorem OperationPtr.next!_OperationPtr_linkBetween {operation : OperationPtr} :
    (operation.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn)).next =
    if operation = prev then
      some op'
    else if operation = op' then
      next
    else
      (operation.get! ctx).next := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OperationPtr_linkBetween {operation : OperationPtr} :
    (operation.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn)).parent =
    (operation.get! ctx).parent := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OperationPtr_linkBetween {operation : OperationPtr} :
    (operation.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn)).opType =
    (operation.get! ctx).opType := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OperationPtr_linkBetween {operation : OperationPtr} :
    (operation.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.properties!_OperationPtr_linkBetween {operation : OperationPtr} :
    (operation.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn)).properties =
    (operation.get! ctx).properties := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getNumResults! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getNumResults! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpResultPtr.get!_OperationPtr_linkBetween {opResult : OpResultPtr} :
    opResult.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    opResult.get! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getNumOperands! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getNumOperands! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_OperationPtr_linkBetween {opOperand : OpOperandPtr} :
    opOperand.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    opOperand.get! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getNumSuccessors! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getNumSuccessors! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OperationPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    blockOperand.get! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getNumRegions! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getNumRegions! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getRegion! (op'.linkBetween ctx prev next selfIn prevIn nextIn) i =
    operation.getRegion! ctx i := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_linkBetween {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    blockOperandPtr.get! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_linkBetween {block : BlockPtr} :
    block.getNumArguments! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    block.getNumArguments! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OperationPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    blockArg.get! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_linkBetween {region : RegionPtr} :
    region.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    region.get! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_linkBetween {value : ValuePtr} :
    value.getFirstUse! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    value.getFirstUse! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OperationPtr_linkBetween {value : ValuePtr} :
    value.getType! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    value.getType! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_linkBetween {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    opOperandPtr.get! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

end linkBetween

section setParentWithCheck

/- OperationPtr.setParentWithCheck -/
attribute [local grind] OperationPtr.setParentWithCheck

@[simp]
theorem IRContext.topLevelOp_OperationPtr_setParentWithCheck :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    newCtx.topLevelOp = ctx.topLevelOp := by
  grind

grind_pattern IRContext.topLevelOp_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, newCtx.topLevelOp

@[simp]
theorem BlockPtr.get!_OperationPtr_setParentWithCheck {block : BlockPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (block.get! newCtx) = (block.get! ctx) := by
  grind

grind_pattern BlockPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, block.get! newCtx

@[simp]
theorem OperationPtr.prev!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (operation.get! newCtx).prev = (operation.get! ctx).prev := by
  grind

grind_pattern OperationPtr.prev!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.get! newCtx).prev

@[simp]
theorem OperationPtr.next!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (operation.get! newCtx).next = (operation.get! ctx).next := by
  simp only [OperationPtr.setParentWithCheck]
  grind

grind_pattern OperationPtr.next!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.get! newCtx).next

@[grind →]
theorem OperationPtr.parent!_of_OperationPtr_setParentWithCheck_eq :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (op'.get! ctx).parent = none := by
  grind

theorem OperationPtr.parent!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (operation.get! newCtx).parent =
    if operation = op' then
      some newParent
    else
      (operation.get! ctx).parent := by
  grind

grind_pattern OperationPtr.parent!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.get! newCtx).parent

@[simp]
theorem OperationPtr.opType!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (operation.get! newCtx).opType = (operation.get! ctx).opType := by
  grind

grind_pattern OperationPtr.opType!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.get! newCtx).opType

@[simp]
theorem OperationPtr.attrs!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (operation.get! newCtx).attrs = (operation.get! ctx).attrs := by
  grind

grind_pattern OperationPtr.attrs!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.get! newCtx).attrs

@[simp]
theorem OperationPtr.properties!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (operation.get! newCtx).properties = (operation.get! ctx).properties := by
  grind

grind_pattern OperationPtr.properties!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.get! newCtx).properties

@[simp]
theorem OperationPtr.getNumResults!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getNumResults! newCtx = operation.getNumResults! ctx := by
  grind

grind_pattern OperationPtr.getNumResults!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumResults! newCtx

@[simp]
theorem OpResultPtr.get!_OperationPtr_setParentWithCheck {opResult : OpResultPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    opResult.get! newCtx = opResult.get! ctx := by
  grind

grind_pattern OpResultPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, opResult.get! newCtx

@[simp]
theorem OperationPtr.getNumOperands!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  grind

grind_pattern OperationPtr.getNumOperands!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumOperands! newCtx

@[simp]
theorem OpOperandPtr.get!_OperationPtr_setParentWithCheck {operand : OpOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  grind

grind_pattern OpOperandPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.get! newCtx

@[simp]
theorem OperationPtr.getNumSuccessors!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getNumSuccessors! newCtx = operation.getNumSuccessors! ctx := by
  grind

grind_pattern OperationPtr.getNumSuccessors!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumSuccessors! newCtx

@[simp]
theorem BlockOperandPtr.get!_OperationPtr_setParentWithCheck {operand : BlockOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  grind

grind_pattern BlockOperandPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.get! newCtx

@[simp]
theorem OperationPtr.getNumRegions!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getNumRegions! newCtx = operation.getNumRegions! ctx := by
  grind

grind_pattern OperationPtr.getNumRegions!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumRegions! newCtx

@[simp]
theorem OperationPtr.getRegion!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getRegion! newCtx i = operation.getRegion! ctx i := by
  grind

grind_pattern OperationPtr.getRegion!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getRegion! newCtx i

@[simp]
theorem BlockOperandPtrPtr.get!_OperationPtr_setParentWithCheck {operandPtr : BlockOperandPtrPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operandPtr.get! newCtx = operandPtr.get! ctx := by
  grind

grind_pattern BlockOperandPtrPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operandPtr.get! newCtx

@[simp]
theorem BlockPtr.getNumArguments!_OperationPtr_setParentWithCheck {block : BlockPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    block.getNumArguments! newCtx = block.getNumArguments! ctx := by
  grind

grind_pattern BlockPtr.getNumArguments!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, block.getNumArguments! newCtx

@[simp]
theorem BlockArgumentPtr.get!_OperationPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    blockArg.get! newCtx = blockArg.get! ctx := by
  grind

grind_pattern BlockArgumentPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, blockArg.get! newCtx

@[simp]
theorem RegionPtr.get!_OperationPtr_setParentWithCheck {region : RegionPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    region.get! newCtx = region.get! ctx := by
  grind

grind_pattern RegionPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, region.get! newCtx

@[simp]
theorem ValuePtr.getFirstUse!_OperationPtr_setParentWithCheck {value : ValuePtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    value.getFirstUse! newCtx = value.getFirstUse! ctx := by
  grind

grind_pattern ValuePtr.getFirstUse!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, value.getFirstUse! newCtx

@[simp] -- No grind because of Unit
theorem ValuePtr.getType!_OperationPtr_setParentWithCheck {value : ValuePtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    value.getType! newCtx = value.getType! ctx := by
  grind

grind_pattern ValuePtr.getType!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, value.getType! newCtx

@[simp]
theorem OpOperandPtrPtr.get!_OperationPtr_setParentWithCheck {opOperandPtr : OpOperandPtrPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    opOperandPtr.get! newCtx = opOperandPtr.get! ctx := by
  grind

grind_pattern OpOperandPtrPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, opOperandPtr.get! newCtx

end setParentWithCheck

section linkBetweenWithParent

/- OperationPtr.linkBetweenWithParent -/
attribute [local grind] OperationPtr.linkBetweenWithParent

@[simp]
theorem IRContext.topLevelOp_OperationPtr_linkBetweenWithParent :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    newCtx.topLevelOp = ctx.topLevelOp := by
  grind

grind_pattern IRContext.topLevelOp_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, newCtx.topLevelOp

@[simp]
theorem BlockPtr.firstUse!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).firstUse = (block.get! ctx).firstUse
    := by
  grind

grind_pattern BlockPtr.firstUse!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).firstUse

@[simp]
theorem BlockPtr.prev!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).prev = (block.get! ctx).prev
    := by
  grind

grind_pattern BlockPtr.prev!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).prev

@[simp]
theorem BlockPtr.next!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).next = (block.get! ctx).next
    := by
  grind

grind_pattern BlockPtr.next!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).next

@[grind →]
theorem OperationPtr.parent!_of_OperationPtr_linkBetweenWithParent_eq :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (op'.get! ctx).parent = none := by
  grind

@[simp]
theorem BlockPtr.parent!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).parent = (block.get! ctx).parent := by
  grind

grind_pattern BlockPtr.parent!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).parent

theorem BlockPtr.firstOp!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).firstOp =
    if parent = block ∧ prev = none then
      some op'
    else
      (block.get! ctx).firstOp := by
  grind

grind_pattern BlockPtr.firstOp!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).firstOp

theorem BlockPtr.lastOp!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).lastOp =
    if parent = block ∧ next = none then
      some op'
    else
      (block.get! ctx).lastOp := by
  grind

grind_pattern BlockPtr.lastOp!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).lastOp

theorem OperationPtr.prev!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx).prev =
    if operation = next then
      some op'
    else if operation = op' then
      prev
    else
      (operation.get! ctx).prev := by
  grind

grind_pattern OperationPtr.prev!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.get! newCtx).prev

theorem OperationPtr.next!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx).next =
    if operation = prev then
      some op'
    else if operation = op' then
      next
    else
      (operation.get! ctx).next := by
  grind

grind_pattern OperationPtr.next!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.get! newCtx).next

theorem OperationPtr.parent!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx).parent =
    if operation = op' then
      some parent
    else
      (operation.get! ctx).parent := by
  grind

grind_pattern OperationPtr.parent!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.get! newCtx).parent

@[simp]
theorem OperationPtr.opType!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx).opType = (operation.get! ctx).opType := by
  grind

grind_pattern OperationPtr.opType!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.get! newCtx).opType

@[simp]
theorem OperationPtr.attrs!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx).attrs = (operation.get! ctx).attrs := by
  grind

grind_pattern OperationPtr.attrs!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.get! newCtx).attrs

@[simp]
theorem OperationPtr.properties!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx).properties = (operation.get! ctx).properties := by
  grind

grind_pattern OperationPtr.properties!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.get! newCtx).properties

@[simp]
theorem OperationPtr.getNumResults!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumResults! newCtx = operation.getNumResults! ctx := by
  grind

grind_pattern OperationPtr.getNumResults!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumResults! newCtx

@[simp]
theorem OpResultPtr.get!_OperationPtr_linkBetweenWithParent {opResult : OpResultPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    opResult.get! newCtx = opResult.get! ctx := by
  grind

grind_pattern OpResultPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opResult.get! newCtx

@[simp]
theorem OperationPtr.getNumOperands!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  grind

grind_pattern OperationPtr.getNumOperands!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumOperands! newCtx

@[simp]
theorem OpOperandPtr.get!_OperationPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  grind

grind_pattern OpOperandPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.get! newCtx

@[simp]
theorem OperationPtr.getNumSuccessors!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumSuccessors! newCtx = operation.getNumSuccessors! ctx := by
  grind

grind_pattern OperationPtr.getNumSuccessors!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumSuccessors! newCtx

@[simp]
theorem BlockOperandPtr.get!_OperationPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  grind

grind_pattern BlockOperandPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.get! newCtx

@[simp]
theorem OperationPtr.getNumRegions!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumRegions! newCtx = operation.getNumRegions! ctx := by
  grind

grind_pattern OperationPtr.getNumRegions!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumRegions! newCtx

@[simp]
theorem OperationPtr.getRegion!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getRegion! newCtx i = operation.getRegion! ctx i := by
  grind

grind_pattern OperationPtr.getRegion!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getRegion! newCtx i

@[simp]
theorem BlockOperandPtrPtr.get!_OperationPtr_linkBetweenWithParent {operandPtr : BlockOperandPtrPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operandPtr.get! newCtx = operandPtr.get! ctx := by
  grind

grind_pattern BlockOperandPtrPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operandPtr.get! newCtx

@[simp]
theorem BlockPtr.getNumArguments!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    block.getNumArguments! newCtx = block.getNumArguments! ctx := by
  grind

grind_pattern BlockPtr.getNumArguments!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, block.getNumArguments! newCtx

@[simp]
theorem BlockArgumentPtr.get!_OperationPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    blockArg.get! newCtx = blockArg.get! ctx := by
  grind

grind_pattern BlockArgumentPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, blockArg.get! newCtx

@[simp]
theorem RegionPtr.get!_OperationPtr_linkBetweenWithParent {region : RegionPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    region.get! newCtx = region.get! ctx := by
  grind

grind_pattern RegionPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, region.get! newCtx

@[simp]
theorem ValuePtr.getFirstUse!_OperationPtr_linkBetweenWithParent {value : ValuePtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    value.getFirstUse! newCtx = value.getFirstUse! ctx := by
  grind

grind_pattern ValuePtr.getFirstUse!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, value.getFirstUse! newCtx

theorem ValuePtr.getType!_OperationPtr_linkBetweenWithParent {value : ValuePtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    value.getType! newCtx = value.getType! ctx := by
  grind

grind_pattern ValuePtr.getType!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, value.getType! newCtx

@[simp]
theorem OpOperandPtrPtr.get!_OperationPtr_linkBetweenWithParent {opOperandPtr : OpOperandPtrPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    opOperandPtr.get! newCtx = opOperandPtr.get! ctx := by
  grind

grind_pattern OpOperandPtrPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opOperandPtr.get! newCtx

end linkBetweenWithParent

/- BlockPtr.linkBetween -/
section linkBetween

unseal BlockPtr.linkBetween
attribute [local grind] BlockPtr.linkBetween

@[simp, grind =]
theorem IRContext.topLevelOp_BlockPtr_linkBetween :
    (block'.linkBetween ctx prev next selfIn prevIn nextIn).topLevelOp =
    ctx.topLevelOp := by
  -- TODO: Why does grind need an explicit unfold here?
  simp only [BlockPtr.linkBetween]
  grind

--  -   * Block.firstUse
--  -   * Block.prev
--  -   * Block.next
--  -   * Block.parent
--  -   * Block.firstOp
--  -   * Block.lastOp

@[simp, grind =]
theorem BlockPtr.firstUse!_BlockPtr_linkBetween {block : BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn)).firstUse =
    (block.get! ctx).firstUse := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.prev!_BlockPtr_linkBetween {block : BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn)).prev =
    if block =  next then
      some block'
    else if block = block' then
      prev
    else
      (block.get! ctx).prev := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.next!_BlockPtr_linkBetween {block : BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn)).next =
    if block =  prev then
      some block'
    else if block = block' then
      next
    else
      (block.get! ctx).next := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.parent!_BlockPtr_linkBetween {block : BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn)).parent =
    (block.get! ctx).parent := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockPtr_linkBetween {block : BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn)).firstOp =
    (block.get! ctx).firstOp := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockPtr_linkBetween {block : BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn)).lastOp =
    (block.get! ctx).lastOp := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.get!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.get! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getNumResults! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = operation.getNumResults! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockPtr_linkBetween {opResult : OpResultPtr} :
    opResult.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    opResult.get! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getNumOperands! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getNumOperands! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockPtr_linkBetween {opOperandPtr : OpOperandPtr} :
    opOperandPtr.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    opOperandPtr.get! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getNumSuccessors! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getNumSuccessors! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_BlockPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    blockOperand.get! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getNumRegions! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getNumRegions! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getRegion! (block'.linkBetween ctx prev next selfIn prevIn nextIn) i =
    operation.getRegion! ctx i := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockPtr_linkBetween {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    blockOperandPtr.get! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockPtr_linkBetween {block : BlockPtr} :
    block.getNumArguments! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    block.getNumArguments! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    blockArg.get! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockPtr_linkBetween {region : RegionPtr} :
    region.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    region.get! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockPtr_linkBetween {value : ValuePtr} :
    value.getFirstUse! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    value.getFirstUse! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockPtr_linkBetween {value : ValuePtr} :
    value.getType! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    value.getType! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockPtr_linkBetween {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    opOperandPtr.get! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

end linkBetween

section setParentWithCheck

/- OperationPtr.setParentWithCheck -/
unseal BlockPtr.setParentWithCheck
attribute [local grind] BlockPtr.setParentWithCheck

@[simp]
theorem IRContext.topLevelOp_BlockPtr_setParentWithCheck :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    newCtx.topLevelOp = ctx.topLevelOp := by
  grind

grind_pattern IRContext.topLevelOp_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, newCtx.topLevelOp

theorem BlockPtr.firstUse!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (block.get! newCtx).firstUse = (block.get! ctx).firstUse := by
  grind

grind_pattern BlockPtr.firstUse!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx).firstUse

theorem BlockPtr.prev!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (block.get! newCtx).prev = (block.get! ctx).prev := by
  grind

grind_pattern BlockPtr.prev!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx).prev

theorem BlockPtr.next!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (block.get! newCtx).next = (block.get! ctx).next := by
  grind

grind_pattern BlockPtr.next!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx).next

theorem BlockPtr.parent!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (block.get! newCtx).parent =
    if block = block' then
      some newParent
    else
      (block.get! ctx).parent := by
  grind

grind_pattern BlockPtr.parent!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx).parent

theorem BlockPtr.firstOp!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (block.get! newCtx).firstOp = (block.get! ctx).firstOp := by
  grind

grind_pattern BlockPtr.firstOp!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx).firstOp

theorem BlockPtr.lastOp!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (block.get! newCtx).lastOp = (block.get! ctx).lastOp := by
  grind

grind_pattern BlockPtr.lastOp!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx).lastOp

@[simp]
theorem OperationPtr.get!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.get! newCtx = operation.get! ctx := by
  grind

grind_pattern OperationPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.get! newCtx

@[simp]
theorem OperationPtr.getNumResults!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getNumResults! newCtx = operation.getNumResults! ctx := by
  grind

grind_pattern OperationPtr.getNumResults!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumResults! newCtx

@[simp]
theorem OpResultPtr.get!_BlockPtr_setParentWithCheck {opResult : OpResultPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    opResult.get! newCtx = opResult.get! ctx := by
  grind

grind_pattern OpResultPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, opResult.get! newCtx

@[simp]
theorem OperationPtr.getNumOperands!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  grind

grind_pattern OperationPtr.getNumOperands!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumOperands! newCtx

@[simp]
theorem OpOperandPtr.get!_BlockPtr_setParentWithCheck {operand : OpOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  grind

grind_pattern OpOperandPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.get! newCtx

@[simp]
theorem OperationPtr.getNumSuccessors!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getNumSuccessors! newCtx = operation.getNumSuccessors! ctx := by
  grind

grind_pattern OperationPtr.getNumSuccessors!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumSuccessors! newCtx

@[simp]
theorem BlockOperandPtr.get!_BlockPtr_setParentWithCheck {operand : BlockOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  grind

grind_pattern BlockOperandPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.get! newCtx

@[simp]
theorem OperationPtr.getNumRegions!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getNumRegions! newCtx = operation.getNumRegions! ctx := by
  grind

grind_pattern OperationPtr.getNumRegions!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumRegions! newCtx

@[simp]
theorem OperationPtr.getRegion!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getRegion! newCtx i = operation.getRegion! ctx i := by
  grind

grind_pattern OperationPtr.getRegion!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getRegion! newCtx i

@[simp]
theorem BlockOperandPtrPtr.get!_BlockPtr_setParentWithCheck {operandPtr : BlockOperandPtrPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operandPtr.get! newCtx = operandPtr.get! ctx := by
  grind

grind_pattern BlockOperandPtrPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operandPtr.get! newCtx

@[simp]
theorem BlockPtr.getNumArguments!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    block.getNumArguments! newCtx = block.getNumArguments! ctx := by
  grind

grind_pattern BlockPtr.getNumArguments!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, block.getNumArguments! newCtx

@[simp]
theorem BlockArgumentPtr.get!_BlockPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    blockArg.get! newCtx = blockArg.get! ctx := by
  grind

grind_pattern BlockArgumentPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, blockArg.get! newCtx

@[simp]
theorem RegionPtr.get!_BlockPtr_setParentWithCheck {region : RegionPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    region.get! newCtx = region.get! ctx := by
  grind

grind_pattern RegionPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, region.get! newCtx

@[simp]
theorem ValuePtr.getFirstUse!_BlockPtr_setParentWithCheck {value : ValuePtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    value.getFirstUse! newCtx = value.getFirstUse! ctx := by
  grind

grind_pattern ValuePtr.getFirstUse!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, value.getFirstUse! newCtx

@[simp] -- No grind because of Unit
theorem ValuePtr.getType!_BlockPtr_setParentWithCheck {value : ValuePtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    value.getType! newCtx = value.getType! ctx := by
  grind

grind_pattern ValuePtr.getType!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, value.getType! newCtx

@[simp]
theorem OpOperandPtrPtr.get!_BlockPtr_setParentWithCheck {opOperandPtr : OpOperandPtrPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    opOperandPtr.get! newCtx = opOperandPtr.get! ctx := by
  grind

grind_pattern OpOperandPtrPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, opOperandPtr.get! newCtx

end setParentWithCheck

section linkBetweenWithParent

/- OperationPtr.linkBetweenWithParent -/
unseal BlockPtr.linkBetweenWithParent
attribute [local grind] BlockPtr.linkBetweenWithParent

@[simp]
theorem IRContext.topLevelOp_BlockPtr_linkBetweenWithParent :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    newCtx.topLevelOp = ctx.topLevelOp := by
  grind

grind_pattern IRContext.topLevelOp_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, newCtx.topLevelOp

@[simp]
theorem BlockPtr.firstUse!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).firstUse = (block.get! ctx).firstUse
    := by
  grind

grind_pattern BlockPtr.firstUse!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).firstUse

theorem BlockPtr.prev!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).prev =
    if block = next then
      some block'
    else if block = block' then
      prev
    else
      (block.get! ctx).prev := by
  grind

grind_pattern BlockPtr.prev!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).prev

@[simp]
theorem BlockPtr.next!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).next =
      if block =  prev then
        some block'
      else if block = block' then
        next
      else
        (block.get! ctx).next := by
  grind

grind_pattern BlockPtr.next!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).next

@[simp]
theorem BlockPtr.parent!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).parent =
      if block = block' then
        some parent
      else
        (block.get! ctx).parent := by
  grind

grind_pattern BlockPtr.parent!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).parent

theorem BlockPtr.firstOp!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).firstOp = (block.get! ctx).firstOp := by
  grind

grind_pattern BlockPtr.firstOp!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).firstOp

theorem BlockPtr.lastOp!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).lastOp = (block.get! ctx).lastOp := by
  grind

grind_pattern BlockPtr.lastOp!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).lastOp

theorem OperationPtr.get!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx) = operation.get! ctx := by
  grind

grind_pattern OperationPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.get! newCtx

@[simp]
theorem OperationPtr.getNumResults!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumResults! newCtx = operation.getNumResults! ctx := by
  grind

grind_pattern OperationPtr.getNumResults!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumResults! newCtx

@[simp]
theorem OpResultPtr.get!_BlockPtr_linkBetweenWithParent {opResult : OpResultPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    opResult.get! newCtx = opResult.get! ctx := by
  unfold BlockPtr.linkBetweenWithParent
  grind

grind_pattern OpResultPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opResult.get! newCtx

@[simp]
theorem OperationPtr.getNumOperands!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  grind

grind_pattern OperationPtr.getNumOperands!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumOperands! newCtx

@[simp]
theorem OpOperandPtr.get!_BlockPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  grind

grind_pattern OpOperandPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.get! newCtx

@[simp]
theorem OperationPtr.getNumSuccessors!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumSuccessors! newCtx = operation.getNumSuccessors! ctx := by
  grind

grind_pattern OperationPtr.getNumSuccessors!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumSuccessors! newCtx

@[simp]
theorem BlockOperandPtr.get!_BlockPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  grind

grind_pattern BlockOperandPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.get! newCtx

@[simp]
theorem OperationPtr.getNumRegions!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumRegions! newCtx = operation.getNumRegions! ctx := by
  grind

grind_pattern OperationPtr.getNumRegions!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumRegions! newCtx

@[simp]
theorem OperationPtr.getRegion!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getRegion! newCtx i = operation.getRegion! ctx i := by
  grind

grind_pattern OperationPtr.getRegion!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getRegion! newCtx i

@[simp]
theorem BlockOperandPtrPtr.get!_BlockPtr_linkBetweenWithParent {operandPtr : BlockOperandPtrPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operandPtr.get! newCtx = operandPtr.get! ctx := by
  grind

grind_pattern BlockOperandPtrPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operandPtr.get! newCtx

@[simp]
theorem BlockPtr.getNumArguments!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    block.getNumArguments! newCtx = block.getNumArguments! ctx := by
  grind

grind_pattern BlockPtr.getNumArguments!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, block.getNumArguments! newCtx

@[simp]
theorem BlockArgumentPtr.get!_BlockPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    blockArg.get! newCtx = blockArg.get! ctx := by
  grind

grind_pattern BlockArgumentPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, blockArg.get! newCtx

@[simp]
theorem RegionPtr.firstBlock!_BlockPtr_linkBetweenWithParent {region : RegionPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (region.get! newCtx).firstBlock =
      if prev = none ∧ region = parent then
        some block'
      else
        (region.get! ctx).firstBlock := by
  grind

grind_pattern RegionPtr.firstBlock!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (region.get! newCtx).firstBlock

@[simp]
theorem RegionPtr.lastBlock!_BlockPtr_linkBetweenWithParent {region : RegionPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (region.get! newCtx).lastBlock =
      if next = none ∧ region = parent then
        some block'
      else
        (region.get! ctx).lastBlock := by
  grind

grind_pattern RegionPtr.lastBlock!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (region.get! newCtx).lastBlock

@[simp]
theorem RegionPtr.parent!_BlockPtr_linkBetweenWithParent {region : RegionPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (region.get! newCtx).parent = (region.get! ctx).parent := by
  grind

grind_pattern RegionPtr.parent!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (region.get! newCtx).parent

@[simp]
theorem ValuePtr.getFirstUse!_BlockPtr_linkBetweenWithParent {value : ValuePtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    value.getFirstUse! newCtx = value.getFirstUse! ctx := by
  grind

grind_pattern ValuePtr.getFirstUse!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, value.getFirstUse! newCtx

theorem ValuePtr.getType!_BlockPtr_linkBetweenWithParent {value : ValuePtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    value.getType! newCtx = value.getType! ctx := by
  grind

grind_pattern ValuePtr.getType!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, value.getType! newCtx

@[simp]
theorem OpOperandPtrPtr.get!_BlockPtr_linkBetweenWithParent {opOperandPtr : OpOperandPtrPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    opOperandPtr.get! newCtx = opOperandPtr.get! ctx := by
  grind

grind_pattern OpOperandPtrPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opOperandPtr.get! newCtx

end linkBetweenWithParent
