module

public import Veir.IR
public import Veir.Rewriter.LinkedList.Basic
import all Veir.Rewriter.LinkedList.Basic

public section

/- Transport lemmas: every getter against every linked-list setter. -/
namespace Veir.Sim

variable {op op' : OperationPtr}
variable {operation operation' : OperationPtr}
variable {block block' : BlockPtr}
variable {rg rg' : RegionPtr}
variable {opOperand opOperand' : OpOperandPtr}
variable {opOperandPtr opOperandPtr' : OpOperandPtrPtr}
variable {blockOperand blockOperand' : BlockOperandPtr}
variable {value value' : ValuePtr}
variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo]
variable {ctx ctx' : IRContext OpInfo}

/- OpOperandPtr.removeFromCurrent -/
attribute [local grind =] Sim.OpOperandPtr.removeFromCurrent_def
attribute [local grind] Sim.OpOperandPtr.removeFromCurrentSim

@[simp, grind =]
theorem BlockPtr.firstUse!_OpOperandPtr_removeFromCurrent {block : Veir.BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec).firstUse =
    (block.get! ctx.spec).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.capArguments!_OpOperandPtr_removeFromCurrent {block : Veir.BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec).capArguments =
    (block.get! ctx.spec).capArguments := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_OpOperandPtr_removeFromCurrent {block : Veir.BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec).prev =
    (block.get! ctx.spec).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_OpOperandPtr_removeFromCurrent {block : Veir.BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec).next =
    (block.get! ctx.spec).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_OpOperandPtr_removeFromCurrent {block : Veir.BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec).parent =
    (block.get! ctx.spec).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_OpOperandPtr_removeFromCurrent {block : Veir.BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec).firstOp =
    (block.get! ctx.spec).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_OpOperandPtr_removeFromCurrent {block : Veir.BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec).lastOp =
    (block.get! ctx.spec).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OpOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec).prev =
    (operation.get! ctx.spec).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OpOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec).next =
    (operation.get! ctx.spec).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OpOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec).parent =
    (operation.get! ctx.spec).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OpOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    operation.getOpType! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec =
    operation.getOpType! ctx.spec := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OpOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec).attrs =
    (operation.get! ctx.spec).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.capResults!_OpOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec).capResults =
    (operation.get! ctx.spec).capResults := by
  grind

@[simp, grind =]
theorem OperationPtr.capBlockOperands!_OpOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec).capBlockOperands =
    (operation.get! ctx.spec).capBlockOperands := by
  grind

@[simp, grind =]
theorem OperationPtr.capRegions!_OpOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec).capRegions =
    (operation.get! ctx.spec).capRegions := by
  grind

@[simp, grind =]
theorem OperationPtr.capOperands!_OpOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec).capOperands =
    (operation.get! ctx.spec).capOperands := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OpOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    operation.getProperties! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec propT =
    operation.getProperties! ctx.spec propT := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    operation.getNumResults! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec =
    operation.getNumResults! ctx.spec := by
  grind

@[grind =]
theorem OpResultPtr.get!_OpOperandPtr_removeFromCurrent {opResult : Veir.OpResultPtr} :
    opResult.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec =
    if (opOperand'.spec.get! ctx.spec).back = .valueFirstUse (.opResult opResult) then
      { opResult.get! ctx.spec with firstUse := (opOperand'.spec.get! ctx.spec).nextUse }
    else
      opResult.get! ctx.spec := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    operation.getNumOperands! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec =
    operation.getNumOperands! ctx.spec := by
  grind

@[grind =]
theorem OpOperandPtr.get!_OpOperandPtr_removeFromCurrent {opOperand : Veir.OpOperandPtr} :
    opOperand.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec =
    { opOperand.get! ctx.spec with
        back :=
          if (opOperand'.spec.get! ctx.spec).nextUse = some opOperand then
            (opOperand'.spec.get! ctx.spec).back
          else
            (opOperand.get! ctx.spec).back
        nextUse :=
          if (opOperand'.spec.get! ctx.spec).back = .operandNextUse opOperand then
            (opOperand'.spec.get! ctx.spec).nextUse
          else
            (opOperand.get! ctx.spec).nextUse
    } := by
  simp [removeFromCurrent_def, removeFromCurrentSim]
  split
  · split
    · grind
    · split
      · grind
      · -- TODO: Why doesn't 'grind' work here?
        simp [Veir.OpOperandPtr.get!_OpOperandPtrPtr_set, ite_eq_right_iff]
        grind [generic_ptr_grind]
  · split
    · grind
    · split
      · grind
      · simp [Veir.OpOperandPtr.get!_OpOperandPtr_setBack]
        split
        · grind
        · simp only [Veir.OpOperandPtr.get!_OpOperandPtrPtr_set, ite_eq_right_iff]
          grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OpOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    operation.getOperands! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec =
    operation.getOperands! ctx.spec := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OpOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    operation.getNumSuccessors! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec =
    operation.getNumSuccessors! ctx.spec := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OpOperandPtr_removeFromCurrent {blockOperand : Veir.BlockOperandPtr} :
    blockOperand.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec =
    blockOperand.get! ctx.spec := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OpOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    operation.getNumRegions! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec =
    operation.getNumRegions! ctx.spec := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OpOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    operation.getRegion! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec i =
    operation.getRegion! ctx.spec i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OpOperandPtr_removeFromCurrent {blockOperandPtr : Veir.BlockOperandPtrPtr} :
    blockOperandPtr.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec =
    blockOperandPtr.get! ctx.spec := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OpOperandPtr_removeFromCurrent {block : Veir.BlockPtr} {hop} :
    block.getNumArguments! (opOperand'.removeFromCurrent ctx newOperands hop).spec =
    block.getNumArguments! ctx.spec := by
  grind

@[grind =]
theorem BlockArgumentPtr.get!_OpOperandPtr_removeFromCurrent {blockArg : Veir.BlockArgumentPtr} :
    blockArg.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec =
    if (opOperand'.spec.get! ctx.spec).back = .valueFirstUse (.blockArgument blockArg) then
      { blockArg.get! ctx.spec with firstUse := (opOperand'.spec.get! ctx.spec).nextUse }
    else
      blockArg.get! ctx.spec := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpOperandPtr_removeFromCurrent {region : Veir.RegionPtr} :
    region.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec =
    region.get! ctx.spec := by
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_OpOperandPtr_removeFromCurrent {value : Veir.ValuePtr} :
    value.getFirstUse! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec =
    if (opOperand'.spec.get! ctx.spec).back = .valueFirstUse value then
      (opOperand'.spec.get! ctx.spec).nextUse
    else
      value.getFirstUse! ctx.spec := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OpOperandPtr_removeFromCurrent {value : Veir.ValuePtr} :
    value.getType! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec =
    value.getType! ctx.spec := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_OpOperandPtr_removeFromCurrent {opOperandPtr : Veir.OpOperandPtrPtr} :
    opOperandPtr.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).spec =
    if opOperandPtr = (opOperand'.spec.get! ctx.spec).back then
      (opOperand'.spec.get! ctx.spec).nextUse
    else
      opOperandPtr.get! ctx.spec := by
  grind

/- OpOperandPtr.insertIntoCurrent -/
attribute [local grind =] Sim.OpOperandPtr.insertIntoCurrent!

@[simp, grind =]
theorem BlockPtr.firstUse!_OpOperandPtr_insertIntoCurrent {block : Veir.BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec).firstUse =
    (block.get! ctx.spec).firstUse := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem BlockPtr.capArguments!_OpOperandPtr_insertIntoCurrent {block : Veir.BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec).capArguments =
    (block.get! ctx.spec).capArguments := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem BlockPtr.prev!_OpOperandPtr_insertIntoCurrent {block : Veir.BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec).prev =
    (block.get! ctx.spec).prev := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem BlockPtr.next!_OpOperandPtr_insertIntoCurrent {block : Veir.BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec).next =
    (block.get! ctx.spec).next := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem BlockPtr.parent!_OpOperandPtr_insertIntoCurrent {block : Veir.BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec).parent =
    (block.get! ctx.spec).parent := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_OpOperandPtr_insertIntoCurrent {block : Veir.BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec).firstOp =
    (block.get! ctx.spec).firstOp := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_OpOperandPtr_insertIntoCurrent {block : Veir.BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec).lastOp =
    (block.get! ctx.spec).lastOp := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OpOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec).prev =
    (operation.get! ctx.spec).prev := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem OperationPtr.next!_OpOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec).next =
    (operation.get! ctx.spec).next := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OpOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec).parent =
    (operation.get! ctx.spec).parent := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OpOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    operation.getOpType! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec =
    operation.getOpType! ctx.spec := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OpOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec).attrs =
    (operation.get! ctx.spec).attrs := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem OperationPtr.capResults!_OpOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec).capResults =
    (operation.get! ctx.spec).capResults := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem OperationPtr.capBlockOperands!_OpOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec).capBlockOperands =
    (operation.get! ctx.spec).capBlockOperands := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem OperationPtr.capRegions!_OpOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec).capRegions =
    (operation.get! ctx.spec).capRegions := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem OperationPtr.capOperands!_OpOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec).capOperands =
    (operation.get! ctx.spec).capOperands := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OpOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    operation.getProperties! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec =
    operation.getProperties! ctx.spec := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    operation.getNumResults! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec =
    operation.getNumResults! ctx.spec := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[grind =]
theorem OpResultPtr.get!_OpOperandPtr_insertIntoCurrent {opResult : Veir.OpResultPtr} :
    opResult.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec =
    if (opOperand'.spec.get! ctx.spec).value = .opResult opResult then
      { opResult.get! ctx.spec with firstUse := some opOperand'.spec }
    else
      opResult.get! ctx.spec := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    operation.getNumOperands! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec =
    operation.getNumOperands! ctx.spec := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[grind =]
theorem OpOperandPtr.get!_OpOperandPtr_insertIntoCurrent {opOperand : Veir.OpOperandPtr} :
    opOperand.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec =
    { opOperand.get! ctx.spec with
        back :=
          if (opOperand'.spec.get! ctx.spec).value.getFirstUse! ctx.spec = some opOperand then
            .operandNextUse opOperand'.spec
          else if opOperand'.spec = opOperand then
            .valueFirstUse ((opOperand'.spec.get! ctx.spec).value)
          else
            (opOperand.get! ctx.spec).back
        nextUse :=
          if opOperand'.spec = opOperand then
            (opOperand'.spec.get! ctx.spec).value.getFirstUse! ctx.spec
          else
            (opOperand.get! ctx.spec).nextUse
    } := by
  simp only [insertIntoCurrent_def, insertIntoCurrentSim]
  by_cases h: opOperand = opOperand'.spec
  · grind [Sim.ValuePtr.getOpOperandPtrPtr, Sim.OpOperandPtr.getOpOperandPtrPtr]
  · split
    · simp only [ValuePtr.setFirstUse_spec, getValue_spec, setNextUse_spec, setBack_spec,
      ValuePtr.getFirstUse_spec, OpOperandPtr.get!_ValuePtr_setFirstUse,
      OpOperandPtr.get!_OpOperandPtr_setNextUse]
      split
      · grind
      · simp only [OpOperandPtr.get!_OpOperandPtr_setBack]
        split
        · grind
        · split
          · grind
          · split <;> grind
    · simp only [setBack_spec, ValuePtr.setFirstUse_spec, getValue_spec, setNextUse_spec,
      ValuePtr.getFirstUse_spec]
      simp only [OpOperandPtr.get!_OpOperandPtr_setBack, OpOperandPtr.get!_ValuePtr_setFirstUse]
      split
      · grind [Sim.ValuePtr.getOpOperandPtrPtr, Sim.OpOperandPtr.getOpOperandPtrPtr]
      · simp only [OpOperandPtr.get!_OpOperandPtr_setNextUse]
        split
        · grind
        · simp only [OpOperandPtr.get!_OpOperandPtr_setBack]
          split
          · grind
          · split
            · grind
            · split <;> grind


@[simp, grind =]
theorem OperationPtr.getOperands!_OpOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    operation.getOperands! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec =
    operation.getOperands! ctx.spec := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OpOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    operation.getNumSuccessors! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec =
    operation.getNumSuccessors! ctx.spec := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OpOperandPtr_insertIntoCurrent {blockOperand : Veir.BlockOperandPtr} :
    blockOperand.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec =
    blockOperand.get! ctx.spec := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OpOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    operation.getNumRegions! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec =
    operation.getNumRegions! ctx.spec := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OpOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    operation.getRegion! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec i =
    operation.getRegion! ctx.spec i := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OpOperandPtr_insertIntoCurrent {blockOperandPtr : Veir.BlockOperandPtrPtr} :
    blockOperandPtr.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec =
    blockOperandPtr.get! ctx.spec := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OpOperandPtr_insertIntoCurrent {block : Veir.BlockPtr} {hop} :
    block.getNumArguments! (opOperand'.insertIntoCurrent ctx newOperands hop).spec =
    block.getNumArguments! ctx.spec := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[grind =]
theorem BlockArgumentPtr.get!_OpOperandPtr_insertIntoCurrent {blockArg : Veir.BlockArgumentPtr} :
    blockArg.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec =
    if (opOperand'.spec.get! ctx.spec).value = (.blockArgument blockArg) then
      { blockArg.get! ctx.spec with firstUse := some opOperand'.spec }
    else
      blockArg.get! ctx.spec := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpOperandPtr_insertIntoCurrent {region : Veir.RegionPtr} :
    region.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec =
    region.get! ctx.spec := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_OpOperandPtr_insertIntoCurrent {value : Veir.ValuePtr} :
    value.getFirstUse! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec =
    if (opOperand'.spec.get! ctx.spec).value = value then
      some opOperand'.spec
    else
      value.getFirstUse! ctx.spec := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OpOperandPtr_insertIntoCurrent {value : Veir.ValuePtr} :
    value.getType! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec =
    value.getType! ctx.spec := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_OpOperandPtr_insertIntoCurrent {opOperandPtr : Veir.OpOperandPtrPtr} :
    opOperandPtr.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).spec =
    if opOperandPtr = .operandNextUse opOperand'.spec then
      (opOperand'.spec.get! ctx.spec).value.getFirstUse! ctx.spec
    else if opOperandPtr = .valueFirstUse ((opOperand'.spec.get! ctx.spec).value) then
      some opOperand'.spec
    else
      opOperandPtr.get! ctx.spec := by
  simp [OpOperandPtr.insertIntoCurrent_def, OpOperandPtr.insertIntoCurrentSim]
  grind

section BlockOperandPtr.removeFromCurrent

attribute [local grind =] Sim.BlockOperandPtr.removeFromCurrent_def
attribute [local grind] Sim.BlockOperandPtr.removeFromCurrentSim

@[grind =]
theorem BlockPtr.firstUse!_BlockOperandPtr_removeFromCurrent {block : Veir.BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec).firstUse =
    if (blockOperand'.spec.get! ctx.spec).back = .blockFirstUse block then
      (blockOperand'.spec.get! ctx.spec).nextUse
    else
      (block.get! ctx.spec).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.capArguments!_BlockOperandPtr_removeFromCurrent {block : Veir.BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec).capArguments =
    (block.get! ctx.spec).capArguments := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_BlockOperandPtr_removeFromCurrent {block : Veir.BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec).prev =
    (block.get! ctx.spec).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_BlockOperandPtr_removeFromCurrent {block : Veir.BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec).next =
    (block.get! ctx.spec).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_BlockOperandPtr_removeFromCurrent {block : Veir.BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec).parent =
    (block.get! ctx.spec).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockOperandPtr_removeFromCurrent {block : Veir.BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec).firstOp =
    (block.get! ctx.spec).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockOperandPtr_removeFromCurrent {block : Veir.BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec).lastOp =
    (block.get! ctx.spec).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_BlockOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    (operation.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec).prev =
    (operation.get! ctx.spec).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_BlockOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    (operation.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec).next =
    (operation.get! ctx.spec).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_BlockOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    (operation.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec).parent =
    (operation.get! ctx.spec).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    operation.getOpType! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec =
    operation.getOpType! ctx.spec := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_BlockOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    (operation.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec).attrs =
    (operation.get! ctx.spec).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.capResults!_BlockOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    (operation.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec).capResults =
    (operation.get! ctx.spec).capResults := by
  grind

@[simp, grind =]
theorem OperationPtr.capBlockOperands!_BlockOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    (operation.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec).capBlockOperands =
    (operation.get! ctx.spec).capBlockOperands := by
  grind

@[simp, grind =]
theorem OperationPtr.capRegions!_BlockOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    (operation.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec).capRegions =
    (operation.get! ctx.spec).capRegions := by
  grind

@[simp, grind =]
theorem OperationPtr.capOperands!_BlockOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    (operation.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec).capOperands =
    (operation.get! ctx.spec).capOperands := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    operation.getProperties! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec opCode =
    operation.getProperties! ctx.spec opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    operation.getNumResults! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec =
    operation.getNumResults! ctx.spec := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockOperandPtr_removeFromCurrent {opResult : Veir.OpResultPtr} :
    opResult.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec =
    opResult.get! ctx.spec := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    operation.getNumOperands! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec =
    operation.getNumOperands! ctx.spec := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockOperandPtr_removeFromCurrent {opOperand : Veir.OpOperandPtr} :
    opOperand.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec =
    opOperand.get! ctx.spec := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    operation.getOperands! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec =
    operation.getOperands! ctx.spec := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    operation.getNumSuccessors! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec =
    operation.getNumSuccessors! ctx.spec := by
  grind

@[grind =]
theorem BlockOperandPtr.get!_BlockOperandPtr_removeFromCurrent {blockOperand : Veir.BlockOperandPtr} :
    blockOperand.get! (blockOperand'.removeFromCurrent ctx hblockOperand' ctxInBounds).spec =
    { blockOperand.get! ctx.spec with
        back :=
          if (blockOperand'.spec.get! ctx.spec).nextUse = some blockOperand then
            (blockOperand'.spec.get! ctx.spec).back
          else
            (blockOperand.get! ctx.spec).back
        nextUse :=
          if (blockOperand'.spec.get! ctx.spec).back = .blockOperandNextUse blockOperand then
            (blockOperand'.spec.get! ctx.spec).nextUse
          else
            (blockOperand.get! ctx.spec).nextUse
    } := by
  simp [removeFromCurrent_def, removeFromCurrentSim]
  split
  · split
    · grind
    · split
      · grind
      · simp [Veir.BlockOperandPtr.get!_BlockOperandPtrPtr_set, ite_eq_right_iff]
        grind [generic_ptr_grind]
  · split
    · grind
    · split
      · grind
      · simp [Veir.BlockOperandPtr.get!_BlockOperandPtr_setBack]
        split
        · grind
        · simp only [Veir.BlockOperandPtr.get!_BlockOperandPtrPtr_set, ite_eq_right_iff]
          grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    operation.getNumRegions! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec =
    operation.getNumRegions! ctx.spec := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockOperandPtr_removeFromCurrent {operation : Veir.OperationPtr} :
    operation.getRegion! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec i =
    operation.getRegion! ctx.spec i := by
  grind

@[grind =]
theorem BlockOperandPtrPtr.get!_BlockOperandPtr_removeFromCurrent {blockOperandPtr : Veir.BlockOperandPtrPtr} :
    blockOperandPtr.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec =
    if blockOperandPtr = (blockOperand'.spec.get! ctx.spec).back then
      (blockOperand'.spec.get! ctx.spec).nextUse
    else
      blockOperandPtr.get! ctx.spec := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockOperandPtr_removeFromCurrent {block : Veir.BlockPtr} {hop} :
    block.getNumArguments! (blockOperand'.removeFromCurrent ctx newOperands hop).spec =
    block.getNumArguments! ctx.spec := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockOperandPtr_removeFromCurrent {blockArg : Veir.BlockArgumentPtr} :
    blockArg.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec =
    blockArg.get! ctx.spec := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockOperandPtr_removeFromCurrent {region : Veir.RegionPtr} :
    region.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec =
    region.get! ctx.spec := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockOperandPtr_removeFromCurrent {value : Veir.ValuePtr} :
    value.getFirstUse! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec =
    value.getFirstUse! ctx.spec := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockOperandPtr_removeFromCurrent {value : Veir.ValuePtr} :
    value.getType! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec =
    value.getType! ctx.spec := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockOperandPtr_removeFromCurrent {opOperandPtr : Veir.OpOperandPtrPtr} :
    opOperandPtr.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds).spec =
    opOperandPtr.get! ctx.spec := by
  grind

end BlockOperandPtr.removeFromCurrent

section BlockOperandPtr.insertIntoCurrent

attribute [local grind =] Sim.BlockOperandPtr.insertIntoCurrent_def
attribute [local grind] Sim.BlockOperandPtr.insertIntoCurrentSim

@[grind =]
theorem BlockPtr.firstUse!_BlockOperandPtr_insertIntoCurrent {block : Veir.BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec).firstUse =
    if (blockOperand'.spec.get! ctx.spec).value = block then
      some blockOperand'.spec
    else
      (block.get! ctx.spec).firstUse := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockPtr.capArguments!_BlockOperandPtr_insertIntoCurrent {block : Veir.BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec).capArguments =
    (block.get! ctx.spec).capArguments := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockPtr.prev!_BlockOperandPtr_insertIntoCurrent {block : Veir.BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec).prev =
    (block.get! ctx.spec).prev := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockPtr.next!_BlockOperandPtr_insertIntoCurrent {block : Veir.BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec).next =
    (block.get! ctx.spec).next := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockPtr.parent!_BlockOperandPtr_insertIntoCurrent {block : Veir.BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec).parent =
    (block.get! ctx.spec).parent := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockOperandPtr_insertIntoCurrent {block : Veir.BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec).firstOp =
    (block.get! ctx.spec).firstOp := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockOperandPtr_insertIntoCurrent {block : Veir.BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec).lastOp =
    (block.get! ctx.spec).lastOp := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.prev!_BlockOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    (operation.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec).prev =
    (operation.get! ctx.spec).prev := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.next!_BlockOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    (operation.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec).next =
    (operation.get! ctx.spec).next := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.parent!_BlockOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    (operation.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec).parent =
    (operation.get! ctx.spec).parent := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    operation.getOpType! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec =
    operation.getOpType! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.attrs!_BlockOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    (operation.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec).attrs =
    (operation.get! ctx.spec).attrs := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.capResults!_BlockOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    (operation.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec).capResults =
    (operation.get! ctx.spec).capResults := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.capBlockOperands!_BlockOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    (operation.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec).capBlockOperands =
    (operation.get! ctx.spec).capBlockOperands := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.capRegions!_BlockOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    (operation.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec).capRegions =
    (operation.get! ctx.spec).capRegions := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.capOperands!_BlockOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    (operation.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec).capOperands =
    (operation.get! ctx.spec).capOperands := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    operation.getProperties! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec opCode =
    operation.getProperties! ctx.spec opCode := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    operation.getNumResults! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec =
    operation.getNumResults! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OpResultPtr.get!_BlockOperandPtr_insertIntoCurrent {opResult : Veir.OpResultPtr} :
    opResult.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec =
    opResult.get! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    operation.getNumOperands! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec =
    operation.getNumOperands! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OpOperandPtr.get!_BlockOperandPtr_insertIntoCurrent {opOperand : Veir.OpOperandPtr} :
    opOperand.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec =
    opOperand.get! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    operation.getOperands! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec =
    operation.getOperands! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    operation.getNumSuccessors! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec =
    operation.getNumSuccessors! ctx.spec := by
  grind (gen := 20)

@[grind =]
theorem BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent {blockOperand : Veir.BlockOperandPtr} :
    blockOperand.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec =
    { blockOperand.get! ctx.spec with
        back :=
          if ((blockOperand'.spec.get! ctx.spec).value.get! ctx.spec).firstUse = some blockOperand then
            .blockOperandNextUse blockOperand'.spec
          else if blockOperand'.spec = blockOperand then
            .blockFirstUse ((blockOperand'.spec.get! ctx.spec).value)
          else
            (blockOperand.get! ctx.spec).back
        nextUse :=
          if blockOperand'.spec = blockOperand then
            ((blockOperand'.spec.get! ctx.spec).value.get! ctx.spec).firstUse
          else
            (blockOperand.get! ctx.spec).nextUse
    } := by
  simp [insertIntoCurrent_def, insertIntoCurrentSim]
  split <;> simp
  · simp [Veir.BlockOperandPtr.get!_BlockOperandPtr_setNextUse]
    split
    · grind [BlockPtr.getBlockOperandPtrPtr]
    · simp [Veir.BlockOperandPtr.get!_BlockOperandPtr_setBack]
      split
      · grind
      · split
        · grind
        · split <;> grind
  · simp [Veir.BlockOperandPtr.get!_BlockOperandPtr_setBack]
    split
    · grind [BlockPtr.getBlockOperandPtrPtr, getBlockOperandPtrPtr]
    · simp [Veir.BlockOperandPtr.get!_BlockOperandPtr_setNextUse]
      split
      · grind [BlockPtr.getBlockOperandPtrPtr]
      · simp [Veir.BlockOperandPtr.get!_BlockOperandPtr_setBack]
        split
        · grind
        · split
          · grind [BlockPtr.getBlockOperandPtrPtr, getBlockOperandPtrPtr]
          · split <;> grind [BlockPtr.getBlockOperandPtrPtr, getBlockOperandPtrPtr]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    operation.getNumRegions! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec =
    operation.getNumRegions! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockOperandPtr_insertIntoCurrent {operation : Veir.OperationPtr} :
    operation.getRegion! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec i =
    operation.getRegion! ctx.spec i := by
  grind (gen := 20)

@[grind =]
theorem BlockOperandPtrPtr.get!_BlockOperandPtr_insertIntoCurrent {blockOperandPtr : Veir.BlockOperandPtrPtr} :
    blockOperandPtr.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec =
    if blockOperandPtr = .blockOperandNextUse blockOperand'.spec then
      ((blockOperand'.spec.get! ctx.spec).value.get! ctx.spec).firstUse
    else if blockOperandPtr = .blockFirstUse ((blockOperand'.spec.get! ctx.spec).value) then
      some blockOperand'.spec
    else
      blockOperandPtr.get! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockOperandPtr_insertIntoCurrent {block : Veir.BlockPtr} {hop} :
    block.getNumArguments! (blockOperand'.insertIntoCurrent ctx newOperands hop).spec =
    block.getNumArguments! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockOperandPtr_insertIntoCurrent {blockArg : Veir.BlockArgumentPtr} :
    blockArg.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec =
    blockArg.get! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem RegionPtr.get!_BlockOperandPtr_insertIntoCurrent {region : Veir.RegionPtr} :
    region.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec =
    region.get! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockOperandPtr_insertIntoCurrent {value : Veir.ValuePtr} :
    value.getFirstUse! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec =
    value.getFirstUse! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem ValuePtr.getType!_BlockOperandPtr_insertIntoCurrent {value : Veir.ValuePtr} :
    value.getType! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec =
    value.getType! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockOperandPtr_insertIntoCurrent {opOperandPtr : Veir.OpOperandPtrPtr} :
    opOperandPtr.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds).spec =
    opOperandPtr.get! ctx.spec := by
  grind (gen := 20)

end BlockOperandPtr.insertIntoCurrent

/- OperationPtr.linkBetween -/
section linkBetween
attribute [local grind =] Sim.OperationPtr.linkBetween_def
attribute [local grind] Sim.OperationPtr.linkBetweenSim

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_linkBetween {block : Veir.BlockPtr} :
    block.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    block.get! ctx.spec := by
  grind (gen := 20)

@[grind =]
theorem OperationPtr.prev!_OperationPtr_linkBetween {operation : Veir.OperationPtr} :
    (operation.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec).prev =
    if operation = next.spec then
      some op'.spec
    else if operation = op'.spec then
      prev.spec
    else
      (operation.get! ctx.spec).prev := by
  grind (gen := 20)

set_option maxHeartbeats 1000000 in
@[grind =]
theorem OperationPtr.next!_OperationPtr_linkBetween {operation : Veir.OperationPtr} :
    (operation.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec).next =
    if operation = prev.spec then
      some op'.spec
    else if operation = op'.spec then
      next.spec
    else
      (operation.get! ctx.spec).next := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.parent!_OperationPtr_linkBetween {operation : Veir.OperationPtr} :
    (operation.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec).parent =
    (operation.get! ctx.spec).parent := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_linkBetween {operation : Veir.OperationPtr} :
    operation.getOpType! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    operation.getOpType! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.attrs!_OperationPtr_linkBetween {operation : Veir.OperationPtr} :
    (operation.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec).attrs =
    (operation.get! ctx.spec).attrs := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.capResults!_OperationPtr_linkBetween {operation : Veir.OperationPtr} :
    (operation.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec).capResults =
    (operation.get! ctx.spec).capResults := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.capBlockOperands!_OperationPtr_linkBetween {operation : Veir.OperationPtr} :
    (operation.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec).capBlockOperands =
    (operation.get! ctx.spec).capBlockOperands := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.capRegions!_OperationPtr_linkBetween {operation : Veir.OperationPtr} :
    (operation.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec).capRegions =
    (operation.get! ctx.spec).capRegions := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.capOperands!_OperationPtr_linkBetween {operation : Veir.OperationPtr} :
    (operation.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec).capOperands =
    (operation.get! ctx.spec).capOperands := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getProperties!_OperationPtr_linkBetween {operation : Veir.OperationPtr} :
    operation.getProperties! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec opCode =
    operation.getProperties! ctx.spec opCode := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_linkBetween {operation : Veir.OperationPtr} :
    operation.getNumResults! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    operation.getNumResults! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OpResultPtr.get!_OperationPtr_linkBetween {opResult : Veir.OpResultPtr} :
    opResult.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    opResult.get! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_linkBetween {operation : Veir.OperationPtr} :
    operation.getNumOperands! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    operation.getNumOperands! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OpOperandPtr.get!_OperationPtr_linkBetween {opOperand : Veir.OpOperandPtr} :
    opOperand.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    opOperand.get! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getOperands!_OperationPtr_linkBetween {operation : Veir.OperationPtr} :
    operation.getOperands! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    operation.getOperands! ctx.spec := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_linkBetween {operation : Veir.OperationPtr} :
    operation.getNumSuccessors! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    operation.getNumSuccessors! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockOperandPtr.get!_OperationPtr_linkBetween {blockOperand : Veir.BlockOperandPtr} :
    blockOperand.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    blockOperand.get! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OperationPtr_linkBetween {operation : Veir.OperationPtr} :
    operation.getNumRegions! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    operation.getNumRegions! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getRegion!_OperationPtr_linkBetween {operation : Veir.OperationPtr} :
    operation.getRegion! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec i =
    operation.getRegion! ctx.spec i := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_linkBetween {blockOperandPtr : Veir.BlockOperandPtrPtr} :
    blockOperandPtr.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    blockOperandPtr.get! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_linkBetween {block : Veir.BlockPtr} :
    block.getNumArguments! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    block.getNumArguments! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockArgumentPtr.get!_OperationPtr_linkBetween {blockArg : Veir.BlockArgumentPtr} :
    blockArg.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    blockArg.get! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_linkBetween {region : Veir.RegionPtr} :
    region.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    region.get! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_linkBetween {value : Veir.ValuePtr} :
    value.getFirstUse! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    value.getFirstUse! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem ValuePtr.getType!_OperationPtr_linkBetween {value : Veir.ValuePtr} :
    value.getType! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    value.getType! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_linkBetween {opOperandPtr : Veir.OpOperandPtrPtr} :
    opOperandPtr.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    opOperandPtr.get! ctx.spec := by
  grind (gen := 20)

end linkBetween

section setParentWithCheck

/- OperationPtr.setParentWithCheck -/
attribute [local grind =] Sim.OperationPtr.setParentWithCheck_def
attribute [local grind] Sim.OperationPtr.setParentWithCheckSim

@[simp]
theorem BlockPtr.get!_OperationPtr_setParentWithCheck {block : Veir.BlockPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    block.get! newCtx.spec = block.get! ctx.spec := by
  grind

grind_pattern BlockPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, block.get! newCtx.spec

@[simp]
theorem OperationPtr.prev!_OperationPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    (operation.get! newCtx.spec).prev = (operation.get! ctx.spec).prev := by
  grind

grind_pattern OperationPtr.prev!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.get! newCtx.spec).prev

@[simp]
theorem OperationPtr.next!_OperationPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    (operation.get! newCtx.spec).next = (operation.get! ctx.spec).next := by
  grind

grind_pattern OperationPtr.next!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.get! newCtx.spec).next

@[grind →]
theorem OperationPtr.parent!_of_OperationPtr_setParentWithCheck_eq :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    (op'.spec.get! ctx.spec).parent = none := by
  simp [setParentWithCheck_def, setParentWithCheckSim]
  have : (getParent ctx op' (by grind)).InBounds ctx := by grind [generic_ptr_grind]
  grind

theorem OperationPtr.parent!_OperationPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    (operation.get! newCtx.spec).parent =
    if operation = op'.spec then
      some newParent.spec
    else
      (operation.get! ctx.spec).parent := by
  grind

grind_pattern OperationPtr.parent!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.get! newCtx.spec).parent

@[simp]
theorem OperationPtr.getOpType!_OperationPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operation.getOpType! newCtx.spec = operation.getOpType! ctx.spec := by
  grind

grind_pattern OperationPtr.getOpType!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.getOpType! newCtx.spec)

@[simp]
theorem OperationPtr.attrs!_OperationPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    (operation.get! newCtx.spec).attrs = (operation.get! ctx.spec).attrs := by
  grind

grind_pattern OperationPtr.attrs!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.get! newCtx.spec).attrs

@[simp]
theorem OperationPtr.capResults!_OperationPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    (operation.get! newCtx.spec).capResults = (operation.get! ctx.spec).capResults := by
  grind

grind_pattern OperationPtr.capResults!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.get! newCtx.spec).capResults

@[simp]
theorem OperationPtr.capBlockOperands!_OperationPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    (operation.get! newCtx.spec).capBlockOperands = (operation.get! ctx.spec).capBlockOperands := by
  grind

grind_pattern OperationPtr.capBlockOperands!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.get! newCtx.spec).capBlockOperands

@[simp]
theorem OperationPtr.capRegions!_OperationPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    (operation.get! newCtx.spec).capRegions = (operation.get! ctx.spec).capRegions := by
  grind

grind_pattern OperationPtr.capRegions!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.get! newCtx.spec).capRegions

@[simp]
theorem OperationPtr.capOperands!_OperationPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    (operation.get! newCtx.spec).capOperands = (operation.get! ctx.spec).capOperands := by
  grind

grind_pattern OperationPtr.capOperands!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.get! newCtx.spec).capOperands

@[simp]
theorem OperationPtr.getProperties!_OperationPtr_setParentWithCheck {operation : Veir.OperationPtr}
    (heq : op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx) :
    operation.getProperties! newCtx.spec opCode =
    operation.getProperties! ctx.spec opCode := by
  grind

grind_pattern OperationPtr.getProperties!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getProperties! newCtx.spec opCode

@[simp]
theorem OperationPtr.getNumResults!_OperationPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operation.getNumResults! newCtx.spec = operation.getNumResults! ctx.spec := by
  grind

grind_pattern OperationPtr.getNumResults!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumResults! newCtx.spec

@[simp]
theorem OpResultPtr.get!_OperationPtr_setParentWithCheck {opResult : Veir.OpResultPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    opResult.get! newCtx.spec = opResult.get! ctx.spec := by
  grind

grind_pattern OpResultPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, opResult.get! newCtx.spec

@[simp]
theorem OperationPtr.getNumOperands!_OperationPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operation.getNumOperands! newCtx.spec = operation.getNumOperands! ctx.spec := by
  grind

grind_pattern OperationPtr.getNumOperands!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumOperands! newCtx.spec

@[simp]
theorem OpOperandPtr.get!_OperationPtr_setParentWithCheck {operand : Veir.OpOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operand.get! newCtx.spec = operand.get! ctx.spec := by
  grind

grind_pattern OpOperandPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.get! newCtx.spec

@[simp]
theorem OperationPtr.getOperands!_OperationPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operation.getOperands! newCtx.spec = operation.getOperands! ctx.spec := by
  grind

grind_pattern OperationPtr.getOperands!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getOperands! newCtx.spec

@[simp]
theorem OperationPtr.getNumSuccessors!_OperationPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operation.getNumSuccessors! newCtx.spec = operation.getNumSuccessors! ctx.spec := by
  grind

grind_pattern OperationPtr.getNumSuccessors!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumSuccessors! newCtx.spec

@[simp]
theorem BlockOperandPtr.get!_OperationPtr_setParentWithCheck {operand : Veir.BlockOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operand.get! newCtx.spec = operand.get! ctx.spec := by
  grind

grind_pattern BlockOperandPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.get! newCtx.spec

@[simp]
theorem OperationPtr.getNumRegions!_OperationPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operation.getNumRegions! newCtx.spec = operation.getNumRegions! ctx.spec := by
  grind

grind_pattern OperationPtr.getNumRegions!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumRegions! newCtx.spec

@[simp]
theorem OperationPtr.getRegion!_OperationPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operation.getRegion! newCtx.spec i = operation.getRegion! ctx.spec i := by
  grind

grind_pattern OperationPtr.getRegion!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getRegion! newCtx.spec i

@[simp]
theorem BlockOperandPtrPtr.get!_OperationPtr_setParentWithCheck {operandPtr : Veir.BlockOperandPtrPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operandPtr.get! newCtx.spec = operandPtr.get! ctx.spec := by
  grind

grind_pattern BlockOperandPtrPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operandPtr.get! newCtx.spec

@[simp]
theorem BlockPtr.getNumArguments!_OperationPtr_setParentWithCheck {block : Veir.BlockPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    block.getNumArguments! newCtx.spec = block.getNumArguments! ctx.spec := by
  grind

grind_pattern BlockPtr.getNumArguments!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, block.getNumArguments! newCtx.spec

@[simp]
theorem BlockArgumentPtr.get!_OperationPtr_setParentWithCheck {blockArg : Veir.BlockArgumentPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    blockArg.get! newCtx.spec = blockArg.get! ctx.spec := by
  grind

grind_pattern BlockArgumentPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, blockArg.get! newCtx.spec

@[simp]
theorem RegionPtr.get!_OperationPtr_setParentWithCheck {region : Veir.RegionPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    region.get! newCtx.spec = region.get! ctx.spec := by
  grind

grind_pattern RegionPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, region.get! newCtx.spec

@[simp]
theorem ValuePtr.getFirstUse!_OperationPtr_setParentWithCheck {value : Veir.ValuePtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    value.getFirstUse! newCtx.spec = value.getFirstUse! ctx.spec := by
  grind

grind_pattern ValuePtr.getFirstUse!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, value.getFirstUse! newCtx.spec

@[simp] -- No grind because of Unit
theorem ValuePtr.getType!_OperationPtr_setParentWithCheck {value : Veir.ValuePtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    value.getType! newCtx.spec = value.getType! ctx.spec := by
  grind

grind_pattern ValuePtr.getType!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, value.getType! newCtx.spec

@[simp]
theorem OpOperandPtrPtr.get!_OperationPtr_setParentWithCheck {opOperandPtr : Veir.OpOperandPtrPtr} :
    op'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    opOperandPtr.get! newCtx.spec = opOperandPtr.get! ctx.spec := by
  grind

grind_pattern OpOperandPtrPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, opOperandPtr.get! newCtx.spec

end setParentWithCheck

section linkBetweenWithParent

/- OperationPtr.linkBetweenWithParent -/
attribute [local grind =] Sim.OperationPtr.linkBetweenWithParent_def
attribute [local grind] Sim.OperationPtr.linkBetweenWithParentSim

@[simp]
theorem BlockPtr.firstUse!_OperationPtr_linkBetweenWithParent {block : Veir.BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx.spec).firstUse = (block.get! ctx.spec).firstUse := by
  grind (gen := 20)

grind_pattern BlockPtr.firstUse!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx.spec).firstUse

@[simp]
theorem BlockPtr.capArguments!_OperationPtr_linkBetweenWithParent {block : Veir.BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx.spec).capArguments = (block.get! ctx.spec).capArguments := by
  grind (gen := 20)

grind_pattern BlockPtr.capArguments!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx.spec).capArguments

@[simp]
theorem BlockPtr.prev!_OperationPtr_linkBetweenWithParent {block : Veir.BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx.spec).prev = (block.get! ctx.spec).prev := by
  grind (gen := 20)

grind_pattern BlockPtr.prev!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx.spec).prev

@[simp]
theorem BlockPtr.next!_OperationPtr_linkBetweenWithParent {block : Veir.BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx.spec).next = (block.get! ctx.spec).next := by
  grind (gen := 20)

grind_pattern BlockPtr.next!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx.spec).next

@[grind →]
theorem OperationPtr.parent!_of_OperationPtr_linkBetweenWithParent_eq :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (op'.spec.get! ctx.spec).parent = none := by
  grind

@[simp]
theorem BlockPtr.parent!_OperationPtr_linkBetweenWithParent {block : Veir.BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx.spec).parent = (block.get! ctx.spec).parent := by
  grind (gen := 20)

grind_pattern BlockPtr.parent!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx.spec).parent

theorem BlockPtr.firstOp!_OperationPtr_linkBetweenWithParent {block : Veir.BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx.spec).firstOp =
    if parent.spec = block ∧ prev.spec = none then
      some op'.spec
    else
      (block.get! ctx.spec).firstOp := by
  grind (gen := 20)

grind_pattern BlockPtr.firstOp!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx.spec).firstOp

theorem BlockPtr.lastOp!_OperationPtr_linkBetweenWithParent {block : Veir.BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx.spec).lastOp =
    if parent.spec = block ∧ next.spec = none then
      some op'.spec
    else
      (block.get! ctx.spec).lastOp := by
  grind (gen := 20)

grind_pattern BlockPtr.lastOp!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx.spec).lastOp

theorem OperationPtr.prev!_OperationPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx.spec).prev =
    if operation = next.spec then
      some op'.spec
    else if operation = op'.spec then
      prev.spec
    else
      (operation.get! ctx.spec).prev := by
  grind (gen := 20)

grind_pattern OperationPtr.prev!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.get! newCtx.spec).prev

theorem OperationPtr.next!_OperationPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx.spec).next =
    if operation = prev.spec then
      some op'.spec
    else if operation = op'.spec then
      next.spec
    else
      (operation.get! ctx.spec).next := by
  grind (gen := 20)

grind_pattern OperationPtr.next!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.get! newCtx.spec).next

theorem OperationPtr.parent!_OperationPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx.spec).parent =
    if operation = op'.spec then
      some parent.spec
    else
      (operation.get! ctx.spec).parent := by
  grind (gen := 20)

grind_pattern OperationPtr.parent!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.get! newCtx.spec).parent

@[simp]
theorem OperationPtr.getOpType!_OperationPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getOpType! newCtx.spec = operation.getOpType! ctx.spec := by
  grind (gen := 20)

grind_pattern OperationPtr.getOpType!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.getOpType! newCtx.spec)

@[simp]
theorem OperationPtr.attrs!_OperationPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx.spec).attrs = (operation.get! ctx.spec).attrs := by
  grind (gen := 20)

grind_pattern OperationPtr.attrs!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.get! newCtx.spec).attrs

@[simp]
theorem OperationPtr.capResults!_OperationPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx.spec).capResults = (operation.get! ctx.spec).capResults := by
  grind (gen := 20)

grind_pattern OperationPtr.capResults!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.get! newCtx.spec).capResults

@[simp]
theorem OperationPtr.capBlockOperands!_OperationPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx.spec).capBlockOperands = (operation.get! ctx.spec).capBlockOperands := by
  grind (gen := 20)

grind_pattern OperationPtr.capBlockOperands!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.get! newCtx.spec).capBlockOperands

@[simp]
theorem OperationPtr.capRegions!_OperationPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx.spec).capRegions = (operation.get! ctx.spec).capRegions := by
  grind (gen := 20)

grind_pattern OperationPtr.capRegions!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.get! newCtx.spec).capRegions

@[simp]
theorem OperationPtr.capOperands!_OperationPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx.spec).capOperands = (operation.get! ctx.spec).capOperands := by
  grind (gen := 20)

grind_pattern OperationPtr.capOperands!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.get! newCtx.spec).capOperands

@[simp]
theorem OperationPtr.getProperties!_OperationPtr_linkBetweenWithParent {operation : Veir.OperationPtr}
    (heq : op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx) :
    operation.getProperties! newCtx.spec opCode =
    operation.getProperties! ctx.spec opCode := by
  grind (gen := 20)

grind_pattern OperationPtr.getProperties!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getProperties! newCtx.spec opCode

@[simp]
theorem OperationPtr.getNumResults!_OperationPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumResults! newCtx.spec = operation.getNumResults! ctx.spec := by
  grind (gen := 20)

grind_pattern OperationPtr.getNumResults!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumResults! newCtx.spec

@[simp]
theorem OpResultPtr.get!_OperationPtr_linkBetweenWithParent {opResult : Veir.OpResultPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    opResult.get! newCtx.spec = opResult.get! ctx.spec := by
  grind (gen := 20)

grind_pattern OpResultPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opResult.get! newCtx.spec

@[simp]
theorem OperationPtr.getNumOperands!_OperationPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumOperands! newCtx.spec = operation.getNumOperands! ctx.spec := by
  grind (gen := 20)

grind_pattern OperationPtr.getNumOperands!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumOperands! newCtx.spec

@[simp]
theorem OpOperandPtr.get!_OperationPtr_linkBetweenWithParent {operand : Veir.OpOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operand.get! newCtx.spec = operand.get! ctx.spec := by
  grind (gen := 20)

grind_pattern OpOperandPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.get! newCtx.spec

@[simp]
theorem OperationPtr.getOperands!_OperationPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getOperands! newCtx.spec = operation.getOperands! ctx.spec := by
  grind

grind_pattern OperationPtr.getOperands!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getOperands! newCtx.spec

@[simp]
theorem OperationPtr.getNumSuccessors!_OperationPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumSuccessors! newCtx.spec = operation.getNumSuccessors! ctx.spec := by
  grind (gen := 20)

grind_pattern OperationPtr.getNumSuccessors!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumSuccessors! newCtx.spec

@[simp]
theorem BlockOperandPtr.get!_OperationPtr_linkBetweenWithParent {operand : Veir.BlockOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operand.get! newCtx.spec = operand.get! ctx.spec := by
  grind (gen := 20)

grind_pattern BlockOperandPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.get! newCtx.spec

@[simp]
theorem OperationPtr.getNumRegions!_OperationPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumRegions! newCtx.spec = operation.getNumRegions! ctx.spec := by
  grind (gen := 20)

grind_pattern OperationPtr.getNumRegions!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumRegions! newCtx.spec

@[simp]
theorem OperationPtr.getRegion!_OperationPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getRegion! newCtx.spec i = operation.getRegion! ctx.spec i := by
  grind (instances := 2000) (gen := 20)

grind_pattern OperationPtr.getRegion!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getRegion! newCtx.spec i

@[simp]
theorem BlockOperandPtrPtr.get!_OperationPtr_linkBetweenWithParent {operandPtr : Veir.BlockOperandPtrPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operandPtr.get! newCtx.spec = operandPtr.get! ctx.spec := by
  grind (gen := 20)

grind_pattern BlockOperandPtrPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operandPtr.get! newCtx.spec

@[simp]
theorem BlockPtr.getNumArguments!_OperationPtr_linkBetweenWithParent {block : Veir.BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    block.getNumArguments! newCtx.spec = block.getNumArguments! ctx.spec := by
  grind (gen := 20)

grind_pattern BlockPtr.getNumArguments!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, block.getNumArguments! newCtx.spec

@[simp]
theorem BlockArgumentPtr.get!_OperationPtr_linkBetweenWithParent {blockArg : Veir.BlockArgumentPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    blockArg.get! newCtx.spec = blockArg.get! ctx.spec := by
  grind (gen := 20)

grind_pattern BlockArgumentPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, blockArg.get! newCtx.spec

@[simp]
theorem RegionPtr.get!_OperationPtr_linkBetweenWithParent {region : Veir.RegionPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    region.get! newCtx.spec = region.get! ctx.spec := by
  grind (gen := 20)

grind_pattern RegionPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, region.get! newCtx.spec

@[simp]
theorem ValuePtr.getFirstUse!_OperationPtr_linkBetweenWithParent {value : Veir.ValuePtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    value.getFirstUse! newCtx.spec = value.getFirstUse! ctx.spec := by
  grind (gen := 20)

grind_pattern ValuePtr.getFirstUse!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, value.getFirstUse! newCtx.spec

theorem ValuePtr.getType!_OperationPtr_linkBetweenWithParent {value : Veir.ValuePtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    value.getType! newCtx.spec = value.getType! ctx.spec := by
  grind (gen := 20)

grind_pattern ValuePtr.getType!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, value.getType! newCtx.spec

@[simp]
theorem OpOperandPtrPtr.get!_OperationPtr_linkBetweenWithParent {opOperandPtr : Veir.OpOperandPtrPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    opOperandPtr.get! newCtx.spec = opOperandPtr.get! ctx.spec := by
  grind (gen := 20)

grind_pattern OpOperandPtrPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opOperandPtr.get! newCtx.spec

end linkBetweenWithParent

/- BlockPtr.linkBetween -/
section linkBetween

attribute [local grind =] Sim.BlockPtr.linkBetween_def
attribute [local grind] Sim.BlockPtr.linkBetweenSim


@[simp, grind =]
theorem BlockPtr.firstUse!_BlockPtr_linkBetween {block : Veir.BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec).firstUse =
    (block.get! ctx.spec).firstUse := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockPtr.capArguments!_BlockPtr_linkBetween {block : Veir.BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec).capArguments =
    (block.get! ctx.spec).capArguments := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockPtr.prev!_BlockPtr_linkBetween {block : Veir.BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec).prev =
    if block = next.spec then
      some block'.spec
    else if block = block'.spec then
      prev.spec
    else
      (block.get! ctx.spec).prev := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockPtr.next!_BlockPtr_linkBetween {block : Veir.BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec).next =
    if block = prev.spec then
      some block'.spec
    else if block = block'.spec then
      next.spec
    else
      (block.get! ctx.spec).next := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockPtr.parent!_BlockPtr_linkBetween {block : Veir.BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec).parent =
    (block.get! ctx.spec).parent := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockPtr_linkBetween {block : Veir.BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec).firstOp =
    (block.get! ctx.spec).firstOp := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockPtr_linkBetween {block : Veir.BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec).lastOp =
    (block.get! ctx.spec).lastOp := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.get!_BlockPtr_linkBetween {operation : Veir.OperationPtr} :
    operation.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    operation.get! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockPtr_linkBetween {operation : Veir.OperationPtr} :
    operation.getOpType! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    operation.getOpType! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockPtr_linkBetween {operation : Veir.OperationPtr} :
    operation.getNumResults! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    operation.getNumResults! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OpResultPtr.get!_BlockPtr_linkBetween {opResult : Veir.OpResultPtr} :
    opResult.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    opResult.get! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockPtr_linkBetween {operation : Veir.OperationPtr} :
    operation.getNumOperands! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    operation.getNumOperands! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OpOperandPtr.get!_BlockPtr_linkBetween {opOperandPtr : Veir.OpOperandPtr} :
    opOperandPtr.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    opOperandPtr.get! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockPtr_linkBetween {operation : Veir.OperationPtr} :
    operation.getOperands! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    operation.getOperands! ctx.spec := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockPtr_linkBetween {operation : Veir.OperationPtr} :
    operation.getNumSuccessors! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    operation.getNumSuccessors! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockOperandPtr.get!_BlockPtr_linkBetween {blockOperand : Veir.BlockOperandPtr} :
    blockOperand.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    blockOperand.get! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockPtr_linkBetween {operation : Veir.OperationPtr} :
    operation.getNumRegions! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    operation.getNumRegions! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockPtr_linkBetween {operation : Veir.OperationPtr} :
    operation.getRegion! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec i =
    operation.getRegion! ctx.spec i := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockPtr_linkBetween {blockOperandPtr : Veir.BlockOperandPtrPtr} :
    blockOperandPtr.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    blockOperandPtr.get! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockPtr_linkBetween {block : Veir.BlockPtr} :
    block.getNumArguments! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    block.getNumArguments! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockPtr_linkBetween {blockArg : Veir.BlockArgumentPtr} :
    blockArg.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    blockArg.get! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem RegionPtr.get!_BlockPtr_linkBetween {region : Veir.RegionPtr} :
    region.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    region.get! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockPtr_linkBetween {value : Veir.ValuePtr} :
    value.getFirstUse! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    value.getFirstUse! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem ValuePtr.getType!_BlockPtr_linkBetween {value : Veir.ValuePtr} :
    value.getType! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    value.getType! ctx.spec := by
  grind (gen := 20)

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockPtr_linkBetween {opOperandPtr : Veir.OpOperandPtrPtr} :
    opOperandPtr.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn).spec =
    opOperandPtr.get! ctx.spec := by
  grind (gen := 20)

end linkBetween

section setParentWithCheck

/- BlockPtr.setParentWithCheck -/
attribute [local grind =] Sim.BlockPtr.setParentWithCheck_def
attribute [local grind] Sim.BlockPtr.setParentWithCheckSim

@[grind →]
theorem BlockPtr.parent!_of_BlockPtr_setParentWithCheck_eq :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    (block'.spec.get! ctx.spec).parent = none := by
  simp [setParentWithCheck_def, setParentWithCheckSim]
  have : (getParent ctx block' (by grind)).InBounds ctx := by grind [generic_ptr_grind]
  grind

theorem BlockPtr.firstUse!_BlockPtr_setParentWithCheck {block : Veir.BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    (block.get! newCtx.spec).firstUse = (block.get! ctx.spec).firstUse := by
  grind

grind_pattern BlockPtr.firstUse!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx.spec).firstUse

theorem BlockPtr.capArguments!_BlockPtr_setParentWithCheck {block : Veir.BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    (block.get! newCtx.spec).capArguments = (block.get! ctx.spec).capArguments := by
  grind

grind_pattern BlockPtr.capArguments!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx.spec).capArguments

theorem BlockPtr.prev!_BlockPtr_setParentWithCheck {block : Veir.BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    (block.get! newCtx.spec).prev = (block.get! ctx.spec).prev := by
  grind

grind_pattern BlockPtr.prev!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx.spec).prev

theorem BlockPtr.next!_BlockPtr_setParentWithCheck {block : Veir.BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    (block.get! newCtx.spec).next = (block.get! ctx.spec).next := by
  grind

grind_pattern BlockPtr.next!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx.spec).next

theorem BlockPtr.parent!_BlockPtr_setParentWithCheck {block : Veir.BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    (block.get! newCtx.spec).parent =
    if block = block'.spec then
      some newParent.spec
    else
      (block.get! ctx.spec).parent := by
  grind

grind_pattern BlockPtr.parent!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx.spec).parent

theorem BlockPtr.firstOp!_BlockPtr_setParentWithCheck {block : Veir.BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    (block.get! newCtx.spec).firstOp = (block.get! ctx.spec).firstOp := by
  grind

grind_pattern BlockPtr.firstOp!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx.spec).firstOp

theorem BlockPtr.lastOp!_BlockPtr_setParentWithCheck {block : Veir.BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    (block.get! newCtx.spec).lastOp = (block.get! ctx.spec).lastOp := by
  grind

grind_pattern BlockPtr.lastOp!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx.spec).lastOp

@[simp]
theorem OperationPtr.get!_BlockPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operation.get! newCtx.spec = operation.get! ctx.spec := by
  grind

grind_pattern OperationPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.get! newCtx.spec

@[simp]
theorem OperationPtr.getOpType!_BlockPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operation.getOpType! newCtx.spec = operation.getOpType! ctx.spec := by
  grind

grind_pattern OperationPtr.getOpType!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getOpType! newCtx.spec

@[simp]
theorem OperationPtr.getNumResults!_BlockPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operation.getNumResults! newCtx.spec = operation.getNumResults! ctx.spec := by
  grind

grind_pattern OperationPtr.getNumResults!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumResults! newCtx.spec

@[simp]
theorem OpResultPtr.get!_BlockPtr_setParentWithCheck {opResult : Veir.OpResultPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    opResult.get! newCtx.spec = opResult.get! ctx.spec := by
  grind

grind_pattern OpResultPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, opResult.get! newCtx.spec

@[simp]
theorem OperationPtr.getNumOperands!_BlockPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operation.getNumOperands! newCtx.spec = operation.getNumOperands! ctx.spec := by
  grind

grind_pattern OperationPtr.getNumOperands!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumOperands! newCtx.spec

@[simp]
theorem OpOperandPtr.get!_BlockPtr_setParentWithCheck {operand : Veir.OpOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operand.get! newCtx.spec = operand.get! ctx.spec := by
  grind

grind_pattern OpOperandPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.get! newCtx.spec

@[simp]
theorem OperationPtr.getOperands!_BlockPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operation.getOperands! newCtx.spec = operation.getOperands! ctx.spec := by
  grind

grind_pattern OperationPtr.getOperands!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getOperands! newCtx.spec

@[simp]
theorem OperationPtr.getNumSuccessors!_BlockPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operation.getNumSuccessors! newCtx.spec = operation.getNumSuccessors! ctx.spec := by
  grind

grind_pattern OperationPtr.getNumSuccessors!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumSuccessors! newCtx.spec

@[simp]
theorem BlockOperandPtr.get!_BlockPtr_setParentWithCheck {operand : Veir.BlockOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operand.get! newCtx.spec = operand.get! ctx.spec := by
  grind

grind_pattern BlockOperandPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.get! newCtx.spec

@[simp]
theorem OperationPtr.getNumRegions!_BlockPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operation.getNumRegions! newCtx.spec = operation.getNumRegions! ctx.spec := by
  grind

grind_pattern OperationPtr.getNumRegions!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumRegions! newCtx.spec

@[simp]
theorem OperationPtr.getRegion!_BlockPtr_setParentWithCheck {operation : Veir.OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operation.getRegion! newCtx.spec i = operation.getRegion! ctx.spec i := by
  grind

grind_pattern OperationPtr.getRegion!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getRegion! newCtx.spec i

@[simp]
theorem BlockOperandPtrPtr.get!_BlockPtr_setParentWithCheck {operandPtr : Veir.BlockOperandPtrPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    operandPtr.get! newCtx.spec = operandPtr.get! ctx.spec := by
  grind

grind_pattern BlockOperandPtrPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operandPtr.get! newCtx.spec

@[simp]
theorem BlockPtr.getNumArguments!_BlockPtr_setParentWithCheck {block : Veir.BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    block.getNumArguments! newCtx.spec = block.getNumArguments! ctx.spec := by
  grind

grind_pattern BlockPtr.getNumArguments!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, block.getNumArguments! newCtx.spec

@[simp]
theorem BlockArgumentPtr.get!_BlockPtr_setParentWithCheck {blockArg : Veir.BlockArgumentPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    blockArg.get! newCtx.spec = blockArg.get! ctx.spec := by
  grind

grind_pattern BlockArgumentPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, blockArg.get! newCtx.spec

@[simp]
theorem RegionPtr.get!_BlockPtr_setParentWithCheck {region : Veir.RegionPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    region.get! newCtx.spec = region.get! ctx.spec := by
  grind

grind_pattern RegionPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, region.get! newCtx.spec

@[simp]
theorem ValuePtr.getFirstUse!_BlockPtr_setParentWithCheck {value : Veir.ValuePtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    value.getFirstUse! newCtx.spec = value.getFirstUse! ctx.spec := by
  grind

grind_pattern ValuePtr.getFirstUse!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, value.getFirstUse! newCtx.spec

@[simp] -- No grind because of Unit
theorem ValuePtr.getType!_BlockPtr_setParentWithCheck {value : Veir.ValuePtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    value.getType! newCtx.spec = value.getType! ctx.spec := by
  grind

grind_pattern ValuePtr.getType!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, value.getType! newCtx.spec

@[simp]
theorem OpOperandPtrPtr.get!_BlockPtr_setParentWithCheck {opOperandPtr : Veir.OpOperandPtrPtr} :
    block'.setParentWithCheck ctx newParent selfIn parentSim = some newCtx →
    opOperandPtr.get! newCtx.spec = opOperandPtr.get! ctx.spec := by
  grind

grind_pattern OpOperandPtrPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, opOperandPtr.get! newCtx.spec

end setParentWithCheck

section linkBetweenWithParent

/- BlockPtr.linkBetweenWithParent -/
attribute [local grind =] Sim.BlockPtr.linkBetweenWithParent_def
attribute [local grind] Sim.BlockPtr.linkBetweenWithParentSim

@[grind →]
theorem BlockPtr.parent!_of_BlockPtr_linkBetweenWithParent_eq :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block'.spec.get! ctx.spec).parent = none := by
  grind

@[simp]
theorem BlockPtr.firstUse!_BlockPtr_linkBetweenWithParent {block : Veir.BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx.spec).firstUse = (block.get! ctx.spec).firstUse := by
  grind (gen := 20)

grind_pattern BlockPtr.firstUse!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx.spec).firstUse

@[simp]
theorem BlockPtr.capArguments!_BlockPtr_linkBetweenWithParent {block : Veir.BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx.spec).capArguments = (block.get! ctx.spec).capArguments := by
  grind (gen := 20)

grind_pattern BlockPtr.capArguments!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx.spec).capArguments

theorem BlockPtr.prev!_BlockPtr_linkBetweenWithParent {block : Veir.BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx.spec).prev =
    if block = next.spec then
      some block'.spec
    else if block = block'.spec then
      prev.spec
    else
      (block.get! ctx.spec).prev := by
  grind (gen := 20)

grind_pattern BlockPtr.prev!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx.spec).prev

@[simp]
theorem BlockPtr.next!_BlockPtr_linkBetweenWithParent {block : Veir.BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx.spec).next =
      if block = prev.spec then
        some block'.spec
      else if block = block'.spec then
        next.spec
      else
        (block.get! ctx.spec).next := by
  grind (gen := 20)

grind_pattern BlockPtr.next!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx.spec).next

@[simp]
theorem BlockPtr.parent!_BlockPtr_linkBetweenWithParent {block : Veir.BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx.spec).parent =
      if block = block'.spec then
        some parent.spec
      else
        (block.get! ctx.spec).parent := by
  grind (gen := 20)

grind_pattern BlockPtr.parent!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx.spec).parent

theorem BlockPtr.firstOp!_BlockPtr_linkBetweenWithParent {block : Veir.BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx.spec).firstOp = (block.get! ctx.spec).firstOp := by
  grind (gen := 20)

grind_pattern BlockPtr.firstOp!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx.spec).firstOp

theorem BlockPtr.lastOp!_BlockPtr_linkBetweenWithParent {block : Veir.BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx.spec).lastOp = (block.get! ctx.spec).lastOp := by
  grind (gen := 20)

grind_pattern BlockPtr.lastOp!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx.spec).lastOp

theorem OperationPtr.get!_BlockPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.get! newCtx.spec = operation.get! ctx.spec := by
  grind (gen := 20)

grind_pattern OperationPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.get! newCtx.spec

theorem OperationPtr.getOpType!_BlockPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getOpType! newCtx.spec = operation.getOpType! ctx.spec := by
  grind (gen := 20)

grind_pattern OperationPtr.getOpType!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getOpType! newCtx.spec

@[simp]
theorem OperationPtr.getNumResults!_BlockPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumResults! newCtx.spec = operation.getNumResults! ctx.spec := by
  grind (gen := 20)

grind_pattern OperationPtr.getNumResults!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumResults! newCtx.spec

@[simp]
theorem OpResultPtr.get!_BlockPtr_linkBetweenWithParent {opResult : Veir.OpResultPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    opResult.get! newCtx.spec = opResult.get! ctx.spec := by
  grind (gen := 20)

grind_pattern OpResultPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opResult.get! newCtx.spec

@[simp]
theorem OperationPtr.getNumOperands!_BlockPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumOperands! newCtx.spec = operation.getNumOperands! ctx.spec := by
  grind (gen := 20)

grind_pattern OperationPtr.getNumOperands!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumOperands! newCtx.spec

@[simp]
theorem OpOperandPtr.get!_BlockPtr_linkBetweenWithParent {operand : Veir.OpOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operand.get! newCtx.spec = operand.get! ctx.spec := by
  grind (gen := 20)

grind_pattern OpOperandPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.get! newCtx.spec

@[simp]
theorem OperationPtr.getOperands!_BlockPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getOperands! newCtx.spec = operation.getOperands! ctx.spec := by
  grind

grind_pattern OperationPtr.getOperands!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getOperands! newCtx.spec

@[simp]
theorem OperationPtr.getNumSuccessors!_BlockPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumSuccessors! newCtx.spec = operation.getNumSuccessors! ctx.spec := by
  grind (gen := 20)

grind_pattern OperationPtr.getNumSuccessors!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumSuccessors! newCtx.spec

@[simp]
theorem BlockOperandPtr.get!_BlockPtr_linkBetweenWithParent {operand : Veir.BlockOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operand.get! newCtx.spec = operand.get! ctx.spec := by
  grind (gen := 20)

grind_pattern BlockOperandPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.get! newCtx.spec

@[simp]
theorem OperationPtr.getNumRegions!_BlockPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumRegions! newCtx.spec = operation.getNumRegions! ctx.spec := by
  grind (gen := 20)

grind_pattern OperationPtr.getNumRegions!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumRegions! newCtx.spec

@[simp]
theorem OperationPtr.getRegion!_BlockPtr_linkBetweenWithParent {operation : Veir.OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getRegion! newCtx.spec i = operation.getRegion! ctx.spec i := by
  grind (gen := 20)

grind_pattern OperationPtr.getRegion!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getRegion! newCtx.spec i

@[simp]
theorem BlockOperandPtrPtr.get!_BlockPtr_linkBetweenWithParent {operandPtr : Veir.BlockOperandPtrPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operandPtr.get! newCtx.spec = operandPtr.get! ctx.spec := by
  grind (gen := 20)

grind_pattern BlockOperandPtrPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operandPtr.get! newCtx.spec

@[simp]
theorem BlockPtr.getNumArguments!_BlockPtr_linkBetweenWithParent {block : Veir.BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    block.getNumArguments! newCtx.spec = block.getNumArguments! ctx.spec := by
  grind (gen := 20)

grind_pattern BlockPtr.getNumArguments!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, block.getNumArguments! newCtx.spec

@[simp]
theorem BlockArgumentPtr.get!_BlockPtr_linkBetweenWithParent {blockArg : Veir.BlockArgumentPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    blockArg.get! newCtx.spec = blockArg.get! ctx.spec := by
  grind (gen := 20)

grind_pattern BlockArgumentPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, blockArg.get! newCtx.spec

@[simp]
theorem RegionPtr.firstBlock!_BlockPtr_linkBetweenWithParent {region : Veir.RegionPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (region.get! newCtx.spec).firstBlock =
      if prev.spec = none ∧ region = parent.spec then
        some block'.spec
      else
        (region.get! ctx.spec).firstBlock := by
  grind (gen := 20) (splits := 20) (instances := 3000)

grind_pattern RegionPtr.firstBlock!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (region.get! newCtx.spec).firstBlock

@[simp]
theorem RegionPtr.lastBlock!_BlockPtr_linkBetweenWithParent {region : Veir.RegionPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (region.get! newCtx.spec).lastBlock =
      if next.spec = none ∧ region = parent.spec then
        some block'.spec
      else
        (region.get! ctx.spec).lastBlock := by
  grind (gen := 20) (splits := 20) (instances := 3000)

grind_pattern RegionPtr.lastBlock!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (region.get! newCtx.spec).lastBlock

@[simp]
theorem RegionPtr.parent!_BlockPtr_linkBetweenWithParent {region : Veir.RegionPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (region.get! newCtx.spec).parent = (region.get! ctx.spec).parent := by
  grind (gen := 20) (splits := 20) (instances := 3000)

grind_pattern RegionPtr.parent!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (region.get! newCtx.spec).parent

@[simp]
theorem ValuePtr.getFirstUse!_BlockPtr_linkBetweenWithParent {value : Veir.ValuePtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    value.getFirstUse! newCtx.spec = value.getFirstUse! ctx.spec := by
  grind (gen := 20)

grind_pattern ValuePtr.getFirstUse!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, value.getFirstUse! newCtx.spec

theorem ValuePtr.getType!_BlockPtr_linkBetweenWithParent {value : Veir.ValuePtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    value.getType! newCtx.spec = value.getType! ctx.spec := by
  grind (gen := 20)

grind_pattern ValuePtr.getType!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, value.getType! newCtx.spec

@[simp]
theorem OpOperandPtrPtr.get!_BlockPtr_linkBetweenWithParent {opOperandPtr : Veir.OpOperandPtrPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    opOperandPtr.get! newCtx.spec = opOperandPtr.get! ctx.spec := by
  grind (gen := 20)

grind_pattern OpOperandPtrPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opOperandPtr.get! newCtx.spec

end linkBetweenWithParent
