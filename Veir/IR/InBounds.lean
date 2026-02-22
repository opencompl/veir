module

public import Veir.IR.Basic
import all Veir.IR.Basic
import Veir.ForLean

namespace Veir

variable { opInfo : Type} [OpInfo opInfo]

public section

attribute [local grind cases] ValuePtr OpOperandPtrPtr GenericPtr -- does this work?

/- Mark all get/set and InBounds definitions as transparent for grind -/
setup_grind_with_get_set_definitions
attribute [local grind] BlockOperandPtrPtr.InBounds BlockOperandPtr.InBounds OperationPtr.InBounds
  RegionPtr.InBounds OpResultPtr.InBounds RegionPtr.InBounds BlockPtr.InBounds OpOperandPtr.InBounds
  BlockArgumentPtr.InBounds

@[grind .]
theorem IRContext.empty_not_inBounds (ptr : GenericPtr)  :
    ¬ ptr.InBounds (empty opInfo) := by
  grind

variable {ctx ctx' : IRContext opInfo}

section operation

variable {op : OperationPtr} (h : op.InBounds ctx)

@[grind =]
theorem OperationPtr.setNextOp_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setNextOp op ctx newNext? h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem OperationPtr.setPrevOp_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setPrevOp op ctx newNext? h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem OperationPtr.setParent_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setParent op ctx newNext? h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem OperationPtr.setRegions_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setRegions op ctx newRegions h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem OperationPtr.pushRegion_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (pushRegion op ctx newRegion h) ↔ ptr.InBounds ctx := by
  grind

@[grind .]
theorem OperationPtr.getOpOperand_inBounds (op : OperationPtr)
    (hop : op.InBounds ctx) i (h₂ : i < op.getNumOperands ctx hop) :
    (op.getOpOperand i).InBounds ctx := by
  grind

@[grind .]
theorem OperationPtr.getBlockOperand_inBounds (op : OperationPtr)
    (hop : op.InBounds ctx) i (h₂ : i < op.getNumSuccessors ctx hop) :
    (op.getBlockOperand i).InBounds ctx := by
  grind

@[grind .]
theorem OperationPtr.getResult_inBounds (op : OperationPtr)
    (hop : op.InBounds ctx) i (h₂ : i < op.getNumResults ctx hop) :
    (op.getResult i).InBounds ctx := by
  grind

@[grind =]
theorem OperationPtr.setResults_genericPtr_mono (ptr : GenericPtr)
    (newResultsSize : OperationPtr.getNumResults op ctx h < newResults.size) :
    (ptr.InBounds (setResults op ctx newResults h) ↔
    (ptr.InBounds ctx
    ∨ (∃ index, ptr = GenericPtr.opResult ⟨op, index⟩ ∧ index < newResults.size ∧ index ≥ OperationPtr.getNumResults op ctx h)
    ∨ (∃ index, ptr = GenericPtr.value (.opResult ⟨op, index⟩) ∧ index < newResults.size ∧ index ≥ OperationPtr.getNumResults op ctx h)
    ∨ (∃ index, ptr = GenericPtr.opOperandPtr (.valueFirstUse (.opResult ⟨op, index⟩)) ∧ index < newResults.size ∧ index ≥ OperationPtr.getNumResults op ctx h))) := by
  grind

@[grind .]
theorem OperationPtr.setResults_genericPtr_mono_impl (ptr : GenericPtr)
    (newOperandsSize : OperationPtr.getNumResults op ctx h < newResults.size) :
    ptr.InBounds ctx → ptr.InBounds (setResults op ctx newResults h) := by
  grind

@[grind =]
theorem OperationPtr.pushResult_genericPtr_mono (ptr : GenericPtr) :
    (ptr.InBounds (pushResult op ctx newResult h) ↔
    (ptr.InBounds ctx
    ∨ (ptr = GenericPtr.opResult (op.nextResult ctx))
    ∨ (ptr = GenericPtr.value (.opResult (op.nextResult ctx)))
    ∨ (ptr = GenericPtr.opOperandPtr (.valueFirstUse (.opResult (op.nextResult ctx)))))) := by
  grind

@[grind .]
theorem OperationPtr.pushResult_genericPtr_mono_impl (ptr : GenericPtr) :
    ptr.InBounds ctx → ptr.InBounds (pushResult op ctx newResult h) := by
  grind

@[grind =]
theorem OperationPtr.setOperands_genericPtr_mono (ptr : GenericPtr)
    (newOperandsSize : OperationPtr.getNumOperands op ctx h < newOperands.size) :
    (ptr.InBounds (setOperands op ctx newOperands h) ↔
    (ptr.InBounds ctx
    ∨ (∃ index, ptr = GenericPtr.opOperand ⟨op, index⟩ ∧ index < newOperands.size ∧ index ≥ OperationPtr.getNumOperands op ctx h)
    ∨ (∃ index, ptr = GenericPtr.opOperandPtr (.operandNextUse ⟨op, index⟩) ∧ index < newOperands.size ∧ index ≥ OperationPtr.getNumOperands op ctx h))) := by
  grind

@[grind =]
theorem OperationPtr.pushOperand_genericPtr_iff (ptr : GenericPtr) :
    ptr.InBounds (pushOperand op ctx newOperand h) ↔
    (ptr.InBounds ctx
    ∨ (ptr = GenericPtr.opOperand (op.nextOperand ctx))
    ∨ (ptr = GenericPtr.opOperandPtr (.operandNextUse (op.nextOperand ctx)))) := by
  grind

@[grind .]
theorem OperationPtr.pushOperand_genericPtr_mono (ptr : GenericPtr) :
    ptr.InBounds ctx → ptr.InBounds (pushOperand op ctx newOperand h) := by
  grind

@[grind =]
theorem OperationPtr.setOperands_ValuePtr_InBounds_mono (ptr : ValuePtr) :
    ptr.InBounds (setOperands op ctx newOperands h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem OperationPtr.setOperands_OpOperandPtr_InBounds_mono_ne {opOperand : OpOperandPtr} :
    opOperand.op ≠ op →
    (opOperand.InBounds (op.setOperands ctx h' newOperands) ↔ opOperand.InBounds ctx) := by
  grind

@[grind =]
theorem OperationPtr.setBlockOperands_genericPtr_mono (ptr : GenericPtr)
    (newOperandsSize : OperationPtr.getNumSuccessors! op ctx < newOperands.size) :
    (ptr.InBounds (setBlockOperands op ctx newOperands h) ↔
    (ptr.InBounds ctx
    ∨ (∃ index, ptr = GenericPtr.blockOperand ⟨op, index⟩ ∧ index < newOperands.size
      ∧ index ≥ OperationPtr.getNumSuccessors! op ctx)
    ∨ (∃ index, ptr = GenericPtr.blockOperandPtr (.blockOperandNextUse ⟨op, index⟩)
      ∧ index < newOperands.size ∧ index ≥ OperationPtr.getNumSuccessors! op ctx))) := by
  grind

@[grind =]
theorem OperationPtr.pushBlockOperand_genericPtr_iff (ptr : GenericPtr) :
    ptr.InBounds (pushBlockOperand op ctx newOperand h) ↔
    (ptr.InBounds ctx
    ∨ (ptr = GenericPtr.blockOperand (op.nextBlockOperand ctx))
    ∨ (ptr = GenericPtr.blockOperandPtr (.blockOperandNextUse (op.nextBlockOperand ctx)))) := by
  grind

@[grind .]
theorem OperationPtr.pushBlockOperand_genericPtr_mono (ptr : GenericPtr) :
    ptr.InBounds ctx → ptr.InBounds (pushBlockOperand op ctx newOperand h) := by
  grind

@[grind =]
theorem OperationPtr.setBlockOperands_ValuePtr_InBounds_mono (ptr : ValuePtr) :
    ptr.InBounds (setBlockOperands op ctx newOperands h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem OperationPtr.setBlockOperands_OpOperandPtr_InBounds_mono_ne {opOperand : OpOperandPtr} :
    opOperand.op ≠ op →
    (opOperand.InBounds (op.setBlockOperands ctx h' newOperands) ↔ opOperand.InBounds ctx) := by
  grind

@[grind =]
theorem OperationPtr.setProperties_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setProperties op ctx newProperties h propEq) ↔ ptr.InBounds ctx := by
  grind

@[grind .]
theorem OpResultPtr.allocEmpty_no_results {opResult : OpResultPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opResult.op = op' → ¬ opResult.InBounds ctx' := by
  grind

@[grind .]
theorem OpOperandPtr.allocEmpty_no_operands {opOperand : OpOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opOperand.op = op' → ¬ opOperand.InBounds ctx' := by
  grind

@[grind .]
theorem BlockOperandPtr.allocEmpty_no_operands {blockOperand : BlockOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockOperand.op = op' → ¬ blockOperand.InBounds ctx' := by
  grind

@[grind .]
theorem OperationPtr.allocEmpty_genericPtr_iff (ptr : GenericPtr)
    (heq : allocEmpty ctx type properties = some (ctx', ptr')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .operation ⟨ctx.nextID⟩) := by
  grind

-- TODO: make this the main statement?
theorem OperationPtr.allocEmpty_genericPtr_iff' (ptr : GenericPtr)
    (heq : allocEmpty ctx type properties = some (ctx', ptr')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .operation ptr') := by
  grind

theorem OperationPtr.allocEmpty_operationPtr_iff (ptr : OperationPtr)
    (heq : allocEmpty ctx type properties = some (ctx', ptr')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr =  ptr') := by
  grind

@[grind . ]
theorem OperationPtr.allocEmpty_genericPtr_mono (ptr : GenericPtr)
    (heq : allocEmpty ctx type properties = some (ctx', ptr')) :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  grind

@[grind .]
theorem OperationPtr.allocEmpty_not_inBounds
    (heq : allocEmpty ctx type properties = some (ctx', ptr')) :
    ¬ ptr'.InBounds ctx := by
  grind

@[grind .]
theorem OperationPtr.allocEmpty_newBlock_inBounds
    (heq : allocEmpty ctx type properties = some (ctx', ptr)) :
    ptr.InBounds ctx' := by
  grind


@[grind →]
theorem OpResultPtr.dealloc.inBounds_genericPtr_of_inBounds_dealloc {ptr : GenericPtr} :
    ptr.InBounds (OperationPtr.dealloc op ctx inBounds) → ptr.InBounds ctx := by
  grind

@[grind .]
theorem OpOperandPtr.dealloc.inBounds_dealloc_genericPtr {ptr : GenericPtr} :
    ptr.InBounds ctx →
    (match ptr with
     | .operation op => op ≠ op'
     | .opResult or => or.op ≠ op'
     | .opOperand oo => oo.op ≠ op'
     | .blockOperand bo => bo.op ≠ op'
     | .value ( .opResult or ) => or.op ≠ op'
     | .opOperandPtr ( .operandNextUse oo) => oo.op ≠ op'
     | .opOperandPtr ( .valueFirstUse ( .opResult or ) ) => or.op ≠ op'
     | .blockOperandPtr ( .blockOperandNextUse oo) => oo.op ≠ op'
     | _ => True) →
    ptr.InBounds (OperationPtr.dealloc op' ctx inBounds) := by
  grind

theorem OpResultPtr.InBounds.op_ne_of_inBounds_OperationPtr_dealloc {opResult : OpResultPtr} :
    opResult.InBounds (OperationPtr.dealloc op' ctx inBounds) → opResult.op ≠ op' := by
  grind

theorem OpOperandPtr.InBounds.op_ne_of_inBounds_OperationPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.InBounds (OperationPtr.dealloc op' ctx inBounds) → opOperand.op ≠ op' := by
  grind

theorem BlockOperandPtr.InBounds.op_ne_of_inBounds_OperationPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.InBounds (OperationPtr.dealloc op' ctx inBounds) → blockOperand.op ≠ op' := by
  grind

@[grind .]
theorem OperationPtr.nextOperand_not_inBounds (opPtr : OperationPtr) (h : opPtr.InBounds ctx) : ¬ (opPtr.nextOperand ctx).InBounds ctx := by
  grind

@[grind .]
theorem OperationPtr.nextBlockOperand_not_inBounds (opPtr : OperationPtr) (h : opPtr.InBounds ctx) : ¬ (opPtr.nextBlockOperand ctx).InBounds ctx := by
  grind

@[grind .]
theorem OperationPtr.nextResult_not_inBounds (opPtr : OperationPtr) (h : opPtr.InBounds ctx) : ¬ (opPtr.nextResult ctx).InBounds ctx := by
  grind

end operation

/- OpOperandPtr -/

section opoperand

attribute [local grind] OpOperandPtr.setNextUse OpOperandPtr.setBack OpOperandPtr.setOwner OpOperandPtr.setValue

variable {opOperand : OpOperandPtr} (h : opOperand.InBounds ctx)

@[grind =]
theorem OpOperandPtr.get_set {op : OperationPtr} (hop : op.InBounds (opOperand.set ctx x h)) :
    (op.get (opOperand.set ctx x)).operands =
      if heq : op = opOperand.op
        then (op.get ctx).operands.set opOperand.index x (by grind)
        else (op.get ctx).operands := by
  grind

@[grind .]
theorem OpOperandPtr.operation_inBounds_of_inBounds (h : opOperand.InBounds ctx) :
    opOperand.op.InBounds ctx := by
  grind [OpOperandPtr.InBounds]

@[grind =]
theorem OpOperandPtr.setNextUse_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setNextUse opOperand ctx newNextuse h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem OpOperandPtr.setBack_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setBack opOperand ctx newNextuse h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem OpOperandPtr.setOwner_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setOwner opOperand ctx newNextuse h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem OpOperandPtr.setValue_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setValue opOperand ctx newNextuse h) ↔ ptr.InBounds ctx := by
  grind

theorem OpOperandPtr.inBounds_if_operand_size_eq :
    (OperationPtr.getNumOperands opPtr ctx opIn = OperationPtr.getNumOperands opPtr' ctx' op'In) ↔
    (∀ index, (OpOperandPtr.mk opPtr index).InBounds ctx ↔ (OpOperandPtr.mk opPtr' index).InBounds ctx') := by
  constructor
  · grind
  · intro hi
    apply Nat.eq_iff_forall_lessthan
    intros i
    have := hi i
    grind

end opoperand

section opresult

attribute [local grind] OpResultPtr.setType OpResultPtr.setFirstUse OpResultPtr.setOwner

variable {opRes : OpResultPtr} (h : opRes.InBounds ctx)

@[grind .]
theorem OpResultPtr.operation_inBounds_of_inBounds (h : opRes.InBounds ctx) :
    opRes.op.InBounds ctx := by
  grind

@[grind =]
theorem OpResultPtr.setType_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setType opRes ctx newNextuse h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem OpResultPtr.setFirstUse_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setFirstUse opRes ctx newNextuse h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem OpResultPtr.setOwner_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setOwner opRes ctx newNextuse h) ↔ ptr.InBounds ctx := by
  grind

end opresult

section blockargument

variable {ba : BlockArgumentPtr}

@[grind .]
theorem BlockArgumentPtr.operation_inBounds_of_inBounds (h : ba.InBounds ctx) :
    ba.block.InBounds ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.setType_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setType blockArgPtr ctx newType h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.setFirstUse_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setFirstUse blockArgPtr ctx newFirstUse h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.setLoc_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setLoc blockArgPtr ctx newLoc h) ↔ ptr.InBounds ctx := by
  grind

end blockargument

section value

attribute [local grind] ValuePtr.setFirstUse ValuePtr.setType

variable {value : ValuePtr} (h : value.InBounds ctx)

@[grind =]
theorem ValuePtr.setType_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setType value ctx newNextuse h) ↔ ptr.InBounds ctx := by
  grind


@[grind =]
theorem ValuePtr.setFirstUse_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setFirstUse value ctx newNextuse h) ↔ ptr.InBounds ctx := by
  grind

end value

section block

variable {block : BlockPtr} (h : block.InBounds ctx)

@[grind .]
theorem BlockPtr.getArgument_inBounds (block : BlockPtr)
    (hblock : block.InBounds ctx) i (h₂ : i < block.getNumArguments ctx hblock) :
    (block.getArgument i).InBounds ctx := by
  grind

@[grind =]
theorem BlockPtr.setParent_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setParent block ctx newParent h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem BlockPtr.setFirstUse_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setFirstUse block ctx newFirstUse h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem BlockPtr.setFirstOp_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setFirstOp block ctx newFirstOp h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem BlockPtr.setLastOp_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setLastOp block ctx newLastOp h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem BlockPtr.setNextBlock_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setNextBlock block ctx newNextBlock h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem BlockPtr.setPrevBlock_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setPrevBlock block ctx newPrevBlock h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem BlockPtr.setArguments_genericPtr_mono (ptr : GenericPtr)
    (newResultsSize : BlockPtr.getNumArguments block ctx h ≤ newArguments.size) :
    (ptr.InBounds (setArguments block ctx newArguments h) ↔
    (ptr.InBounds ctx
    ∨ (∃ index, ptr = .blockArgument ⟨block, index⟩ ∧
        index < newArguments.size ∧
        index ≥ BlockPtr.getNumArguments block ctx h)
    ∨ (∃ index, ptr = .value (.blockArgument ⟨block, index⟩) ∧
        index < newArguments.size ∧ index ≥ BlockPtr.getNumArguments block ctx h)
    ∨ (∃ index, ptr = .opOperandPtr (.valueFirstUse (.blockArgument ⟨block, index⟩)) ∧
        index < newArguments.size ∧ index ≥ BlockPtr.getNumArguments block ctx h))) := by
  grind

@[grind .]
theorem BlockPtr.setArguments_genericPtr_mono_impl (ptr : GenericPtr)
    (newOperandsSize : BlockPtr.getNumArguments block ctx h ≤ newArguments.size) :
    ptr.InBounds ctx → ptr.InBounds (setArguments block ctx newArguments h) := by
  grind

@[grind =]
theorem BlockPtr.pushArgument_genericPtr_mono (ptr : GenericPtr) :
    (ptr.InBounds (pushArgument block ctx newArguments h) ↔
    (ptr.InBounds ctx
    ∨ (ptr = .blockArgument (block.nextArgument ctx))
    ∨ (ptr = .value (.blockArgument (block.nextArgument ctx)))
    ∨ (ptr = .opOperandPtr (.valueFirstUse (.blockArgument (block.nextArgument ctx)))))) := by
  grind [getArgument]

@[grind .]
theorem BlockPtr.pushResult_genericPtr_mono_impl (ptr : GenericPtr) :
    ptr.InBounds ctx → ptr.InBounds (pushArgument block ctx newArguments h) := by
  grind

@[grind .]
theorem BlockPtr.allocEmpty_genericPtr_iff (ptr : GenericPtr) (heq : allocEmpty ctx = some (ctx', ptr')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .block ⟨ctx.nextID⟩ ∨ ptr = .blockOperandPtr (BlockOperandPtrPtr.blockFirstUse ⟨ctx.nextID⟩)) := by
  grind

theorem BlockPtr.allocEmpty_genericPtr_iff' (ptr : GenericPtr) (heq : allocEmpty ctx = some (ctx', ptr')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .block ptr' ∨ ptr = .blockOperandPtr (BlockOperandPtrPtr.blockFirstUse ptr')) := by
  grind

@[grind .]
theorem BlockPtr.allocEmpty_genericPtr_mono (ptr : GenericPtr) (heq : allocEmpty ctx = some (ctx', ptr')) :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  grind

@[grind .]
theorem BlockPtr.allocEmpty_newBlock_inBounds (heq : allocEmpty ctx = some (ctx', ptr)) :
    ptr.InBounds ctx' := by
  grind

@[grind .]
theorem BlockPtr.allocEmpty_not_inBounds (heq : allocEmpty ctx = some (ctx', ptr')) :
    ¬ ptr'.InBounds ctx := by
  grind

@[grind .]
theorem BlockPtr.allocEmpty_no_argument {ba : BlockArgumentPtr}
    (heq : allocEmpty ctx = some (ctx', ba')) :
    ba.block = ba' → ¬ ba.InBounds ctx' := by
  grind

end block

section region

variable {region : RegionPtr} (h : region.InBounds ctx)

@[grind =]
theorem RegionPtr.setParent_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setParent region ctx newParent h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem RegionPtr.setFirstBlock_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setFirstBlock region ctx newFirstBlock h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem RegionPtr.setLastBlock_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setLastBlock region ctx newLastBlock h) ↔ ptr.InBounds ctx := by
  grind

@[grind .]
theorem RegionPtr.allocEmpty_genericPtr_iff (ptr : GenericPtr) (heq : allocEmpty ctx = some (ctx', ptr')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .region ⟨ctx.nextID⟩) := by
  constructor <;> cases ptr <;> simp <;>
    try grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

theorem RegionPtr.allocEmpty_genericPtr_iff' (ptr : GenericPtr) (heq : allocEmpty ctx = some (ctx', ptr')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .region ptr') := by
  constructor <;> cases ptr <;> simp <;>
    try grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

@[grind .]
theorem RegionPtr.allocEmpty_newBlock_inBounds (heq : allocEmpty ctx = some (ctx', ptr)) :
    ptr.InBounds ctx' := by
  grind [allocEmpty]

@[grind .]
theorem RegionPtr.allocEmpty_genericPtr_mono (ptr : GenericPtr) (heq : allocEmpty ctx = some (ctx', ptr')) :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  grind

end region

section operandptr

variable {opOperandPtr : OpOperandPtrPtr} (h : opOperandPtr.InBounds ctx)

/- OpOperandPtrPtr.set -/

@[grind =]
theorem OpOperandPtrPtr.set_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (set opOperandPtr ctx newPtr h) ↔ ptr.InBounds ctx := by
  grind

end operandptr

section blockoperand

variable {blockOperand : BlockOperandPtr} (h : blockOperand.InBounds ctx)

@[grind .]
theorem BlockOperandPtr.operation_inBounds_of_inBounds (h : blockOperand.InBounds ctx) :
    blockOperand.op.InBounds ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.setNextUse_genericPtr_mono (ptr : GenericPtr) :
    ptr.InBounds (setNextUse blockOperand ctx newNextuse h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.setBack_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setBack blockOperand ctx newNextuse h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.setOwner_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setOwner blockOperand ctx newNextuse h) ↔ ptr.InBounds ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.setValue_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setValue blockOperand ctx newNextuse h) ↔ ptr.InBounds ctx := by
  grind

end blockoperand

section blockOperandPtr

variable {blockOperandPtr : BlockOperandPtrPtr} (h : blockOperandPtr.InBounds ctx)

@[grind =]
theorem BlockOperandPtrPtr.set_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (set blockOperandPtr ctx newPtr h) ↔ ptr.InBounds ctx := by
  grind

end blockOperandPtr
