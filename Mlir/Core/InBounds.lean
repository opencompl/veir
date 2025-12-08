module

public import Mlir.Core.Basic
import all Mlir.Core.Basic
import Mlir.ForLean

namespace Mlir

public section

attribute [local grind cases] ValuePtr OpOperandPtrPtr GenericPtr -- does this work?

macro "setup_grind_for_basic_proofs" : command => `(
  attribute [local grind cases] ValuePtr OpOperandPtrPtr BlockOperandPtr
  attribute [local grind] Option.maybe BlockOperandPtrPtr.InBounds
    BlockOperandPtrPtr.get BlockOperandPtrPtr.set
    OperationPtr.InBounds RegionPtr.InBounds OpResultPtr.get OpResultPtr.set
    OpOperandPtr.get OpOperandPtr.set BlockOperandPtr.get BlockOperandPtr.set OpResultPtr.get
    OpResultPtr.set BlockArgumentPtr.get BlockArgumentPtr.set BlockArgumentPtr.setType
    BlockArgumentPtr.setFirstUse OpOperandPtrPtr.set OperationPtr.get
    OperationPtr.set BlockPtr.get BlockPtr.set RegionPtr.get RegionPtr.set RegionPtr.InBounds
    BlockOperandPtrPtr.get BlockOperandPtrPtr.set
    BlockArgumentPtr.setLoc BlockPtr.InBounds OperationPtr.getNumResults
)

setup_grind_for_basic_proofs

variable {ctx : IRContext}

section operation

attribute [local grind]
  OperationPtr.setNextOp OperationPtr.setPrevOp
  OperationPtr.setParent OperationPtr.setRegions OperationPtr.setProperties OperationPtr.pushResult
  OperationPtr.setOperands OperationPtr.pushOperand OperationPtr.setResults OperationPtr.allocEmpty Operation.empty

variable {op : OperationPtr} (h : op.InBounds ctx)

@[grind =]
theorem OperationPtr.setNextOp_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setNextOp op ctx newNext? h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpResultPtr.InBounds, OpOperandPtr.InBounds, OpOperandPtrPtr.InBounds, BlockPtr.InBounds]

@[grind =]
theorem OperationPtr.setPrevOp_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setPrevOp op ctx newNext? h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpResultPtr.InBounds, OpOperandPtr.InBounds, OpOperandPtrPtr.InBounds, BlockPtr.InBounds]

@[grind =]
theorem OperationPtr.setParent_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setParent op ctx newNext? h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpResultPtr.InBounds, OpOperandPtr.InBounds, OpOperandPtrPtr.InBounds, BlockPtr.InBounds]

@[grind =]
theorem OperationPtr.setRegions_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setRegions op ctx newRegions h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpResultPtr.InBounds, OpOperandPtr.InBounds, OpOperandPtrPtr.InBounds, BlockPtr.InBounds]

@[grind .]
theorem OperationPtr.getResult_inBounds (op : OperationPtr)
    (hop : op.InBounds ctx) i (h₂ : i < op.getNumResults ctx hop) :
    (op.getResult i).InBounds ctx := by
  grind [getResult, getNumResults, OpResultPtr.InBounds]

@[grind =]
theorem OperationPtr.setResults_genericPtr_mono (ptr : GenericPtr)
    (newResultsSize : OperationPtr.getNumResults op ctx h < newResults.size) :
    (ptr.InBounds (setResults op ctx newResults h) ↔
    (ptr.InBounds ctx
    ∨ (∃ index, ptr = GenericPtr.opResult ⟨op, index⟩ ∧ index < newResults.size ∧ index ≥ OperationPtr.getNumResults op ctx h)
    ∨ (∃ index, ptr = GenericPtr.value (.opResult ⟨op, index⟩) ∧ index < newResults.size ∧ index ≥ OperationPtr.getNumResults op ctx h)
    ∨ (∃ index, ptr = GenericPtr.opOperandPtr (.valueFirstUse (.opResult ⟨op, index⟩)) ∧ index < newResults.size ∧ index ≥ OperationPtr.getNumResults op ctx h))) := by
  constructor
  · cases ptr
    case opResult opResultPtr =>
      rcases opResultPtr with ⟨op, index⟩
      grind [OpResultPtr.InBounds]
    case value value =>
      cases value
      case opResult resultPtr =>
        cases resultPtr
        grind [OpResultPtr.InBounds]
      case blockArgument blockArg =>
        grind [OpResultPtr.InBounds, BlockArgumentPtr.InBounds]
    case opOperandPtr opOperandPtrPtr =>
      cases opOperandPtrPtr
      case operandNextUse operandPtr =>
        grind [OpOperandPtr.InBounds]
      case valueFirstUse value =>
        cases value
        case opResult resultPtr =>
          cases resultPtr
          grind [OpResultPtr.InBounds]
        case blockArgument blockArg =>
          grind [OpResultPtr.InBounds, BlockArgumentPtr.InBounds]
    any_goals grind [OpResultPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockOperandPtr.InBounds, BlockPtr.InBounds, OpResultPtr.InBounds]
  · cases ptr <;> grind [OpResultPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockOperandPtr.InBounds, BlockPtr.InBounds]

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
    (newOperandsSize : (OperationPtr.get op ctx h).operands.size < newOperands.size) :
    (ptr.InBounds (setOperands op ctx newOperands h) ↔
    (ptr.InBounds ctx
    ∨ (∃ index, ptr = GenericPtr.opOperand ⟨op, index⟩ ∧ index < newOperands.size ∧ index ≥ (OperationPtr.get op ctx h).operands.size)
    ∨ (∃ index, ptr = GenericPtr.opOperandPtr (.operandNextUse ⟨op, index⟩) ∧ index < newOperands.size ∧ index ≥ (OperationPtr.get op ctx h).operands.size))) := by
  constructor
  · cases ptr
    case opOperand opOperandPtr =>
      cases opOperandPtr
      grind [OpOperandPtr.InBounds]
    case opOperandPtr opOperandPtrPtr =>
      cases opOperandPtrPtr
      case operandNextUse operandPtr =>
        cases operandPtr
        grind [OpOperandPtr.InBounds]
      case valueFirstUse valuePtr =>
        grind [OpResultPtr.InBounds, BlockArgumentPtr.InBounds]
    all_goals grind [OpResultPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockOperandPtr.InBounds, BlockPtr.InBounds]
  · cases ptr <;> grind [OpResultPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockOperandPtr.InBounds, BlockPtr.InBounds]

@[grind =]
theorem OperationPtr.pushOperand_genericPtr_iff (ptr : GenericPtr) :
    ptr.InBounds (pushOperand op ctx newOperand h) ↔
    (ptr.InBounds ctx
    ∨ (ptr = GenericPtr.opOperand (op.nextOperand ctx))
    ∨ (ptr = GenericPtr.opOperandPtr (.operandNextUse (op.nextOperand ctx)))) := by
  grind [nextOperand]

@[grind .]
theorem OperationPtr.pushOperand_genericPtr_mono (ptr : GenericPtr) :
    ptr.InBounds ctx → ptr.InBounds (pushOperand op ctx newOperand h) := by
  grind [nextOperand]

@[grind =]
theorem OperationPtr.setOperands_ValuePtr_InBounds_mono (ptr : ValuePtr) :
    ptr.InBounds (setOperands op ctx newOperands h) ↔ ptr.InBounds ctx := by
  constructor
  · cases ptr
    case opResult opResultPtr =>
      grind [OpResultPtr.InBounds]
    case blockArgument blockArgumentPtr =>
      grind [BlockArgumentPtr.InBounds]
  · cases ptr
    case opResult opResultPtr =>
      grind [OpResultPtr.InBounds]
    case blockArgument blockArgumentPtr =>
      grind [BlockArgumentPtr.InBounds]

@[grind =]
theorem OperationPtr.setOperands_OpOperandPtr_InBounds_mono_ne {opOperand : OpOperandPtr} :
    opOperand.op ≠ op →
    (opOperand.InBounds (op.setOperands ctx h' newOperands) ↔ opOperand.InBounds ctx) := by
  grind [OpOperandPtr.InBounds]

@[grind =]
theorem OperationPtr.setProperties_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setProperties op ctx newProperties h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpResultPtr.InBounds, OpOperandPtr.InBounds, OpOperandPtrPtr.InBounds, BlockPtr.InBounds]

@[grind .]
theorem OpResultPtr.allocEmpty_no_results {opResult : OpResultPtr}
    (heq : OperationPtr.allocEmpty ctx ty = some (ctx', op')) :
    opResult.op = op' → ¬ opResult.InBounds ctx' := by
  grind [OpResultPtr.InBounds, OperationPtr.InBounds]

@[grind .]
theorem OpOperandPtr.allocEmpty_no_operands {opOperand : OpOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty = some (ctx', op')) :
    opOperand.op = op' → ¬ opOperand.InBounds ctx' := by
  grind [OpOperandPtr.InBounds, OperationPtr.InBounds]

@[grind .]
theorem BlockOperandPtr.allocEmpty_no_operands {blockOperand : BlockOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty = some (ctx', op')) :
    blockOperand.op = op' → ¬ blockOperand.InBounds ctx' := by
  grind [BlockOperandPtr.InBounds, OperationPtr.InBounds]

@[grind .]
theorem OperationPtr.allocEmpty_genericPtr_iff (ptr : GenericPtr) (heq : allocEmpty ctx type = some (ctx', ptr')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .operation ctx.nextID) := by
  constructor <;> cases ptr <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

-- TODO: make this the main statement?
theorem OperationPtr.allocEmpty_genericPtr_iff' (ptr : GenericPtr) (heq : allocEmpty ctx type = some (ctx', ptr')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .operation ptr') := by
  constructor <;> cases ptr <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

theorem OperationPtr.allocEmpty_operationPtr_iff (ptr : OperationPtr) (heq : allocEmpty ctx type = some (ctx', ptr')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr =  ptr') := by
  constructor <;> cases ptr <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

@[grind . ]
theorem OperationPtr.allocEmpty_genericPtr_mono (ptr : GenericPtr) (heq : allocEmpty ctx type = some (ctx', ptr')) :
    ptr.InBounds ctx → ptr.InBounds ctx' := by
  grind

@[grind .]
theorem OperationPtr.allocEmpty_not_inBounds (heq : allocEmpty ctx type = some (ctx', ptr')) :
    ¬ ptr'.InBounds ctx := by
  grind

@[grind .]
theorem OperationPtr.allocEmpty_newBlock_inBounds (heq : allocEmpty ctx type = some (ctx', ptr)) :
    ptr.InBounds ctx' := by
  grind

@[grind .]
theorem OperationPtr.nextOperand_not_inBounds (opPtr : OperationPtr) (h : opPtr.InBounds ctx) : ¬ (opPtr.nextOperand ctx).InBounds ctx := by
  grind [nextOperand, OpOperandPtr.InBounds, OperationPtr.get]

@[grind .]
theorem OperationPtr.nextResult_not_inBounds (opPtr : OperationPtr) (h : opPtr.InBounds ctx) : ¬ (opPtr.nextResult ctx).InBounds ctx := by
  grind [nextOperand, OpResultPtr.InBounds, OperationPtr.get]

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
  grind

@[grind =]
theorem OpOperandPtr.setNextUse_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setNextUse opOperand ctx newNextuse h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;> simp <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

@[grind =]
theorem OpOperandPtr.setBack_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setBack opOperand ctx newNextuse h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;> simp <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

@[grind =]
theorem OpOperandPtr.setOwner_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setOwner opOperand ctx newNextuse h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;> simp <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

@[grind =]
theorem OpOperandPtr.setValue_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setValue opOperand ctx newNextuse h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;> simp <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

theorem OpOperandPtr.inBounds_if_operand_size_eq :
    ((OperationPtr.get opPtr ctx opIn).operands.size = (OperationPtr.get opPtr' ctx' op'In).operands.size) ↔
    (∀ index, (OpOperandPtr.mk opPtr index).InBounds ctx ↔ (OpOperandPtr.mk opPtr' index).InBounds ctx') := by
  constructor
  · intro hsize index
    simp only [InBounds]
    grind [OperationPtr.InBounds, OperationPtr.get]
  · intro hi
    apply Nat.eq_iff_forall_lessthan
    intros i
    have := hi i
    simp [InBounds] at this
    grind [OperationPtr.InBounds, OperationPtr.get]

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
  constructor <;> cases ptr <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpResultPtr.InBounds, OpOperandPtr.InBounds, OpOperandPtrPtr.InBounds, BlockPtr.InBounds]

@[grind =]
theorem OpResultPtr.setFirstUse_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setFirstUse opRes ctx newNextuse h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpResultPtr.InBounds, OpOperandPtr.InBounds, OpOperandPtrPtr.InBounds, BlockPtr.InBounds]

@[grind =]
theorem OpResultPtr.setOwner_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setOwner opRes ctx newNextuse h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpResultPtr.InBounds, OpOperandPtr.InBounds, OpOperandPtrPtr.InBounds, BlockPtr.InBounds]

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
  constructor <;> cases ptr <;> simp <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds, ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

@[grind =]
theorem BlockArgumentPtr.setFirstUse_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setFirstUse blockArgPtr ctx newFirstUse h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

@[grind =]
theorem BlockArgumentPtr.setLoc_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setLoc blockArgPtr ctx newLoc h) ↔ ptr.InBounds ctx := by
  unfold setLoc
  constructor <;> cases ptr <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

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

attribute [local grind]
  BlockPtr.setParent BlockPtr.setFirstUse BlockPtr.setFirstOp BlockPtr.setLastOp BlockPtr.setPrevBlock
  BlockPtr.setNextBlock BlockPtr.allocEmpty
  Block.empty

variable {block : BlockPtr} (h : block.InBounds ctx)

@[grind =]
theorem BlockPtr.setParent_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setParent block ctx newParent h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;> simp <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

@[grind =]
theorem BlockPtr.setFirstUse_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setFirstUse block ctx newFirstUse h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;> simp <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

@[grind =]
theorem BlockPtr.setFirstOp_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setFirstOp block ctx newFirstOp h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;> simp <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

@[grind =]
theorem BlockPtr.setLastOp_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setLastOp block ctx newLastOp h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;> simp <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

@[grind =]
theorem BlockPtr.setNextBlock_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setNextBlock block ctx newNextBlock h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;> simp <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

@[grind =]
theorem BlockPtr.setPrevBlock_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setPrevBlock block ctx newPrevBlock h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;> simp <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

@[grind .]
theorem BlockPtr.allocEmpty_genericPtr_iff (ptr : GenericPtr) (heq : allocEmpty ctx = some (ctx', ptr')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .block ctx.nextID ∨ ptr = .blockOperandPtr (BlockOperandPtrPtr.blockFirstUse ctx.nextID)) := by
  constructor <;> cases ptr <;> simp <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

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
  grind [BlockArgumentPtr.InBounds, BlockPtr.InBounds]

end block

section region

attribute [local grind] RegionPtr.setParent RegionPtr.setFirstBlock RegionPtr.setLastBlock RegionPtr.allocEmpty Region.empty

variable {region : RegionPtr} (h : region.InBounds ctx)

@[grind =]
theorem RegionPtr.setParent_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setParent region ctx newParent h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpResultPtr.InBounds, OpOperandPtr.InBounds, OpOperandPtrPtr.InBounds, BlockPtr.InBounds]

@[grind =]
theorem RegionPtr.setFirstBlock_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setFirstBlock region ctx newFirstBlock h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpResultPtr.InBounds, OpOperandPtr.InBounds, OpOperandPtrPtr.InBounds, BlockPtr.InBounds]

@[grind =]
theorem RegionPtr.setLastBlock_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setLastBlock region ctx newLastBlock h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpResultPtr.InBounds, OpOperandPtr.InBounds, OpOperandPtrPtr.InBounds, BlockPtr.InBounds]

@[grind .]
theorem RegionPtr.allocEmpty_genericPtr_iff (ptr : GenericPtr) (heq : allocEmpty ctx = some (ctx', ptr')) :
    ptr.InBounds ctx' ↔ (ptr.InBounds ctx ∨ ptr = .region ctx.nextID) := by
  constructor <;> cases ptr <;> simp <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]

@[grind .]
theorem RegionPtr.allocEmpty_newBlock_inBounds (heq : allocEmpty ctx = some (ctx', ptr)) :
    ptr.InBounds ctx' := by
  grind [allocEmpty]

end region

section operandptr

variable {opOperandPtr : OpOperandPtrPtr} (h : opOperandPtr.InBounds ctx)

/- OpOperandPtrPtr.set -/

@[grind =]
theorem OpOperandPtrPtr.set_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (set opOperandPtr ctx newPtr h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;> simp <;>
    grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
           ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds]


end operandptr

section blockoperand

attribute [local grind] Option.maybe BlockOperandPtr.setNextUse BlockOperandPtr.setOwner
  BlockOperandPtr.setBack BlockOperandPtr.setNextUse BlockOperandPtr.setValue

variable {blockOperand : BlockOperandPtr} (h : blockOperand.InBounds ctx)

@[grind .]
theorem BlockOperandPtr.operation_inBounds_of_inBounds (h : blockOperand.InBounds ctx) :
    blockOperand.op.InBounds ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.setNextUse_genericPtr_mono (ptr : GenericPtr) :
    ptr.InBounds (setNextUse blockOperand ctx newNextuse h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;> simp
  case mpr.blockOperandPtr =>
    rename_i ptr
    intros
    cases ptr <;> grind [BlockOperandPtr.InBounds]
  all_goals grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
                   ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds, BlockOperandPtrPtr.InBounds]


@[grind =]
theorem BlockOperandPtr.setBack_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setBack blockOperand ctx newNextuse h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;> simp
  case mpr.blockOperandPtr =>
    rename_i ptr
    intros
    cases ptr <;> grind [BlockOperandPtr.InBounds]
  all_goals grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
                   ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds, BlockOperandPtrPtr.InBounds]

@[grind =]
theorem BlockOperandPtr.setOwner_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setOwner blockOperand ctx newNextuse h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;> simp
  case mpr.blockOperandPtr =>
    rename_i ptr
    intros
    cases ptr <;> grind [BlockOperandPtr.InBounds]
  all_goals grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
                   ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds, BlockOperandPtrPtr.InBounds]

@[grind =]
theorem BlockOperandPtr.setValue_genericPtr_mono (ptr : GenericPtr)  :
    ptr.InBounds (setValue blockOperand ctx newNextuse h) ↔ ptr.InBounds ctx := by
  constructor <;> cases ptr <;> simp
  case mpr.blockOperandPtr =>
    rename_i ptr
    intros
    cases ptr <;> grind [BlockOperandPtr.InBounds]
  all_goals grind [BlockOperandPtr.InBounds, BlockArgumentPtr.InBounds, OpOperandPtr.InBounds, BlockPtr.InBounds,
                   ValuePtr.InBounds, OpOperandPtrPtr.InBounds, OpResultPtr.InBounds, BlockOperandPtrPtr.InBounds]

end blockoperand
