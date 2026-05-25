module

public import Veir.IR.Buffed.SimDefs
import Veir.IR.InBounds
import Veir.IR.Fields
import Veir.IR.GetSet
import Veir.IR.Buffed.Layout
public import Veir.Prelude

open Veir.Buffed (ptrCard countCard)

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}

public section

attribute [local grind =] Option.maybe_def

section default

@[grind .]
theorem IRContext.default_IsRepr : IRContext.IsRepr (default : IRContext OpInfo) := by
  simp only [default_def]
  grind [IRContext.IsRepr, OperationPtr.inBounds_def, BlockPtr.inBounds_def, RegionPtr.inBounds_def]

end default

@[grind .]
theorem IRContext.empty_fieldsIsRepr : (empty OpInfo).IsRepr := by
  constructor <;> grind

@[grind .]
theorem OperationPtr.setNextOp_fieldsIsRepr :
    ctx.IsRepr → (setNextOp op ctx newOp h).IsRepr := by
  grind

@[grind .]
theorem OperationPtr.setPrevOp_fieldsIsRepr :
    ctx.IsRepr → (setPrevOp op ctx newOp h).IsRepr := by
  grind

@[grind .]
theorem OperationPtr.setParent_fieldsIsRepr :
    ctx.IsRepr → (setParent op ctx newOp h).IsRepr := by
  grind

@[grind .]
theorem OperationPtr.setRegions_fieldsIsRepr {ctx : IRContext OpInfo} {h} (hcount : newRegions.size ≤ countCard) :
    ctx.IsRepr → (setRegions op ctx newRegions h).IsRepr := by
  grind

@[grind .]
theorem OperationPtr.pushResult_fieldsIsRepr {newResult : OpResult} {op : OperationPtr} h
    (hcound : op.getNumResults! ctx < countCard) :
    ctx.IsRepr → (op.pushResult ctx newResult h).IsRepr := by
  grind

@[grind .]
theorem OperationPtr.setProperties_fieldsIsRepr :
    ctx.IsRepr → (setProperties op ctx newProperties isRepr hprop).IsRepr := by
  grind

@[grind .]
theorem OperationPtr.setAttributes_fieldsIsRepr {op : OperationPtr} {opIn : op.InBounds ctx} :
    ctx.IsRepr → (op.setAttributes ctx newAttrs opIn).IsRepr := by
  grind

@[grind .]
theorem OperationPtr.setOperands_push_fieldsIsRepr  (newOperand : OpOperand)
    (hcount : op.getNumOperands! ctx < countCard) :
    ctx.IsRepr → (pushOperand op ctx newOperand h).IsRepr := by
  grind

@[grind .]
theorem OperationPtr.pushBlockOperand_push_fieldsIsRepr
    (newOperand : BlockOperand) (hcount : op.getNumSuccessors! ctx < countCard) :
    ctx.IsRepr → (pushBlockOperand op ctx newOperand h).IsRepr := by
  grind

attribute [local grind] Operation.empty in
@[grind .]
theorem OperationPtr.allocEmpty_fieldsIsRepr
    (heq : allocEmpty ctx type prop capResults capBlockOperands capRegions capOperands = some (ctx', ptr')) :
    ptr'.IsRepr → ctx.IsRepr → ctx'.IsRepr := by
  grind

@[grind .]
theorem BlockOperandPtr.setBack_fieldsIsRepr {blockOperand} {ctx : IRContext OpInfo} {h newBack} :
    ctx.IsRepr → (setBack blockOperand ctx newBack h).IsRepr := by
  grind

@[grind .]
theorem BlockOperandPtr.setOwner_fieldsIsRepr {blockOperand} {ctx : IRContext OpInfo} {h newOwner} :
    ctx.IsRepr → (setOwner blockOperand ctx newOwner h).IsRepr := by
  grind

@[grind .]
theorem BlockOperandPtr.setNextUse_fieldsIsRepr {blockOperand} {ctx : IRContext OpInfo} {h newNextUse} :
    ctx.IsRepr → (setNextUse blockOperand ctx newNextUse h).IsRepr := by
  grind

@[grind .]
theorem BlockOperandPtr.setValue_fieldsIsRepr {blockOperand} {ctx : IRContext OpInfo} {h newValue} :
    ctx.IsRepr → (setValue blockOperand ctx newValue h).IsRepr := by
  grind

@[grind .]
theorem BlockArgumentPtr.setType_fieldsIsRepr :
    ctx.IsRepr → (setType blockArgPtr ctx newType h).IsRepr := by
  grind

@[grind .]
theorem BlockArgumentPtr.setFirstUse_fieldsIsRepr :
    ctx.IsRepr → (setFirstUse blockArgPtr ctx newFirstUse h).IsRepr := by
  grind

@[grind .]
theorem BlockArgumentPtr.setLoc_fieldsIsRepr :
    ctx.IsRepr → (setLoc blockArgPtr ctx newLoc h).IsRepr := by
  grind

@[grind .]
theorem BlockPtr.setParent_fieldsIsRepr :
    ctx.IsRepr → (setParent block ctx parent h).IsRepr := by
  grind

@[grind .]
theorem BlockPtr.setFirstUse_fieldsIsRepr :
    ctx.IsRepr → (setFirstUse block ctx newFirstUse h).IsRepr := by
  grind

@[grind .]
theorem BlockPtr.setFirstOp_fieldsIsRepr :
    ctx.IsRepr → (setFirstOp block ctx newFirstOp h).IsRepr := by
  grind

@[grind .]
theorem BlockPtr.setLastOp_fieldsIsRepr :
    ctx.IsRepr → (setLastOp block ctx newLastOp h).IsRepr := by
  grind

@[grind .]
theorem BlockPtr.setNextBlock_fieldsIsRepr :
    ctx.IsRepr → (setNextBlock block ctx newNextBlock h).IsRepr := by
  grind

@[grind .]
theorem BlockPtr.setPrevBlock_fieldsIsRepr :
    ctx.IsRepr → (setPrevBlock block ctx newPrevBlock h).IsRepr := by
  grind

attribute [local grind] Block.empty in
@[grind .]
theorem BlockPtr.allocEmpty_fieldsIsRepr (heq : allocEmpty ctx capArguments = some (ctx', ptr')) :
    ptr'.IsRepr → ctx.IsRepr → ctx'.IsRepr := by
  grind

attribute [local grind →] Array.getElem_mem in
attribute [local grind] Block.empty in
@[grind .]
theorem BlockPtr.setArguments_fieldsIsRepr
    (hcount : newArguments.size ≤ countCard) :
    ctx.IsRepr → (setArguments block ctx newArguments h).IsRepr := by
  grind

@[grind .]
theorem BlockPtr.pushArgument_fieldsIsRepr
    (hcount : block.getNumArguments! ctx < countCard) :
    ctx.IsRepr → (pushArgument block ctx newArgument h).IsRepr := by
  grind

@[grind .]
theorem OpOperandPtr.setNextUse_fieldsIsRepr :
    ctx.IsRepr → (setNextUse opOperand ctx newNextUse h).IsRepr := by
  grind

@[grind .]
theorem OpOperandPtr.setBack_fieldsIsRepr :
    ctx.IsRepr → (setBack opOperand ctx newBack h).IsRepr := by
  grind

@[grind .]
theorem OpOperandPtr.setOwner_fieldsIsRepr :
    ctx.IsRepr → (setOwner opOperand ctx newOwner h).IsRepr := by
  grind

@[grind .]
theorem OpOperandPtrPtr.set_fieldsIsRepr_maybe :
    ctx.IsRepr → (set opOperandPtr ctx newPtr h).IsRepr := by
  grind

@[grind .]
theorem OpOperandPtr.setValue_fieldsIsRepr :
    ctx.IsRepr → (setValue opOperand ctx newValue h).IsRepr := by
  grind

@[grind .]
theorem OpResultPtr.setType_fieldsIsRepr :
    ctx.IsRepr → (setType opOperand ctx newType h).IsRepr := by
  grind

@[grind .]
theorem OpResultPtr.setFirstUse_fieldsIsRepr_maybe  :
    ctx.IsRepr → (setFirstUse opOperand ctx newFirstUse h).IsRepr := by
  grind

@[grind .]
theorem RegionPtr.setParent_fieldsIsRepr :
    ctx.IsRepr → (setParent region ctx newParent h).IsRepr := by
  grind

@[grind .]
theorem RegionPtr.setFirstBlock_fieldsIsRepr :
    ctx.IsRepr → (setFirstBlock region ctx newFirstBlock h).IsRepr := by
  grind

@[grind .]
theorem RegionPtr.setLastBlock_fieldsIsRepr :
    ctx.IsRepr → (setLastBlock region ctx newLastBlock h).IsRepr := by
  grind

attribute [local grind] Region.empty in
@[grind .]
theorem RegionPtr.allocEmpty_fieldsIsRepr (heq : allocEmpty ctx = some (ctx', rg')) :
    rg'.IsRepr → ctx.IsRepr → ctx'.IsRepr := by
  grind

@[grind .]
theorem BlockOperandPtrPtr.set_fieldsIsRepr_maybe  (hnew : new.maybe BlockOperandPtr.IsRepr ctx) :
    ctx.IsRepr → (set blockOperandPtr ctx new h).IsRepr := by
  cases new <;> grind

@[grind .]
theorem ValuePtr.setType_fieldsIsRepr :
    ctx.IsRepr → (setType value ctx newType h).IsRepr := by
  cases value <;> simp only [setType_OpResultPtr, setType_BlockArgumentPtr] <;> grind

@[grind .]
theorem ValuePtr.setFirstUse_fieldsIsRepr_maybe :
    ctx.IsRepr → (setFirstUse value ctx newFirstUse h).IsRepr := by
  cases value <;> simp only [setFirstUse_OpResultPtr, setFirstUse_BlockArgumentPtr] <;> grind
