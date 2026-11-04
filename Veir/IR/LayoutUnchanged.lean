module

public import Veir.IR.Basic
public import Veir.IR.InBounds
import Veir.ForLean
import Veir.IR.GetSet
import Veir.Prelude

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-! ## Predicates stating that the layout of objects has not changed. -/

@[local grind]
structure OperationPtr.LayoutPreserved (op : OperationPtr) (ctx₁ ctx₂ : IRContext OpInfo) where
  numResults : (op.get! ctx₁).capResults = (op.get! ctx₂).capResults
  opCode : op.getOpType! ctx₁ = op.getOpType! ctx₂
  numOperands : (op.get! ctx₁).capOperands = (op.get! ctx₂).capOperands
  numSuccessors : (op.get! ctx₁).capBlockOperands = (op.get! ctx₂).capBlockOperands
  numRegions : (op.get! ctx₁).capRegions = (op.get! ctx₂).capRegions

@[expose, local grind]
def BlockPtr.LayoutPreserved (block : Veir.BlockPtr) (ctx₁ ctx₂ : IRContext OpInfo) :=
  (block.get! ctx₁).capArguments = (block.get! ctx₂).capArguments

@[local grind]
structure IRContext.LayoutPreserved (ctx₁ ctx₂ : Veir.IRContext OpInfo) where
  ops (op : Veir.OperationPtr) (ib : op.InBounds ctx₁) : op.LayoutPreserved ctx₁ ctx₂
  blocks (block : Veir.BlockPtr) (ib : block.InBounds ctx₁) : block.LayoutPreserved ctx₁ ctx₂

@[local grind]
structure IRContext.LayoutUnchanged (ctx₁ ctx₂ : Veir.IRContext OpInfo) where
  preserves : ctx₁.LayoutPreserved ctx₂
  creates : ctx₂.LayoutPreserved ctx₁

@[grind .]
theorem IRContext.LayoutPreserved.of_layoutUnchanged_ltr {ctx₁ ctx₂ : Veir.IRContext OpInfo} :
    ctx₁.LayoutUnchanged ctx₂ → ctx₁.LayoutPreserved ctx₂ := by
  grind

@[grind .]
theorem IRContext.LayoutUnchanged.symm {ctx₁ ctx₂ : Veir.IRContext OpInfo} :
    ctx₁.LayoutUnchanged ctx₂ ↔ ctx₂.LayoutUnchanged ctx₁ := by
  grind

@[grind .]
theorem IRContext.LayoutPreserved.of_layoutUnchanged_rtl {ctx₁ ctx₂ : Veir.IRContext OpInfo} :
    ctx₁.LayoutUnchanged ctx₂ → ctx₂.LayoutPreserved ctx₁ := by
  grind

theorem IRContext.LayoutPreserved.trans (ctx₂ : Veir.IRContext OpInfo) (ib : ∀ (ptr : GenericPtr), ptr.InBounds ctx₁ → ptr.InBounds ctx₂) :
    ctx₁.LayoutPreserved ctx₂ → ctx₂.LayoutPreserved ctx₃ → ctx₁.LayoutPreserved ctx₃ := by
  grind

theorem IRContext.LayoutUnchanged.trans (ctx₂ : Veir.IRContext OpInfo)
    (ib : ∀ (ptr : GenericPtr), ptr.InBounds ctx₁ ↔ ptr.InBounds ctx₂)
    (ib' : ∀ (ptr : GenericPtr), ptr.InBounds ctx₂ ↔ ptr.InBounds ctx₃) :
    ctx₁.LayoutUnchanged ctx₂ → ctx₂.LayoutUnchanged ctx₃ → ctx₁.LayoutUnchanged ctx₃ := by
  grind

variable {ctx : IRContext OpInfo}

/-! Basic functions preserve layouts. -/

section operation

variable {op : OperationPtr} (h : op.InBounds ctx)

@[grind .]
theorem OperationPtr.setNextOp_preservesLayout :
    ctx.LayoutUnchanged (setNextOp op ctx newNext? h) := by
  grind

@[grind .]
theorem OperationPtr.setPrevOp_preservesLayout :
    ctx.LayoutUnchanged (setPrevOp op ctx newNext? h) := by
  grind

@[grind .]
theorem OperationPtr.setParent_preservesLayout :
    ctx.LayoutUnchanged (setParent op ctx newNext? h) := by
  grind

@[grind .]
theorem OperationPtr.setAttributes_preservesLayout :
    ctx.LayoutUnchanged (op.setAttributes ctx newAttrs h) := by
  grind

@[grind .]
theorem OperationPtr.pushBlockOperand_preservesLayout :
    ctx.LayoutUnchanged (op.pushBlockOperand ctx bo h) := by
  grind

@[grind .]
theorem OperationPtr.pushOperand_preservesLayout :
    ctx.LayoutUnchanged (op.pushOperand ctx oper h) := by
  grind

@[grind .]
theorem OperationPtr.pushResult_preservesLayout :
    ctx.LayoutUnchanged (op.pushResult ctx result h) := by
  grind

@[grind .]
theorem OperationPtr.pushRegion_preservesLayout :
    ctx.LayoutUnchanged (op.pushRegion ctx region h) := by
  grind

@[grind .]
theorem OperationPtr.allocEmptyAt_preservesLayout
    (heq : OperationPtr.allocEmptyAt ctx ty properties capResults capBlockOperands capRegions capOperands addr = some (ctx', op')) :
    ctx.LayoutPreserved ctx' := by
  grind [Std.HashMap.mem_iff_contains]

@[grind .]
theorem OperationPtr.allocEmpty_preservesLayout
    (heq : OperationPtr.allocEmpty ctx ty properties capResults capBlockOperands capRegions capOperands = some (ctx', op')) :
    ctx.LayoutPreserved ctx' := by
  grind

end operation

/- OpOperandPtr -/

section opoperand

attribute [local grind] OpOperandPtr.setNextUse OpOperandPtr.setBack OpOperandPtr.setOwner OpOperandPtr.setValue

variable {opOperand : OpOperandPtr} (h : opOperand.InBounds ctx)

@[grind .]
theorem OpOperandPtr.setNextUse_preservesLayout {ctx : IRContext OpInfo}
    (h : opOperand.InBounds ctx) :
    ctx.LayoutUnchanged (setNextUse opOperand ctx newNextuse h) := by
  grind

@[grind .]
theorem OpOperandPtr.setBack_preservesLayout {ctx : IRContext OpInfo}
    (h : opOperand.InBounds ctx) :
    ctx.LayoutUnchanged (setBack opOperand ctx newNextuse h) := by
  grind

@[grind .]
theorem OpOperandPtr.setOwner_preservesLayout {ctx : IRContext OpInfo}
    (h : opOperand.InBounds ctx) :
    ctx.LayoutUnchanged (setOwner opOperand ctx newNextuse h) := by
  grind

@[grind .]
theorem OpOperandPtr.setValue_preservesLayout {ctx : IRContext OpInfo}
    (h : opOperand.InBounds ctx) :
    ctx.LayoutUnchanged (setValue opOperand ctx newNextuse h) := by
  grind

end opoperand

section opresult

attribute [local grind] OpResultPtr.setType OpResultPtr.setFirstUse OpResultPtr.setOwner

variable {opRes : OpResultPtr} (h : opRes.InBounds ctx)

@[grind .]
theorem OpResultPtr.setType_preservesLayout {ctx : IRContext OpInfo}
    (h : opRes.InBounds ctx) :
    ctx.LayoutUnchanged (setType opRes ctx newNextuse h) := by
  grind

@[grind .]
theorem OpResultPtr.setFirstUse_preservesLayout {ctx : IRContext OpInfo}
    (h : opRes.InBounds ctx) :
    ctx.LayoutUnchanged (setFirstUse opRes ctx newNextuse h) := by
  grind

@[grind .]
theorem OpResultPtr.setOwner_preservesLayout  :
    ctx.LayoutUnchanged (setOwner opRes ctx newNextuse h) := by
  grind

end opresult

section blockargument

variable {ba : BlockArgumentPtr}

@[grind .]
theorem BlockArgumentPtr.setType_preservesLayout {ctx : IRContext OpInfo}
    (h : blockArgPtr.InBounds ctx) :
    ctx.LayoutUnchanged (setType blockArgPtr ctx newType h) := by
  grind

@[grind .]
theorem BlockArgumentPtr.setFirstUse_preservesLayout {ctx : IRContext OpInfo}
    (h : blockArgPtr.InBounds ctx) :
    ctx.LayoutUnchanged (setFirstUse blockArgPtr ctx newFirstUse h) := by
  grind

@[grind .]
theorem BlockArgumentPtr.setLoc_preservesLayout {ctx : IRContext OpInfo}
    (h : blockArgPtr.InBounds ctx) :
    ctx.LayoutUnchanged (setLoc blockArgPtr ctx newLoc h) := by
  grind

@[grind .]
theorem BlockArgumentPtr.setIndex_preservesLayout {ctx : IRContext OpInfo}
    (h : blockArgPtr.InBounds ctx) :
    ctx.LayoutUnchanged (setIndex blockArgPtr ctx newIndex h) := by
  grind

@[grind .]
theorem BlockArgumentPtr.setOwner_preservesLayout {ctx : IRContext OpInfo}
    (h : blockArgPtr.InBounds ctx) :
    ctx.LayoutUnchanged (setOwner blockArgPtr ctx newOwner h) := by
  grind

end blockargument

section value

attribute [local grind] ValuePtr.setFirstUse ValuePtr.setType

variable {value : ValuePtr} (h : value.InBounds ctx)

@[grind .]
theorem ValuePtr.setType_preservesLayout {ctx : IRContext OpInfo}
    (h : value.InBounds ctx) :
    ctx.LayoutUnchanged (setType value ctx newNextuse h) := by
  grind


@[grind .]
theorem ValuePtr.setFirstUse_preservesLayout {ctx : IRContext OpInfo}
    (h : value.InBounds ctx) :
    ctx.LayoutUnchanged (setFirstUse value ctx newNextuse h) := by
  grind

end value

section block

variable {block : BlockPtr} (h : block.InBounds ctx)

@[grind .]
theorem BlockPtr.setParent_preservesLayout {ctx : IRContext OpInfo}
    (h : block.InBounds ctx) :
    ctx.LayoutUnchanged (setParent block ctx newParent h) := by
  grind

@[grind .]
theorem BlockPtr.setFirstUse_preservesLayout {ctx : IRContext OpInfo}
    (h : block.InBounds ctx) :
    ctx.LayoutUnchanged (setFirstUse block ctx newFirstUse h) := by
  grind

@[grind .]
theorem BlockPtr.setFirstOp_preservesLayout {ctx : IRContext OpInfo}
    (h : block.InBounds ctx) :
    ctx.LayoutUnchanged (setFirstOp block ctx newFirstOp h) := by
  grind

@[grind .]
theorem BlockPtr.setLastOp_preservesLayout {ctx : IRContext OpInfo}
    (h : block.InBounds ctx) :
    ctx.LayoutUnchanged (setLastOp block ctx newLastOp h) := by
  grind

@[grind .]
theorem BlockPtr.setNextBlock_preservesLayout {ctx : IRContext OpInfo}
    (h : block.InBounds ctx) :
    ctx.LayoutUnchanged (setNextBlock block ctx newNextBlock h) := by
  grind

@[grind .]
theorem BlockPtr.setPrevBlock_preservesLayout {ctx : IRContext OpInfo}
    (h : block.InBounds ctx) :
    ctx.LayoutUnchanged (setPrevBlock block ctx newPrevBlock h) := by
  grind

@[grind .]
theorem BlockPtr.pushBlockArgument_preservesLayout :
    ctx.LayoutUnchanged (block.pushArgument ctx region h) := by
  grind

@[grind .]
theorem BlockPtr.allocEmptyAtAddress_preservesLayout
    (heq : allocEmptyAtAddress ctx capArguments address = some (ctx', ptr')) :
    ctx.LayoutPreserved ctx' := by
  grind [Std.HashMap.mem_iff_contains]

@[grind .]
theorem BlockPtr.allocEmpty_preservesLayout (heq : allocEmpty ctx capArguments = some (ctx', ptr')) :
    ctx.LayoutPreserved ctx' := by
  grind
end block

section region

variable {region : RegionPtr} (h : region.InBounds ctx)

@[grind .]
theorem RegionPtr.setParent_preservesLayout {ctx : IRContext OpInfo}
    (h : region.InBounds ctx) :
    ctx.LayoutUnchanged (setParent region ctx newParent h) := by
  grind

@[grind .]
theorem RegionPtr.setFirstBlock_preservesLayout {ctx : IRContext OpInfo}
    (h : region.InBounds ctx) :
    ctx.LayoutUnchanged (setFirstBlock region ctx newFirstBlock h) := by
  grind

@[grind .]
theorem RegionPtr.setLastBlock_preservesLayout {ctx : IRContext OpInfo}
    (h : region.InBounds ctx) :
    ctx.LayoutUnchanged (setLastBlock region ctx newLastBlock h) := by
  grind

@[grind .]
theorem RegionPtr.allocEmptyAt_preservesLayout (heq : allocEmptyAt ctx addr = some (ctx', ptr')) :
    ctx.LayoutUnchanged ctx' := by
  grind

@[grind .]
theorem RegionPtr.allocEmpty_preservesLayout (heq : allocEmpty ctx = some (ctx', ptr')) :
    ctx.LayoutUnchanged ctx' := by
  grind

end region

section operandptr

variable {opOperandPtr : OpOperandPtrPtr} (h : opOperandPtr.InBounds ctx)

/- OpOperandPtrPtr.set -/

@[grind .]
theorem OpOperandPtrPtr.set_preservesLayout {ctx : IRContext OpInfo}
    (h : opOperandPtr.InBounds ctx) :
    ctx.LayoutUnchanged (set opOperandPtr ctx newPtr h) := by
  grind

end operandptr

section blockoperand

variable {blockOperand : BlockOperandPtr} (h : blockOperand.InBounds ctx)

@[grind .]
theorem BlockOperandPtr.setNextUse_preservesLayout {ctx : IRContext OpInfo}
    (h : blockOperand.InBounds ctx) :
    ctx.LayoutUnchanged (setNextUse blockOperand ctx newNextuse h) := by
  grind

@[grind .]
theorem BlockOperandPtr.setBack_preservesLayout {ctx : IRContext OpInfo}
    (h : blockOperand.InBounds ctx) :
    ctx.LayoutUnchanged (setBack blockOperand ctx newNextuse h) := by
  grind

@[grind .]
theorem BlockOperandPtr.setOwner_preservesLayout {ctx : IRContext OpInfo}
    (h : blockOperand.InBounds ctx) :
    ctx.LayoutUnchanged (setOwner blockOperand ctx newNextuse h) := by
  grind

@[grind .]
theorem BlockOperandPtr.setValue_preservesLayout {ctx : IRContext OpInfo}
    (h : blockOperand.InBounds ctx) :
    ctx.LayoutUnchanged (setValue blockOperand ctx newNextuse h) := by
  grind

end blockoperand

section blockOperandPtr

variable {blockOperandPtr : BlockOperandPtrPtr} (h : blockOperandPtr.InBounds ctx)

@[grind .]
theorem BlockOperandPtrPtr.set_preservesLayout :
    ctx.LayoutUnchanged (set blockOperandPtr ctx newPtr h) := by
  grind

end blockOperandPtr
