module

public import Veir.Rewriter.WfRewriter.Basic

import all Veir.Rewriter.WfRewriter.Basic

/-!
# `InBounds` theorems for `WfRewriter`

This file contains lemmas about how the `InBounds` property of pointers is preserved (or not)
by various operations of the `WfRewriter`. All of these lemmas are annotated by `grind`, and should
in principle never need to be manually invoked.
-/

public section
namespace Veir

variable {OpInfo} [HasOpInfo OpInfo]
variable {ctx ctx' : WfIRContext OpInfo}
variable {newOp operation : OperationPtr} {region : RegionPtr} {block blockPtr : BlockPtr}
variable {oldValue newValue : ValuePtr}
variable {ptr : GenericPtr}

/-! ## `WfRewriter.insertOp` -/

@[grind =>]
theorem WfRewriter.insertOp_inBounds_iff
    (heq : WfRewriter.insertOp ctx newOp ip h₁ h₂ = some ctx') :
    ptr.InBounds ctx'.raw ↔ ptr.InBounds ctx.raw := by
  grind [insertOp]

/-! ## `WfRewriter.detachOp` -/

@[simp, grind =]
theorem WfRewriter.detachOp_inBounds_iff :
    ptr.InBounds (WfRewriter.detachOp ctx op hIn hasParent).raw ↔ ptr.InBounds ctx.raw := by
  grind [detachOp]

/-! ## `WfRewriter.detachOpIfAttached` -/

@[simp, grind =]
theorem WfRewriter.detachOpIfAttached_inBounds_iff :
    ptr.InBounds (WfRewriter.detachOpIfAttached ctx op h).raw ↔ ptr.InBounds ctx.raw := by
  grind [detachOpIfAttached]

/-! ## `WfRewriter.insertBlock` -/

@[grind =>]
theorem WfRewriter.insertBlock_inBounds_iff
    (heq : WfRewriter.insertBlock ctx newBlock ip h₁ h₂ = some ctx') :
    ptr.InBounds ctx.raw ↔ ptr.InBounds ctx'.raw := by
  grind [insertBlock]

/-! ## `WfRewriter.replaceOperand` -/

@[simp, grind =]
theorem WfRewriter.replaceOperand_inBounds_iff :
    ptr.InBounds (WfRewriter.replaceOperand ctx use newValue h₁ h₂).raw ↔ ptr.InBounds ctx.raw := by
  grind [replaceOperand]

/-! ## `WfRewriter.replaceValue` -/

@[simp, grind =]
theorem WfRewriter.replaceValue_inBounds
    {ne : oldValue ≠ newValue} {oldIn : oldValue.InBounds ctx.raw}
    {newIn : newValue.InBounds ctx.raw} :
    ptr.InBounds (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw ↔
    ptr.InBounds ctx.raw := by
  fun_induction replaceValue
  grind [Id.run, pure]

/-! ## `WfRewriter.createBlock` -/

@[grind .]
theorem WfRewriter.createBlock_inBounds_mono
    (heq : WfRewriter.createBlock ctx types ip hip = some (ctx', newBlock)) :
    ptr.InBounds ctx.raw → ptr.InBounds ctx'.raw := by
  grind [createBlock]

/-! ## `WfRewriter.setBlockArguments` -/

@[simp, grind =]
theorem WfRewriter.setBlockArguments_inBounds_iff :
    ptr.InBounds (WfRewriter.setBlockArguments ctx blockPtr types hblock noUses).raw ↔
    match ptr with
    | .blockArgument argPtr
    | .value (.blockArgument argPtr)
    | .opOperandPtr (.valueFirstUse (.blockArgument argPtr)) =>
      if argPtr.block = blockPtr then argPtr.index < types.size else argPtr.InBounds ctx.raw
    | _ => ptr.InBounds ctx.raw := by
  grind [setBlockArguments]

/-! ## `WfRewriter.createRegion` -/

@[grind →]
theorem WfRewriter.createRegion_new_inBounds
    (heq : WfRewriter.createRegion ctx = some (ctx', reg)) :
    reg.InBounds ctx'.raw := by
  grind [createRegion]

@[grind →]
theorem WfRewriter.createRegion_new_not_inBounds
    (heq : WfRewriter.createRegion ctx = some (ctx', reg)) :
    ¬ reg.InBounds ctx.raw := by
  grind [WfRewriter.createRegion]

@[grind =>]
theorem WfRewriter.createRegion_genericPtr_mono
    (heq : WfRewriter.createRegion ctx = some (ctx', ptr')) :
    ptr.InBounds ctx'.raw ↔ (ptr.InBounds ctx.raw ∨ ptr = .region ptr') := by
  grind [WfRewriter.createRegion]

/-! ## `WfRewriter.pushRegion` -/

@[simp, grind =]
theorem WfRewriter.pushRegion_inBounds_iff :
    ptr.InBounds (WfRewriter.pushRegion ctx op region hop hregion hRegionParent).raw ↔
    ptr.InBounds ctx.raw := by
  grind [WfRewriter.pushRegion]

/-! ## `WfRewriter.pushResult` -/

@[grind .]
theorem WfRewriter.pushResult_inBounds_mono :
    ptr.InBounds ctx.raw → ptr.InBounds (WfRewriter.pushResult ctx op type hop).raw := by
  grind [WfRewriter.pushResult]

@[simp, grind =]
theorem WfRewriter.pushResult_inBounds_iff :
    ptr.InBounds (WfRewriter.pushResult ctx op type hop).raw ↔
    (ptr.InBounds ctx.raw ∨
      ptr = .opResult (op.nextResult ctx.raw) ∨
      ptr = .value (op.nextResult ctx.raw) ∨
      ptr = .opOperandPtr (.valueFirstUse (op.nextResult ctx.raw))) := by
  grind [WfRewriter.pushResult]

/-! ## `WfRewriter.pushOperand` -/

@[simp, grind =]
theorem WfRewriter.pushOperand_inBounds_iff :
    ptr.InBounds (WfRewriter.pushOperand ctx opPtr valuePtr h₁ h₂).raw ↔
    (ptr.InBounds ctx.raw ∨
     ptr = .opOperand (opPtr.nextOperand ctx.raw) ∨
     ptr = .opOperandPtr (.operandNextUse (opPtr.nextOperand ctx.raw))) := by
  grind [WfRewriter.pushOperand]

@[grind .]
theorem WfRewriter.pushOperand_inBounds_mono :
    ptr.InBounds ctx.raw → ptr.InBounds (WfRewriter.pushOperand ctx opPtr valuePtr h₁ h₂).raw := by
  grind [WfRewriter.pushOperand]

/-! ## `WfRewriter.pushBlockOperand` -/

@[simp, grind =]
theorem WfRewriter.pushBlockOperand_inBounds_iff :
    ptr.InBounds (WfRewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂).raw ↔
    (ptr.InBounds ctx.raw ∨
      ptr = .blockOperand (opPtr.nextBlockOperand ctx.raw) ∨
      ptr = .blockOperandPtr (.blockOperandNextUse (opPtr.nextBlockOperand ctx.raw))) := by
  grind [WfRewriter.pushBlockOperand]

@[grind .]
theorem WfRewriter.pushBlockOperand_inBounds_mono :
    ptr.InBounds ctx.raw → ptr.InBounds (WfRewriter.pushBlockOperand ctx opPtr blockPtr h₁ h₂).raw := by
  grind [WfRewriter.pushBlockOperand]

/-! ## `WfRewriter.createOp` -/

@[grind →]
theorem WfRewriter.createOp_new_inBounds (ptr : OperationPtr)
    (heq : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', ptr)) :
    ptr.InBounds ctx'.raw := by
  grind [WfRewriter.createOp]

@[grind →]
theorem WfRewriter.createOp_new_not_inBounds (ptr : OperationPtr)
    (heq : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', ptr)) :
    ¬ ptr.InBounds ctx.raw := by
  grind [WfRewriter.createOp]

@[grind .]
theorem WfRewriter.createOp_inBounds_mono
    (heq : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (ctx', newOp)) :
    ptr.InBounds ctx.raw → ptr.InBounds ctx'.raw := by
  grind [WfRewriter.createOp]

/-! ## `WfIRContext.create` -/

@[grind →]
theorem WfIRContext.create_new_inBounds
    (heq : WfIRContext.create OpInfo = some (ctx', op)) :
    op.InBounds ctx'.raw := by
  grind [WfIRContext.create]

end Veir
