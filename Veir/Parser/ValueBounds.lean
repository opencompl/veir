module

public import Veir.Rewriter.WfRewriter

import all Veir.IR.Basic
import all Veir.Rewriter.Basic
import all Veir.Rewriter.WfRewriter.Basic

/-!
Bounds transport for the values retained by the parser.  Creating and linking IR objects
preserves existing values.  Replacing empty block arguments also preserves them, while
erasing an operation requires excluding its results.
-/

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx' : WfIRContext OpInfo} {value : ValuePtr}

@[grind .]
theorem WfRewriter.createBlock_valueInBounds_mono
    (heq : WfRewriter.createBlock ctx types ip hip = some (ctx', newBlock)) :
    value.InBounds ctx.raw → value.InBounds ctx'.raw := by
  exact WfRewriter.createBlock_inBounds_mono (ptr := .value value) heq

@[grind .]
theorem WfRewriter.createRegion_valueInBounds_mono
    (heq : WfRewriter.createRegion ctx = some (ctx', newRegion)) :
    value.InBounds ctx.raw → value.InBounds ctx'.raw := by
  intro h
  exact (WfRewriter.createRegion_genericPtr_mono (ptr := .value value) heq).mpr (.inl h)

@[grind .]
theorem WfRewriter.insertOp_valueInBounds_mono
    (heq : WfRewriter.insertOp ctx newOp ip hop hip = some ctx') :
    value.InBounds ctx.raw → value.InBounds ctx'.raw := by
  exact (WfRewriter.insertOp_inBounds_iff (ptr := .value value) heq).mpr

@[grind .]
theorem WfRewriter.insertBlock_valueInBounds_mono
    (heq : WfRewriter.insertBlock ctx newBlock ip hblock hip = some ctx') :
    value.InBounds ctx.raw → value.InBounds ctx'.raw := by
  exact (WfRewriter.insertBlock_inBounds_iff (ptr := .value value) heq).mp

@[simp, grind =]
theorem WfRewriter.setAttributes_valueInBounds_iff :
    value.InBounds (WfRewriter.setAttributes ctx op attrs hop).raw ↔
    value.InBounds ctx.raw := by
  exact Rewriter.setAttributes_inBounds (ctx := ctx.raw) (op := op)
    (newAttrs := attrs) (opIn := hop) (.value value)

@[grind .]
theorem WfRewriter.setBlockArguments_valueInBounds_mono
    (empty : block.getNumArguments! ctx.raw = 0) :
    value.InBounds ctx.raw →
    value.InBounds (WfRewriter.setBlockArguments ctx block types hblock noUses).raw := by
  intro hvalue
  have hbounds := WfRewriter.setBlockArguments_inBounds_iff
    (ptr := .value value) (ctx := ctx) (blockPtr := block) (types := types)
    (hblock := hblock) (noUses := noUses)
  cases value with
  | opResult result => exact hbounds.mpr hvalue
  | blockArgument arg =>
    apply hbounds.mpr
    simp only
    split
    · grind [BlockArgumentPtr.inBounds_def,
        BlockPtr.getNumArguments!_eq_getNumArguments]
    · exact (ValuePtr.inBounds_blockArg _ _).mp hvalue

@[grind .]
theorem WfRewriter.eraseOp_valueInBounds_iff
    (other : match value with
      | .blockArgument _ => True
      | .opResult result => result.op ≠ op) :
    value.InBounds (WfRewriter.eraseOp ctx op opRegions opUses hop).raw ↔
    value.InBounds ctx.raw := by
  apply Rewriter.eraseOp_inBounds (.value value)
  cases value <;> exact other

section createOp

variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
variable {opType : Dialect} {properties : propertiesOf opType}

@[grind .]
theorem WfRewriter.createOp_valueInBounds_mono
    (heq : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      ip hoper hblocks hregions hip = some (ctx', newOp)) :
    value.InBounds ctx.raw → value.InBounds ctx'.raw := by
  exact WfRewriter.createOp_inBounds_mono (ptr := .value value) heq

@[grind →]
theorem WfRewriter.createOp_existingValue_not_result
    (heq : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      ip hoper hblocks hregions hip = some (ctx', newOp))
    (hvalue : value.InBounds ctx.raw) :
    match value with
    | .blockArgument _ => True
    | .opResult result => result.op ≠ newOp := by
  have hfresh := WfRewriter.createOp_new_not_inBounds newOp heq
  cases value with
  | blockArgument _ => trivial
  | opResult result => grind [OpResultPtr.inBounds_def]

@[grind .]
theorem WfRewriter.createOp_result_inBounds
    (heq : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      ip hoper hblocks hregions hip = some (ctx', newOp))
    (i : Nat) (hi : i < resultTypes.size) :
    (newOp.getResult i).InBounds ctx'.raw := by
  have hop := WfRewriter.createOp_new_inBounds newOp heq
  have hcount := OperationPtr.getNumResults!_WfRewriter_createOp
    (operation := newOp) heq
  apply OpResultPtr.inBounds_of
  · exact hop
  · simpa only [OperationPtr.getResult, hcount, ite_eq_left] using hi

end createOp
end Veir
