module

public import Veir.Rewriter.WfRewriter

import all Veir.IR.Basic
import all Veir.Rewriter.Basic
import all Veir.Rewriter.WfRewriter.Basic

public section
namespace Veir.Parser

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- Context mutations preserve the blocks and regions retained by the parser. -/
structure StructuralBoundsPreserved (ctx ctx' : IRContext OpInfo) : Prop where
  blocks : ∀ (block : BlockPtr), block.InBounds ctx → block.InBounds ctx'
  regions : ∀ (region : RegionPtr), region.InBounds ctx → region.InBounds ctx'

namespace StructuralBoundsPreserved

theorem refl (ctx : IRContext OpInfo) : StructuralBoundsPreserved ctx ctx :=
  ⟨fun _ h => h, fun _ h => h⟩

theorem trans {ctx ctx' ctx'' : IRContext OpInfo}
    (h : StructuralBoundsPreserved ctx ctx') (h' : StructuralBoundsPreserved ctx' ctx'') :
    StructuralBoundsPreserved ctx ctx'' :=
  ⟨fun block hb => h'.blocks block (h.blocks block hb),
    fun region hr => h'.regions region (h.regions region hr)⟩

/-- Generic pointer preservation includes structural pointers. -/
theorem ofGeneric {ctx ctx' : IRContext OpInfo}
    (h : ∀ ptr : GenericPtr, ptr.InBounds ctx → ptr.InBounds ctx') :
    StructuralBoundsPreserved ctx ctx' :=
  ⟨fun block hb => h (.block block) hb, fun region hr => h (.region region) hr⟩

end StructuralBoundsPreserved
end Veir.Parser

namespace Veir
open _root_.Veir.Parser

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx' : WfIRContext OpInfo}

@[grind .]
theorem BlockInsertPoint.inBounds_of_structuralBoundsPreserved
    {raw raw' : IRContext OpInfo} (h : StructuralBoundsPreserved raw raw')
    {ip : BlockInsertPoint} (hip : ip.InBounds raw) : ip.InBounds raw' := by
  cases ip with
  | before block =>
    simp only [BlockInsertPoint.inBounds_before] at hip ⊢
    exact h.blocks block hip
  | atEnd region =>
    simp only [BlockInsertPoint.inBounds_atEnd] at hip ⊢
    exact h.regions region hip

@[grind .]
theorem OperationPtr.inBounds_of_result_value_inBounds
    {raw : IRContext OpInfo} {op : OperationPtr} {index : Nat}
    (h : (ValuePtr.opResult (op.getResult index)).InBounds raw) : op.InBounds raw := by
  grind

@[grind →]
theorem WfRewriter.createBlock_structuralBoundsPreserved
    (h : WfRewriter.createBlock ctx types ip hip = some (ctx', newBlock)) :
    StructuralBoundsPreserved ctx.raw ctx'.raw :=
  StructuralBoundsPreserved.ofGeneric fun _ => WfRewriter.createBlock_inBounds_mono h

@[grind →]
theorem WfRewriter.createBlock_new_inBounds
    (h : WfRewriter.createBlock ctx types ip hip = some (ctx', newBlock)) :
    newBlock.InBounds ctx'.raw := by
  grind [WfRewriter.createBlock]

@[grind →]
theorem WfRewriter.insertBlock_structuralBoundsPreserved
    (h : WfRewriter.insertBlock ctx block ip hblock hip = some ctx') :
    StructuralBoundsPreserved ctx.raw ctx'.raw :=
  StructuralBoundsPreserved.ofGeneric fun _ => (WfRewriter.insertBlock_inBounds_iff h).mp

@[grind →]
theorem WfRewriter.insertOp_structuralBoundsPreserved
    (h : WfRewriter.insertOp ctx op ip hop hip = some ctx') :
    StructuralBoundsPreserved ctx.raw ctx'.raw :=
  StructuralBoundsPreserved.ofGeneric fun _ => (WfRewriter.insertOp_inBounds_iff h).mpr

@[grind →]
theorem WfRewriter.createRegion_structuralBoundsPreserved
    (h : WfRewriter.createRegion ctx = some (ctx', newRegion)) :
    StructuralBoundsPreserved ctx.raw ctx'.raw :=
  StructuralBoundsPreserved.ofGeneric fun _ hb =>
    (WfRewriter.createRegion_genericPtr_mono h).mpr (.inl hb)

@[grind .]
theorem WfRewriter.setAttributes_structuralBoundsPreserved :
    StructuralBoundsPreserved ctx.raw (WfRewriter.setAttributes ctx op attrs hop).raw := by
  apply StructuralBoundsPreserved.ofGeneric
  intro ptr hp
  exact (Rewriter.setAttributes_inBounds (ctx := ctx.raw) (op := op)
    (newAttrs := attrs) (opIn := hop) ptr).mpr hp

@[grind .]
theorem WfRewriter.setBlockArguments_structuralBoundsPreserved :
    StructuralBoundsPreserved ctx.raw
      (WfRewriter.setBlockArguments ctx block types hblock noUses).raw := by
  constructor
  · intro ptr hp
    exact (WfRewriter.setBlockArguments_inBounds_iff (ptr := .block ptr)).mpr hp
  · intro ptr hp
    exact (WfRewriter.setBlockArguments_inBounds_iff (ptr := .region ptr)).mpr hp

@[grind .]
theorem WfRewriter.replaceValue_structuralBoundsPreserved :
    StructuralBoundsPreserved ctx.raw
      (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw :=
  StructuralBoundsPreserved.ofGeneric fun _ => WfRewriter.replaceValue_inBounds.mpr

@[grind .]
theorem WfRewriter.eraseOp_structuralBoundsPreserved :
    StructuralBoundsPreserved ctx.raw (WfRewriter.eraseOp ctx op noRegions noUses hop).raw := by
  constructor
  · intro ptr hp
    exact (Rewriter.eraseOp_inBounds (ctx := ctx.raw) (op := op) (hCtx := ctx.wellFormed.inBounds)
      (hOp := hop) (.block ptr) trivial).mpr hp
  · intro ptr hp
    exact (Rewriter.eraseOp_inBounds (ctx := ctx.raw) (op := op) (hCtx := ctx.wellFormed.inBounds)
      (hOp := hop) (.region ptr) trivial).mpr hp

@[grind .]
theorem WfRewriter.pushRegion_structuralBoundsPreserved :
    StructuralBoundsPreserved ctx.raw
      (WfRewriter.pushRegion ctx op region hop hregion hparent).raw :=
  StructuralBoundsPreserved.ofGeneric fun _ => WfRewriter.pushRegion_inBounds_iff.mpr

section createOp
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
variable {opType : Dialect} {properties : propertiesOf opType}

@[grind →]
theorem WfRewriter.createOp_structuralBoundsPreserved
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      ip hoper hblocks hregions hip = some (ctx', newOp)) :
    StructuralBoundsPreserved ctx.raw ctx'.raw :=
  StructuralBoundsPreserved.ofGeneric fun _ => WfRewriter.createOp_inBounds_mono h
end createOp

section raw
variable {raw raw' : IRContext OpInfo}

@[grind →]
theorem Rewriter.createBlock_structuralBoundsPreserved
    (h : Rewriter.createBlock raw types ip hctx hip = some (raw', newBlock)) :
    StructuralBoundsPreserved raw raw' :=
  StructuralBoundsPreserved.ofGeneric fun ptr => Rewriter.createBlock_inBounds_mono ptr h

@[grind →]
theorem Rewriter.createBlock_new_inBounds
    (h : Rewriter.createBlock raw types ip hctx hip = some (raw', newBlock)) :
    newBlock.InBounds raw' := by
  have hb := Rewriter.createBlock_inBounds (.block newBlock) h
  exact hb.mpr (.inr (.inl rfl))

@[grind →]
theorem Rewriter.insertBlock_structuralBoundsPreserved
    (h : Rewriter.insertBlock raw block ip hblock hip hctx = some raw') :
    StructuralBoundsPreserved raw raw' :=
  StructuralBoundsPreserved.ofGeneric fun ptr => (Rewriter.insertBlock_inBounds ptr h).mp

@[grind →]
theorem Rewriter.insertOp_structuralBoundsPreserved
    (h : Rewriter.insertOp raw op ip hop hip hctx = some raw') :
    StructuralBoundsPreserved raw raw' :=
  StructuralBoundsPreserved.ofGeneric fun ptr => (Rewriter.insertOp_inBounds_mono ptr h).mpr

@[grind →]
theorem Rewriter.createRegion_structuralBoundsPreserved
    (h : Rewriter.createRegion raw = some (raw', region)) :
    StructuralBoundsPreserved raw raw' :=
  StructuralBoundsPreserved.ofGeneric fun ptr hp =>
    (Rewriter.createRegion_genericPtr_mono ptr h).mpr (.inl hp)

@[grind .]
theorem Rewriter.setAttributes_structuralBoundsPreserved :
    StructuralBoundsPreserved raw (Rewriter.setAttributes raw op attrs hop) :=
  StructuralBoundsPreserved.ofGeneric fun ptr => (Rewriter.setAttributes_inBounds ptr).mpr

@[grind .]
theorem Rewriter.setBlockArguments_structuralBoundsPreserved :
    StructuralBoundsPreserved raw (Rewriter.setBlockArguments raw block types hblock) := by
  constructor
  · intro ptr hp
    exact (Rewriter.setBlockArguments_inBounds (.block ptr)).mpr hp
  · intro ptr hp
    exact (Rewriter.setBlockArguments_inBounds (.region ptr)).mpr hp

@[grind →]
theorem Rewriter.replaceValue?_structuralBoundsPreserved
    (h : Rewriter.replaceValue? raw oldValue newValue oldIn newIn hctx depth = some raw') :
    StructuralBoundsPreserved raw raw' :=
  StructuralBoundsPreserved.ofGeneric fun ptr => (Rewriter.replaceValue?_inBounds ptr h).mp

@[grind .]
theorem Rewriter.eraseOp_structuralBoundsPreserved :
    StructuralBoundsPreserved raw (Rewriter.eraseOp raw op hctx hop) := by
  constructor
  · intro ptr hp
    exact (Rewriter.eraseOp_inBounds (.block ptr) trivial).mpr hp
  · intro ptr hp
    exact (Rewriter.eraseOp_inBounds (.region ptr) trivial).mpr hp

section createOp
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
variable {opType : Dialect} {properties : propertiesOf opType}

@[grind →]
theorem Rewriter.createOp_structuralBoundsPreserved
    (h : Rewriter.createOp raw opType resultTypes operands blockOperands regions properties
      ip hoper hblocks hregions hip hctx = some (raw', newOp)) :
    StructuralBoundsPreserved raw raw' :=
  StructuralBoundsPreserved.ofGeneric fun ptr => Rewriter.createOp_inBounds_mono ptr h
end createOp
end raw
end Veir
