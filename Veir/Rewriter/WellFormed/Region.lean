module

public import Veir.IR.Basic
public import Veir.Rewriter.Basic

import Veir.IR.WellFormed
import Veir.Rewriter.GetSet

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}

theorem IRContext.wellFormed_Rewriter_createRegion (hctx : ctx.WellFormed) :
    Rewriter.createRegion ctx = some (newCtx, region) →
    newCtx.WellFormed := by
  intro h
  constructor
  · grind
  · intro value valueInBounds
    have ⟨array, harray⟩ :=  hctx.valueDefUseChains value (by grind)
    exists array
    apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind
  · intro block blockInBounds
    have ⟨array, harray⟩ :=  hctx.blockDefUseChains block (by grind)
    exists array
    apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind
  · intro block blockInBounds
    have ⟨array, harray⟩ := hctx.opChain block (by grind)
    exists array
    apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind
  · intro region' region'InBounds
    by_cases region = region'
    · exists #[]
      constructor <;> grind
    · have ⟨array, harray⟩ := hctx.blockChain region' (by grind)
      exists array
      apply RegionPtr.blockChain_unchanged (ctx := ctx) <;> grind
  · intro operation operationInBounds
    have := hctx.operations operation (by grind)
    apply OperationPtr.WellFormed_unchanged (ctx := ctx) <;> grind
  · intro block blockInBounds
    have := hctx.blocks block (by grind)
    apply BlockPtr.WellFormed_unchanged (ctx := ctx) <;> grind
  · intro region' region'InBounds
    by_cases region = region'
    · constructor <;> grind
    · have := hctx.regions region' (by grind)
      apply RegionPtr.WellFormed_unchanged (ctx := ctx) <;> grind

theorem BlockPtr.opChain_rewriter_createRegion
    (hWf : BlockPtr.OpChain block' ctx array)
    (h : Rewriter.createRegion ctx = some (newCtx, region)) :
    BlockPtr.OpChain block' newCtx array := by
  apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind

theorem BlockPtr.operationList_rewriter_createRegion
    (h : Rewriter.createRegion ctx = some (newCtx, region))
    (ctxWf : ctx.WellFormed) :
    BlockPtr.operationList block' newCtx newCtxWf blockInBounds' =
    BlockPtr.operationList block' ctx ctxWf (by grind) := by
  have := BlockPtr.opChain_rewriter_createRegion (block' := block')
    (array := block'.operationList ctx ctxWf (by grind))
    (by grind [BlockPtr.operationListWF]) h
  grind

grind_pattern BlockPtr.operationList_rewriter_createRegion =>
  Rewriter.createRegion ctx, some (newCtx, region), newCtx.WellFormed,
  block'.operationList newCtx newCtxWf blockInBounds'
