import Veir.IR.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.GetSetInBounds

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
    apply Operation.WellFormed_unchanged (ctx := ctx) <;> grind
  · intro block blockInBounds
    have := hctx.blocks block (by grind)
    apply Block.WellFormed_unchanged (ctx := ctx) <;> grind
  · intro region' region'InBounds
    by_cases region = region'
    · constructor <;> grind
    · have := hctx.regions region' (by grind)
      apply Region.WellFormed_unchanged (ctx := ctx) <;> grind
