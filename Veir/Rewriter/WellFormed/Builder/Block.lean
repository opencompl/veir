import Veir.IR.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.GetSetInBounds

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}

theorem allocEmpty_wellFormed (hctx : ctx.WellFormed)
    (heq : BlockPtr.allocEmpty ctx = some (newCtx, bl)) :
    newCtx.WellFormed := by
  constructor
  case inBounds =>
    exact BlockPtr.allocEmpty_fieldsInBounds heq hctx.inBounds
  case valueDefUseChains =>
    intro value valueInBounds
    have ⟨array, harray⟩ := hctx.valueDefUseChains value (by grind)
    exists array
    apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind
  case blockDefUseChains =>
    intro block blockInBounds
    by_cases block = bl
    · exists #[]
      constructor <;> grind [Block.empty]
    · have ⟨array, harray⟩ := hctx.blockDefUseChains block (by grind)
      exists array
      apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind
  case opChain =>
    intro block blockInBounds
    by_cases block = bl
    · exists #[]
      constructor <;> grind [Block.empty]
    · have ⟨array, harray⟩ := hctx.opChain block (by grind)
      exists array
      apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind
  case blockChain =>
    intro region regionInBounds
    have ⟨array, harray⟩ := hctx.blockChain region (by grind)
    exists array
    apply RegionPtr.blockChain_unchanged (ctx := ctx) <;> grind [Block.empty]
  case operations =>
    intro operation operationInBounds
    have := hctx.operations operation (by grind)
    apply Operation.WellFormed_unchanged (ctx := ctx) <;> grind
  case blocks =>
    intro block blockInBounds
    by_cases bl = block
    · constructor <;> grind [Block.empty]
    · have := hctx.blocks block (by grind)
      apply Block.WellFormed_unchanged (ctx := ctx) <;> grind
  case regions =>
    intro region regionInBounds
    have := hctx.regions region (by grind)
    apply Region.WellFormed_unchanged (ctx := ctx) <;> grind
