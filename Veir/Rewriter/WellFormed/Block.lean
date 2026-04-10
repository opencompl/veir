import Veir.IR.WellFormed
import Veir.Rewriter.Basic
import Veir.Rewriter.GetSetInBounds
import Veir.Rewriter.InsertPoint
import Veir.Rewriter.LinkedList.WellFormed

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}

/-- # Rewriter.insertBlock? -/

theorem Rewriter.insertBlock?_WellFormed (hctx : ctx.WellFormed) :
    Rewriter.insertBlock? ctx newOp ip newOpIn insIn ctxInBounds = some newCtx →
    newCtx.WellFormed := by
  simp only [Rewriter.insertBlock?]
  split; grind; rename_i parent hparent
  intro h
  apply IRContext.wellFormed_BlockPtr_linkBetweenWithParent hctx h (ip := ip) <;>
    grind [Option.maybe₁]

theorem BlockPtr.allocEmpty_wellFormed (hctx : ctx.WellFormed)
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

theorem Rewriter.createBlock_WellFormed (ctxWf : ctx.WellFormed) :
    Rewriter.createBlock ctx ip hctx hip = some (newCtx, newBlock) →
    newCtx.WellFormed := by
  simp only [Rewriter.createBlock]
  split; grind; rename_i ctx₁ newBlock hctx₁
  have : ctx₁.WellFormed := by grind [BlockPtr.allocEmpty_wellFormed]
  split
  · simp only [Option.bind_eq_bind, Option.bind]
    grind [Rewriter.insertBlock?_WellFormed]
  · grind

end Veir
