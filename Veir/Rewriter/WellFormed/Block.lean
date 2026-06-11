module

public import Veir.IR.Basic
public import Veir.Rewriter.Basic
import all Veir.Rewriter.Basic

import Veir.IR.WellFormed
import Veir.Rewriter.Basic
import Veir.Rewriter.GetSet
import Veir.Rewriter.InsertPoint
import Veir.Rewriter.LinkedList.WellFormed
import Veir.Rewriter.WellFormed.BlockArguments

public section

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
    grind [Option.maybe₁_def]

theorem BlockPtr.operationList_rewriter_insertBlock?
    {block : BlockPtr} {blockInBounds : block.InBounds newCtx}
    (h : Rewriter.insertBlock? ctx newOp ip newOpIn insIn ctxInBounds = some newCtx)
    (ctxWf : ctx.WellFormed) :
    block.operationList newCtx newCtxWf blockInBounds = block.operationList ctx ctxWf (by grind) := by
  simp only [←BlockPtr.operationList_iff_BlockPtr_OpChain]
  grind [BlockPtr.opChain_BlockPtr_linkBetweenWithParent, Rewriter.insertBlock?]

grind_pattern BlockPtr.operationList_rewriter_insertBlock? =>
  Rewriter.insertBlock? ctx newOp ip newOpIn insIn ctxInBounds, newCtx.WellFormed, some newCtx,
  block.operationList newCtx newCtxWf blockInBounds

/-- # Rewriter.insertBlock? -/

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
    apply OperationPtr.WellFormed_unchanged (ctx := ctx) <;> grind
  case blocks =>
    intro block blockInBounds
    by_cases bl = block
    · constructor <;> grind [Block.empty]
    · have := hctx.blocks block (by grind)
      apply BlockPtr.WellFormed_unchanged (ctx := ctx) <;> grind
  case regions =>
    intro region regionInBounds
    have := hctx.regions region (by grind)
    apply RegionPtr.WellFormed_unchanged (ctx := ctx) <;> grind

theorem BlockPtr.operationList_blockPtr_allocEmpty
    {block : BlockPtr} {blockInBounds : block.InBounds newCtx}
    (h : BlockPtr.allocEmpty ctx = some (newCtx, bl)) (ctxWf : ctx.WellFormed) :
    block.operationList newCtx newCtxWf blockInBounds =
    if h : block = bl then #[] else block.operationList ctx ctxWf (by grind) := by
  apply BlockPtr.operationList_iff_BlockPtr_OpChain.mp
  by_cases hbb : block = bl
  · grind [Block.empty, BlockPtr.OpChain]
  · apply BlockPtr.OpChain_unchanged (ctx := ctx) <;>
      grind [BlockPtr.operationListWF]

grind_pattern BlockPtr.operationList_blockPtr_allocEmpty =>
  BlockPtr.allocEmpty ctx, some (newCtx, bl), newCtx.WellFormed, some newCtx,
  block.operationList newCtx newCtxWf blockInBounds

theorem Rewriter.createBlock_WellFormed
    (h : Rewriter.createBlock ctx types ip hctx hip = some (newCtx, newBlock))
    (ctxWf : ctx.WellFormed) :
    newCtx.WellFormed := by
  simp only [Rewriter.createBlock] at h
  split at h; grind; rename_i ctx₁ newBlock₁ hctx₁
  have : ctx₁.WellFormed := by grind [BlockPtr.allocEmpty_wellFormed]
  split at h
  · simp only [Option.bind_eq_bind, Option.bind] at h
    grind [IRContext.wellFormed_Rewriter_initBlockArguments, Rewriter.insertBlock?_WellFormed]
  · grind [IRContext.wellFormed_Rewriter_initBlockArguments]

/-- Any block that already existed before `Rewriter.createBlock` keeps its operation chain. -/
theorem BlockPtr.opChain_rewriter_createBlock {block : BlockPtr} {array : Array OperationPtr}
    (hWf : BlockPtr.OpChain block ctx array)
    (h : Rewriter.createBlock ctx types ip hctx hip = some (newCtx, newBlock)) :
    BlockPtr.OpChain block newCtx array := by
  simp only [Rewriter.createBlock] at h
  split at h; grind
  rename_i ctx₁ newBlock₁ hAlloc
  have hc1 : BlockPtr.OpChain block ctx₁ array := by
    apply BlockPtr.OpChain_unchanged (ctx := ctx) hWf <;> grind
  have hc2 : BlockPtr.OpChain block (Rewriter.initBlockArguments ctx₁ newBlock₁ types) array :=
    BlockPtr.opChain_Rewriter_initBlockArguments hc1
  split at h
  · simp only [Option.bind_eq_bind, Option.bind] at h
    grind [Rewriter.insertBlock?, BlockPtr.opChain_BlockPtr_linkBetweenWithParent]
  · grind

/-- The block freshly created by `Rewriter.createBlock` has an empty operation chain. -/
theorem BlockPtr.opChain_rewriter_createBlock_new
    (h : Rewriter.createBlock ctx types ip hctx hip = some (newCtx, newBlock)) :
    BlockPtr.OpChain newBlock newCtx #[] := by
  simp only [Rewriter.createBlock] at h
  split at h; grind
  rename_i ctx₁ newBlock₁ hAlloc
  have hc0 : BlockPtr.OpChain newBlock₁ ctx₁ #[] := by grind [Block.empty, BlockPtr.OpChain]
  have hc1 : BlockPtr.OpChain newBlock₁ (Rewriter.initBlockArguments ctx₁ newBlock₁ types) #[] :=
    BlockPtr.opChain_Rewriter_initBlockArguments hc0
  split at h
  · simp only [Option.bind_eq_bind, Option.bind] at h
    grind [BlockPtr.opChain_BlockPtr_linkBetweenWithParent, Rewriter.insertBlock?]
  · grind

theorem BlockPtr.operationList_rewriter_createBlock (ctxWf : ctx.WellFormed)
    (newCtxWf : newCtx.WellFormed) {block : BlockPtr} {blockInBounds : block.InBounds newCtx}
    (h : Rewriter.createBlock ctx types ip hctx hip = some (newCtx, newBlock)) :
    block.operationList newCtx newCtxWf blockInBounds =
    if hb : block = newBlock then #[] else block.operationList ctx ctxWf := by
  by_cases hbb : block = newBlock
  · grind [BlockPtr.opChain_rewriter_createBlock_new h]
  · have hChain : BlockPtr.OpChain block ctx (block.operationList ctx ctxWf) := by grind
    grind [BlockPtr.opChain_rewriter_createBlock hChain h]

grind_pattern BlockPtr.operationList_rewriter_createBlock =>
  Rewriter.createBlock ctx types ip hctx hip, some (newCtx, newBlock), newCtx.WellFormed,
  block.operationList newCtx newCtxWf blockInBounds

end Veir
