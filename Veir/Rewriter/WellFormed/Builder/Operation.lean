import Veir.IR.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.Basic
import Veir.Rewriter.WellFormed.Builder.BlockOperands
import Veir.Rewriter.WellFormed.Builder.OpOperands
import Veir.Rewriter.WellFormed.Builder.OpRegion
import Veir.Rewriter.WellFormed.Builder.OpResults
import Veir.Rewriter.WellFormed.Rewriter.Operation
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}

theorem Rewriter.createEmptyOp_wellFormed  (hctx : IRContext.WellFormed ctx) :
    Rewriter.createEmptyOp ctx opType properties = some (newCtx, newOp) →
    newCtx.WellFormed := by
  intro h
  constructor
  case inBounds => grind
  case valueDefUseChains =>
    intro valuePtr valuePtrInBounds
    have ⟨array, harray⟩ := hctx.valueDefUseChains valuePtr (by grind)
    exists array
    apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind
  case blockDefUseChains =>
    intro blockPtr blockPtrInBounds
    have ⟨array, harray⟩ := hctx.blockDefUseChains blockPtr (by grind)
    exists array
    apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind
  case opChain =>
    intro blockPtr blockPtrInBounds
    have ⟨array, harray⟩ := hctx.opChain blockPtr (by grind)
    exists array
    apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind
  case blockChain =>
    intro reg hreg
    have ⟨array, harray⟩ := hctx.blockChain reg (by grind)
    exists array
    apply RegionPtr.blockChain_unchanged (ctx := ctx) <;> grind
  case operations =>
    intro opPtr opPtrInBounds
    by_cases opPtr = newOp
    · constructor <;> grind
    · have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hctx.operations opPtr (by grind)
      constructor
      case neg.region_parent =>
        intro region regionInBounds
        apply Operation.WellFormed.region_parent.unchanged (ctx := ctx) <;> grind
      all_goals grind
  case blocks =>
    intro bl hbl
    have := hctx.blocks bl (by grind)
    apply Block.WellFormed_unchanged (ctx := ctx) <;> grind
  case regions =>
    intro reg hreg
    have := hctx.regions reg (by grind)
    apply Region.WellFormed_unchanged (ctx := ctx) <;> try grind

theorem Rewriter.createOp_WellFormed
    (hctx : IRContext.WellFormed ctx) :
    Rewriter.createOp ctx opType resultTypes operands blockOperands
      regions properties insertionPoint h₁ h₂ h₃ h₄ h₅ = some (newCtx, newOp) →
    newCtx.WellFormed := by
  simp only [createOp]
  split; grind
  rename_i ctx₁ newOp hNewOp
  have : ctx₁.WellFormed := by grind [Rewriter.createEmptyOp_wellFormed]
  split; grind
  rename_i ctx₂ hctx₂
  have : ctx₂.WellFormed :=
    by grind [Rewriter.initOpRegions_WellFormed, IRContext.wellFormed_Rewriter_initOpResults]
  grind [insertOp?_WellFormed, Rewriter.initOpOperands_WellFormed,
    Rewriter.initBlockOperands_WellFormed]
