import Veir.IR.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.GetSetInBounds
import Veir.Rewriter.WellFormed.Region
import Veir.Rewriter.WellFormed.Operation
import Veir.Rewriter.WellFormed.Block

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}

theorem IRContext.wellFormed_IRContext_create :
    IRContext.create OpInfo = some (ctx, op) →
    ctx.WellFormed := by
  simp only [create]
  split; grind; rename_i ctx₁ region hctx₁
  have : ctx₁.WellFormed := by
    grind [IRContext.wellFormed_Rewriter_createRegion, IRContext.empty_wellFormed]
  split; grind; rename_i ctx₂ op' hctx₂
  have : ctx₂.WellFormed := by grind [Rewriter.createOp_WellFormed]
  split; grind; rename_i ctx₃ op'' hctx₃
  grind [Rewriter.createBlock_WellFormed]
