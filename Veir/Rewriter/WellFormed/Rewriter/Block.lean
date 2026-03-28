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

end Veir
