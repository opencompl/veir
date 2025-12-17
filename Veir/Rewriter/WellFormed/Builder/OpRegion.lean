import Veir.IR.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.Basic

namespace Veir

theorem Rewriter.initOpRegions_WellFormed (ctx: IRContext) (opPtr: OperationPtr) (numRegions: Nat)
    (hop : opPtr.InBounds ctx) (hctx : IRContext.WellFormed ctx) (newCtx : IRContext):
    Rewriter.initOpRegions ctx opPtr numRegions hop = some newCtx →
    newCtx.WellFormed := by
  sorry
