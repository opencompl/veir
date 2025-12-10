import Mlir.Core.Basic
import Mlir.Core.WellFormed
import Mlir.Rewriter.Builder

namespace Mlir

theorem Builder.initOpRegions_WellFormed (ctx: IRContext) (opPtr: OperationPtr) (numRegions: Nat)
    (hop : opPtr.InBounds ctx) (hctx : IRContext.WellFormed ctx) (newCtx : IRContext):
    Builder.initOpRegions ctx opPtr numRegions hop = some newCtx →
    newCtx.WellFormed := by
  sorry
