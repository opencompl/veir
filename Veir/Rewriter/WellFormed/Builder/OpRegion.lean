import Veir.IR.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.Basic

namespace Veir

set_option warn.sorry false in
theorem Rewriter.initOpRegions_WellFormed (opPtr: OperationPtr)
    (hop : opPtr.InBounds ctx) (hctx : IRContext.WellFormed ctx) (newCtx : IRContext):
    Rewriter.initOpRegions ctx opPtr regions n hop regionInBounds (by grind) hn = some newCtx →
    newCtx.WellFormed := by
  sorry
