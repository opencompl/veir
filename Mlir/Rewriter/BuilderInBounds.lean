import Mlir.Rewriter.Builder
import Mlir.Rewriter.RewriterGetSetInBounds

namespace Mlir

@[grind .]
theorem Builder.createOp_inBounds_mono (ptr : GenericPtr)
    (heq : createOp ctx opType numResults operands numRegions props ip h₁ h₂ h₃ = some (newCtx, newOp)) :
    ptr.InBounds ctx → ptr.InBounds newCtx := by
  simp [createOp] at heq
  split at heq <;> grind

@[grind .]
theorem Builder.createOp_fieldsInBounds
    (heq : createOp ctx opType numResults operands numRegions props ip h₁ h₂ h₃ = some (newCtx, newOp)) :
    ctx.FieldsInBounds → newCtx.FieldsInBounds := by
  intros hx
  simp [createOp] at heq
  split at heq <;> grind
