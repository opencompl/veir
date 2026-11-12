module

public import Veir.Passes.DCE.dce
public import Veir.Passes.Pipeline.Soundness
import all Veir.Passes.DCE.dce

/-! # Soundness of the strict `dce` pass -/

public section
namespace Veir

/-- The strict `dce` pass refines the module: the driver only erases dead operations that do not
allocate, which `verifiedDeadCodeErasure` covers. -/
theorem DCEPass.runStrict_sound : DCEPass.runStrict.Sound :=
  strictContextPass_sound RewritePattern.PointwiseValid.empty

/-- The pass with its IO, in strict mode, returns what `DCEPass.runStrict` does. -/
theorem DCEPass.impl_eq_runStrict (ctx : WfIRContext OpCode) (op : OperationPtr)
    (opIn : op.InBounds ctx.raw) :
    DCEPass.impl true ctx op opIn = ExceptT.mk (pure (DCEPass.runStrict ctx op)) := by
  rw [DCEPass.impl]
  rfl

end Veir
end
