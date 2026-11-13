module

public import Veir.Passes.DCE.dce
public import Veir.Passes.Pipeline.Soundness
import all Veir.Passes.DCE.dce

/-! # Soundness of the `dce` pass -/

public section
namespace Veir

/-- The `dce` pass refines the module: the driver only erases dead operations that do not
allocate, which `verifiedDeadCodeErasure` covers. -/
theorem DCEPass.run_sound : DCEPass.run.Sound :=
  checkedContextPass_sound RewritePattern.PointwiseValid.empty

/-- The pass with its IO returns what `DCEPass.run` does. -/
theorem DCEPass.impl_eq_run (ctx : WfIRContext OpCode) (op : OperationPtr)
    (opIn : op.InBounds ctx.raw) :
    DCEPass.impl ctx op opIn = ExceptT.mk (pure (DCEPass.run ctx op)) := by
  rw [DCEPass.impl]

end Veir
end
