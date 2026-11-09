module

public import Veir.PatternRewriter.Puddle.CheckedExecution
public import Veir.PatternRewriter.Puddle.CTreeGreedySoundness
import all Veir.PatternRewriter.Puddle.CheckedExecution
import all Veir.PatternRewriter.Puddle.CTreeGreedySoundness
import all Veir.IRNesting

namespace Veir.Puddle
public section

/-- The runtime filter exactly checks the static single-step placement domain. -/
theorem rootEligible_sound {ctx : WfIRContext OpCode} {moduleOp op : OperationPtr}
    (checked : rootEligible moduleOp ctx op = true) : CTree.RootAdmissible ctx moduleOp op := by
  simp only [rootEligible, Bool.and_eq_true, beq_iff_eq] at checked
  obtain ⟨⟨rooted, regions⟩, parentCheck⟩ := checked
  refine ⟨OperationPtr.rootedAt?_sound rooted, ?_⟩
  cases parent : op.getParentRegion! ctx.raw with
  | none => simp [parent] at parentCheck
  | some region => exact ⟨region, rfl, by simpa [parent] using parentCheck, regions⟩

/-- No eligible in-bounds root is omitted by the total runtime filter. -/
theorem rootEligible_iff {ctx : WfIRContext OpCode} {moduleOp op : OperationPtr}
    (opIn : op.InBounds ctx.raw) :
    rootEligible moduleOp ctx op = true ↔ CTree.RootAdmissible ctx moduleOp op := by
  refine ⟨rootEligible_sound, ?_⟩
  rintro ⟨rooted, region, parent, ssa, regions⟩
  have checked := (OperationPtr.rootedAt?_iff opIn).mpr rooted
  simp only [rootEligible, checked, regions, BEq.rfl, parent, ssa, Bool.and_self]

end
end Veir.Puddle
