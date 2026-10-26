module

public import Veir.Passes.DCE.Structure

public section

namespace Veir.DCE

/-- Every operand of a surviving operation is itself a surviving value. -/
theorem Erasures.operands_live {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (survives : operation.InBounds target.raw) :
    ∀ value ∈ operation.getOperands! source.raw, value.InBounds target.raw := by
  intro value member
  rw [← erases.getOperands operation survives] at member
  exact OperationPtr.getOperands!_inBounds target.wellFormed.inBounds survives member

/-- A live operand's original definition remains available in the source context. -/
theorem Erasures.operands_source_inBounds {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (survives : operation.InBounds target.raw) :
    ∀ value ∈ operation.getOperands! source.raw, value.InBounds source.raw := by
  intro value member
  exact erases.value_inBounds value (erases.operands_live operation survives value member)

end Veir.DCE
