module

public import Veir.Passes.Legalization.Validity.PhiCFG
import all Veir.Passes.Legalization.Validity.PhiCFG
import all Veir.GlobalOpInfo
import all Veir.Dialects.GMIR.OpInfo

public section
namespace Veir.Legalization.CTreeProofs

private theorem WidenedIncomingEdges.allocations (tr : WidenedIncomingEdges ctx dst updates) :
    PhiCastAllocation ctx dst := by
  induction tr with
  | nil => exact PhiAllocation.refl _
  | cons step rest ih =>
    exact PhiAllocation.transCasts (step.allocation.castStep (.inr step.extCode) step.extSuccessors)
      ih (fun op ho => ⟨(rest.opHeader ho).code, (rest.opHeader ho).successors⟩)

namespace PhiWidening

variable {src dst : WfIRContext OpCode} {block : BlockPtr} {args : List (Nat × Nat)}
    (W : PhiWidening src dst block args)
include W

/-- Every fresh operation is a cast with no successors. Block and region pointers are preserved. -/
theorem allocations : PhiCastAllocation src dst :=
  PhiAllocation.transCasts W.truncations.allocations W.extensions.allocations fun _ ho =>
    ⟨(W.extensions.opHeader ho).code, (W.extensions.opHeader ho).successors⟩

theorem originalRegion {r : RegionPtr} (h : r.InBounds dst.raw) : r.InBounds src.raw :=
  W.allocations.region h

/-- Each branch operation in the new context already belonged to the old context. -/
theorem originalBranch {op : OperationPtr} (opIn : op.InBounds dst.raw)
    (branch : (op.getOpType! dst.raw).branchOpInterface?.isSome) : op.InBounds src.raw := by
  rcases W.allocations.operation opIn with old | ⟨kind, _⟩
  · exact old
  · rcases kind with trunc | ext
    · rw [trunc] at branch; contradiction
    · rw [ext] at branch; contradiction

/-- Casts introduce no control-flow edges, and each existing operation keeps its successors. -/
theorem hasPredecessor {b : BlockPtr} (hin : b.InBounds src.raw) :
    b.hasPredecessor! dst.raw = b.hasPredecessor! src.raw := by
  apply Bool.eq_iff_iff.mpr
  rw [BlockPtr.hasPredecessor_iff_successor (W.ctxSame.blockIn hin),
      BlockPtr.hasPredecessor_iff_successor hin]
  constructor
  · rintro ⟨op, opIn, succ⟩
    rcases W.allocations.operation opIn with old | fresh
    · exact ⟨op, old, (W.opHeader old).successors ▸ succ⟩
    · simp [fresh.2] at succ
  · rintro ⟨op, opIn, succ⟩
    have hdr := W.opHeader opIn
    exact ⟨op, hdr.inBounds, hdr.successors ▸ succ⟩

/-- Widening changes no region entry or incoming control-flow edge. -/
theorem preserveEntries (entries : PhiEntries src) : PhiEntries dst := by
  intro r b rin first
  have old := W.originalRegion rin
  have entry := (W.ctxSame.firstBlock old).symm.trans first
  have bound : b.InBounds src.raw := by grind
  rw [W.hasPredecessor bound]
  exact entries old entry

end PhiWidening
end Veir.Legalization.CTreeProofs
