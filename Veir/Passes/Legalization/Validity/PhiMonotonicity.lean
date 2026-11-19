module

public import Veir.Passes.Legalization.Validity.PhiCFGFrame
public import Veir.Passes.Legalization.Validity.PhiRequests
public import Veir.Passes.Legalization.Validity.PhiBranchDispatch
import all Veir.Passes.Legalization.Validity.PhiWidening
import all Veir.Interpreter.CTreeRefinement.OpList
import Veir.Interpreter.CTreeRefinement.Monotone
import Veir.Dialects.GMIR.CTreeMonotonicity

public section
namespace Veir.Legalization.CTreeProofs

/-- For a lifted instruction, raw interpreter monotonicity applies to operands of every type. -/
theorem treeMonotone_of_lifted {ctx : WfIRContext OpCode} {op : OperationPtr}
    (lifted : (op.getOpType! ctx.raw).isLifted)
    (mono : InterpretOp'Monotone (op.getOpType! ctx.raw)) : op.TreeMonotone ctx := by
  intro vs vs' m m' _ hv hm
  rw [CTree.interpretOp'_eq_monadLift lifted, CTree.interpretOp'_eq_monadLift lifted]
  exact CTree.sim_monadLift_of_isRefinedBy (mono.monotone _ _ vs vs' _ m m' hv hm)

/-- Header and operand type equality transfer monotonicity to the rewritten instruction. -/
theorem PhiOpHeader.treeMonotone_of_source {src dst : WfIRContext OpCode} {op : OperationPtr}
    (hdr : PhiOpHeader src dst op)
    (types : op.getOperandTypes! dst.raw = op.getOperandTypes! src.raw)
    (mono : op.TreeMonotone src) : op.TreeMonotone dst := by
  intro vs vs' m m' conforms hv hm
  simp only [hdr.properties, hdr.results, hdr.successors]
  rw [hdr.code]
  exact mono vs vs' m m' (types ▸ conforms) hv hm

private theorem treeMonotone_anyext {ctx : WfIRContext OpCode} {op : OperationPtr}
    (code : op.getOpType! ctx.raw = .gmir .g_anyext) : op.TreeMonotone ctx := by
  intro vs vs' m m' _ related memory
  rw [code]
  apply CTree.sim_mono (CTree.sim_g_anyext (Q := fun _ => True) _ _ _ _ related memory
    (fun _ _ _ _ => trivial))
  exact fun _ _ h => h.1

namespace PhiWidening

variable {src dst : WfIRContext OpCode} {block : BlockPtr} {args : List (Nat × Nat)}
    (W : PhiWidening src dst block args)

/-- Operands may move to the inserted truncations, which have exactly the old operand types. -/
theorem operandTypes_of_noUpdates {op : OperationPtr} (opIn : op.InBounds src.raw)
    (untouched : ∀ u ∈ W.updates, u.operand.op ≠ op) :
    op.getOperandTypes! dst.raw = op.getOperandTypes! src.raw := by
  have step := W.truncations.ops op opIn
  have same := step.trans_id (W.extensions.opSame step.inBounds (fun u hu => Ne.symm (untouched u hu)))
  rw [OperationPtr.getOperandTypes!_def, OperationPtr.getOperandTypes!_def, same.operands, Array.map_map]
  exact Array.map_congr_left fun v h => W.mappedType (OperationPtr.getOperands!_inBounds
    src.wellFormed.inBounds opIn h)

include W in
/-- Rewriting a phi preserves monotonicity of old operations. The new truncations and
extensions are monotone for all operands, including poison. -/
theorem preserveMonotone (mono : TreeMonotoneOps src) : TreeMonotoneOps dst := by
  intro op opIn
  rcases W.allocations.operation opIn with old | ⟨trunc | ext, _⟩
  · have hdr := W.opHeader old
    by_cases untouched : ∀ u ∈ W.updates, u.operand.op ≠ op
    · exact hdr.treeMonotone_of_source (W.operandTypes_of_noUpdates old untouched) (mono op old)
    · simp only [Classical.not_forall, Classical.not_not] at untouched
      obtain ⟨u, hu, owner⟩ := untouched
      obtain ⟨edge, _, seg, _, read, _, slot⟩ :=
        (W.update_iff (p := u.operand) (width := u.width)).mp ⟨u, hu, rfl, rfl⟩
      have e : edge.op = op := (congrArg OpOperandPtr.op slot).symm.trans owner
      rw [e] at read
      have active := branchInterface_of_segment read
      rw [← hdr.code] at active
      obtain ⟨lifted, raw⟩ := branchLiftAndMonotone _ active
      exact treeMonotone_of_lifted lifted raw
  · apply treeMonotone_of_lifted (trunc ▸ rfl)
    rw [trunc]
    exact gmir_monotone_g_trunc
  · exact treeMonotone_anyext ext

end PhiWidening
end Veir.Legalization.CTreeProofs
