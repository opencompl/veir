module

public import Veir.Passes.Legalization.Validity.PhiWidening
public import Veir.Interfaces.ControlFlowInterfaces

public section

namespace Veir.Legalization.CTreeProofs.PhiWidening

/-- The updates of a branch occupy forwarded slots. In every successor segment, each slot
either receives the extension for its block argument or retains the original SSA operand. -/
structure BranchSlotPlacement {src dst : WfIRContext OpCode} {block : BlockPtr}
    {args : List (Nat × Nat)} (W : PhiWidening src dst block args)
    (op : OperationPtr) (fixed : Nat) (index : BranchOperandExtension → Nat) : Prop where
  fixedPrefix : ∀ u ∈ W.updates, u.operand.op = op → fixed ≤ u.operand.index
  slots : ∀ edge seg dest, (op.getSuccessors! src.raw)[edge]? = some dest →
    BranchOpInterface.getSuccessorOperands? op edge src.raw = some seg →
    ∀ i < seg.forwardedOperands.size,
      (∃ u ∈ W.updates, u.operand = ⟨op, seg.getOperandIndex i⟩ ∧
        block.getArgument (index u) = dest.getArgument i) ∨
      ((∀ u ∈ W.updates, u.operand ≠ ⟨op, seg.getOperandIndex i⟩) ∧
        dest.getArgument i ∉ selectedArgs block args.reverse)

end Veir.Legalization.CTreeProofs.PhiWidening
