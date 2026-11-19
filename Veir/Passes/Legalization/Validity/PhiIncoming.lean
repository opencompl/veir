module

public import Veir.Passes.Legalization.LegalizerHelper
public import Veir.Interfaces.ControlFlowInterfaces
import all Veir.Passes.Legalization.LegalizerHelper
import Init.Internal.Order.While

namespace Veir.Legalization.CTreeProofs

private def visitEdge (ctx : IRContext OpCode) (_ : Unit)
    (s : List BlockOperandPtr × Option BlockOperandPtr) : Id (ForInStep (List BlockOperandPtr × Option BlockOperandPtr)) :=
  match s.2 with
  | some edge => pure (.yield (edge :: s.1, edge.getNextUse! ctx))
  | _ => pure (.done (s.1, s.2))

private theorem visitEdges_eq {ctx : IRContext OpCode} {block : BlockPtr}
    {chain : Array BlockOperandPtr} (wf : block.DefUse ctx chain)
    (i : Nat) (acc : List BlockOperandPtr) :
    Lean.Loop.forIn {} (acc, chain[i]?) (visitEdge ctx) =
      ((chain.toList.drop i).reverse ++ acc, none) := by
  rw [Lean.Loop.forIn_eq_of_monadTail]
  by_cases hi : i < chain.size
  · simp only [visitEdge, Array.getElem?_eq_getElem hi, pure_bind]
    change Lean.Loop.forIn {} (chain[i] :: acc, _) (visitEdge ctx) = _
    rw [wf.nextElems hi, visitEdges_eq wf (i + 1)]
    rw [List.drop_eq_getElem_cons (l := chain.toList) (by simpa using hi : i < chain.toList.length)]
    simp
  · simp [visitEdge, Array.getElem?_eq_none (by omega : chain.size ≤ i),
      List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_gt hi : chain.toList.length ≤ i)] <;> rfl
termination_by chain.size - i

private theorem incomingEdges_eq {ctx : IRContext OpCode} {block : BlockPtr}
    {chain : Array BlockOperandPtr} (wf : block.DefUse ctx chain) :
    incomingEdges ctx block = chain.toList := by
  change (Lean.Loop.forIn {} ([], block.getFirstUse! ctx) (visitEdge ctx)).1.reverse = _
  rw [← wf.firstElem, visitEdges_eq wf 0]
  simp

public section

/-- A successful widening visits the block's complete def-use chain in order. It records the
original branch operand segments before inserting truncations, then rewrites those segments. -/
theorem widenBlockArgumentsChecked_steps {ctx after : WfIRContext OpCode} {block : BlockPtr}
    {args : List (Nat × Nat)} (blockIn : block.InBounds ctx.raw)
    (run : widenBlockArgumentsChecked block args ctx = .ok after) :
    ∃ (uses : Array BlockOperandPtr) (edges : List (OperationPtr × SuccessorOperands)) (truncated : WfIRContext OpCode),
      block.DefUse ctx.raw uses ∧
      uses.toList.mapM (fun edge => do
        return (edge.op, ← BranchOpInterface.getSuccessorOperands? edge.op edge.index ctx.raw))
          = some edges ∧
      args.foldlM (m := Option) (init := ctx) (fun c (i, w) =>
        widenBlockArgument (InsertPoint.atStart! block ctx.raw) ⟨block, i⟩ w c) = some truncated ∧
      edges.foldlM (m := Option) (init := truncated) (fun c (branch, operands) =>
        args.foldlM (init := c) fun t (i, w) =>
          widenBranchOperand t ⟨branch, operands.getOperandIndex i⟩ w) = some after := by
  obtain ⟨uses, wf⟩ := ctx.wellFormed.blockDefUseChains block blockIn
  have chain : block.DefUse ctx.raw uses := by simpa using wf
  unfold widenBlockArgumentsChecked at run
  split at run <;> try contradiction
  split at run <;> try contradiction
  cases run
  rename_i success
  unfold widenBlockArgumentsImpl at success
  rw [incomingEdges_eq chain] at success
  simp only [bind, Option.bind] at success
  split at success <;> try contradiction
  rename_i edges segments
  dsimp only at success
  split at success <;> try contradiction
  exact ⟨uses, edges, _, chain, segments, by assumption, success⟩

end
end Veir.Legalization.CTreeProofs
