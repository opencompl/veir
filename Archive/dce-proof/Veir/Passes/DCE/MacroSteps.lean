module

public import Veir.Passes.DCE.ErasureTrace
public import Veir.Interpreter.CTreeRefinement.Iteration
import all Veir.Interpreter.CTreeRefinement.Iteration

public section

namespace Veir.DCE

/-- Match one chronological deletion against an interpreter's current operation.
Locations without an operation, such as block entries, never match. -/
def deletionPredicate (operationAt : ι → Option OperationPtr) (operation : OperationPtr) : ι → Bool :=
  fun state => operationAt state == some operation

/-- Fold original source steps in chronological deletion order. An appended
deletion wraps the already grouped body, retaining all intermediate silent steps. -/
def macroBody (operationAt : ι → Option OperationPtr) (body : ι → Tree (ι ⊕ α))
    (operations : List OperationPtr) : ι → Tree (ι ⊕ α) :=
  Tree.spliceIterBodies body (operations.map (deletionPredicate operationAt))

theorem macroBody_nil (operationAt : ι → Option OperationPtr) (body : ι → Tree (ι ⊕ α)) :
    macroBody operationAt body [] = body := by
  simp [macroBody, Tree.spliceIterBodies]

theorem macroBody_snoc (operationAt : ι → Option OperationPtr) (body : ι → Tree (ι ⊕ α))
    (operations : List OperationPtr) (operation : OperationPtr) :
    macroBody operationAt body (operations ++ [operation]) =
      Tree.spliceIterBody (macroBody operationAt body operations)
        (deletionPredicate operationAt operation) := by
  simp [macroBody, Tree.spliceIterBodies, List.foldl_append]

/-- Grouping the finite deleted chains preserves the exact original iteration
tree. This equality is unconditional in the initial location and state. -/
theorem iter_eq_macroBody (operationAt : ι → Option OperationPtr) (body : ι → Tree (ι ⊕ α))
    (operations : List OperationPtr) (initial : ι) :
    CTree.iter body initial = CTree.iter (macroBody operationAt body operations) initial :=
  Tree.iter_spliceIterBodies body (operations.map (deletionPredicate operationAt)) initial

/-- Every actual successful DCE run supplies a duplicate-free chronological
normalization list, exact deletion membership, and exact source-loop equality. -/
theorem applyInContext_macroBody {source target : WfIRContext OpCode}
    (success : RewritePattern.applyInContext pattern source = some target)
    (operationAt : ι → Option OperationPtr) (body : ι → Tree (ι ⊕ α)) :
    ∃ operations, ErasureTrace source operations target ∧ operations.Nodup ∧
      (∀ operation, operation.InBounds source.raw →
        (operation ∈ operations ↔ ¬operation.InBounds target.raw)) ∧
      ∀ initial, CTree.iter body initial =
        CTree.iter (macroBody operationAt body operations) initial := by
  obtain ⟨operations, trace⟩ := (applyInContext_erasures source target success).exists_trace
  exact ⟨operations, trace, trace.nodup, trace.deleted_iff, iter_eq_macroBody operationAt body operations⟩

end Veir.DCE
