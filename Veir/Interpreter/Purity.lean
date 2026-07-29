module

public import Veir.Interpreter.Evaluate

import all Veir.Interpreter.Basic

/-!
# Semantic purity

This file connects executable effect metadata and fold evaluation to semantic
properties of the interpreter.
-/

public section

namespace Veir

/--
An operation is *pure* when its interpretation does not depend on, and does not modify, the
memory state: running it under any memory yields the same result values and control flow, with
the memory threaded through unchanged.

Concretely, the result under `memory₁` is the result under `memory₂` with the output memory
rewritten to the input memory.
-/
def OperationPtr.Pure (op : OperationPtr) (ctx : IRContext OpCode) : Prop :=
  ∀ operands memory₁ memory₂,
    interpretOp' (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
      (op.getResultTypes! ctx) operands (op.getSuccessors! ctx) memory₁ =
    (interpretOp' (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
      (op.getResultTypes! ctx) operands (op.getSuccessors! ctx) memory₂ |>.map
      (fun (r, _, cf) => (r, memory₁, cf)))

/--
Operations accepted by `foldEvaluate` have interpretations that are independent
of memory and thread the input memory through unchanged.

This is currently an explicit trusted boundary between the operation-effect
metadata and the interpreter. It should eventually be proved from the
interpreter implementations, preferably one dialect or operation family at a
time.
-/
axiom foldEvaluationCandidate_memory_independent
    (opCode : OpCode)
    (properties : propertiesOf opCode)
    (hCandidate : isFoldEvaluationCandidate opCode properties = true) :
    ∀ resultTypes operands successors memory₁ memory₂,
      interpretOp' opCode properties resultTypes operands successors memory₁ =
        Interp.map (fun (results, _, action) => (results, memory₁, action))
          (interpretOp' opCode properties resultTypes operands successors memory₂)

/--
Successful fold evaluation is equivalent to successful interpretation under
any memory, with that memory unchanged and no control-flow action.
-/
theorem foldEvaluate_eq_ok_iff
    (opCode : OpCode)
    (properties : propertiesOf opCode)
    (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue)
    (results : Array RuntimeValue)
    (memory : MemoryState)
    (hCandidate : isFoldEvaluationCandidate opCode properties = true) :
    foldEvaluate opCode properties resultTypes operands = some (.ok results) ↔
      interpretOp' opCode properties resultTypes operands #[] memory =
        some (.ok (results, memory, none)) := by
  rw [foldEvaluationCandidate_memory_independent opCode properties hCandidate
    resultTypes operands #[] memory MemoryState.empty]
  simp only [foldEvaluate, hCandidate, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  generalize
    interpretOp' opCode properties resultTypes operands #[] MemoryState.empty =
      interpretation
  cases interpretation with
  | none => simp [Interp.map, Interp, bind]
  | some result =>
    cases result with
    | ub => simp [Interp.map, Interp, bind]
    | ok result =>
      obtain ⟨results', memory', action⟩ := result
      cases action <;> simp [Interp.map, Interp, bind, pure]

/--
An operation accepted by `foldEvaluate` satisfies the semantic definition
`OperationPtr.Pure`.
-/
theorem OperationPtr.pure_of_foldEvaluationCandidate
    (op : OperationPtr)
    (ctx : IRContext OpCode)
    (hCandidate :
      isFoldEvaluationCandidate
        (op.getOpType! ctx)
        (op.getProperties! ctx (op.getOpType! ctx)) = true) :
    op.Pure ctx := by
  intro operands memory₁ memory₂
  exact foldEvaluationCandidate_memory_independent
    (op.getOpType! ctx)
    (op.getProperties! ctx (op.getOpType! ctx))
    hCandidate
    (op.getResultTypes! ctx)
    operands
    (op.getSuccessors! ctx)
    memory₁
    memory₂

namespace OperationPtr.Pure

variable {op : OperationPtr} {ctx : IRContext OpCode}

theorem interpretOp'_eq_interpretOp'_other_memory
    (opPure : op.Pure ctx) (memory₂ : MemoryState) :
      interpretOp' (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
        (op.getResultTypes! ctx) operands (op.getSuccessors! ctx) memory₁ =
      (interpretOp' (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
        (op.getResultTypes! ctx) operands (op.getSuccessors! ctx) memory₂ |>.map
      (fun (r, _, cf) => (r, memory₁, cf))) := by
  grind [Pure]

theorem interpretOp'_eq_ok_implies_memory_eq (h : op.Pure ctx) :
      interpretOp' (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
        (op.getResultTypes! ctx) operands (op.getSuccessors! ctx) memory₁ =
          some (.ok (resValues, memory₂, cf)) →
      memory₁ = memory₂ := by
  rw [h operands memory₁ memory₁]
  simp only [Interp.map, Option.map, Interp, UBOr.map]
  grind

end OperationPtr.Pure

end Veir
