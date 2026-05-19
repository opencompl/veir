import Veir.Interpreter.Basic
import Veir.Interpreter.Lemmas
import Veir.Dominance

/-!
# Equation Lemma and SSA Invariant

This file contains the definition of the equation lemma (`EquationLemmaAt`) and the proof of
preservation when interpreting an operation.

The equation lemma is based on the paper "A formally verified SSA-based middle-end" from
Gilles Barthe, Delphine Demange, and David Pichardie. Our definition is slightly different as
CompCertSSA semantics are based on small-step operational semantics.
-/

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {state : InterpreterState}

/-!
## Equation Lemma
-/

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
  simp only [Interp.map, Option.map, UBOr.map]
  grind

end OperationPtr.Pure

/--
`state.EquationHolds ctx op` holds when `state` records the result of interpreting `op`.
This is encoded by stating that interpreting `op` in `state` produces `state` itself, which is
equivalent to saying that the results of interpreting `op` on the given `state` are present in
`state` itself.
-/
def InterpreterState.EquationHolds (state : InterpreterState) (ctx : WfIRContext OpCode)
    (op : OperationPtr) : Prop :=
  ∃ controlFlow, interpretOp ctx op state = some (.ok (state, controlFlow))

theorem interpretOp_equationHolds_self
    {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom) :
    op.Pure ctx →
    interpretOp ctx op state = some (.ok (state', controlFlow)) →
    state'.EquationHolds ctx op := by
  simp only [InterpreterState.EquationHolds]
  grind [interpretOp_some_iff, OperationPtr.Pure.interpretOp'_eq_ok_implies_memory_eq]

theorem interpretOp_equationHolds_other
    {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom) :
    op₂.Pure ctx →
    interpretOp ctx op₁ state = some (.ok (state', cf₁)) →
    op₂.dominates op₁ ctx →
    state.EquationHolds ctx op₂ →
    state'.EquationHolds ctx op₂ := by
  intro op₂Pure hInterp₁ hDom
  simp only [InterpreterState.EquationHolds]
  rintro ⟨cf₂, hInterp₂⟩
  exists cf₂
  have ⟨operandValues₁, resValues₁, memory₁, hOperandValues₁, hInterp₁', hResValues₁⟩ := interpretOp_some_iff.mp hInterp₁
  have ⟨operandValues₂, resValues₂, memory₂, hOperandValues₂, hInterp₂', hResValues₂⟩ := interpretOp_some_iff.mp hInterp₂
  subst state'
  simp only [interpretOp, bind, pure]
  simp only [VariableState.getOperandValues_setResultValues_of_dominates ctxDom hDom]
  simp only [hOperandValues₂]
  rw [OperationPtr.Pure.interpretOp'_eq_interpretOp'_other_memory op₂Pure state.memory]
  simp only [Interp.map, Option.map, hInterp₂', UBOr.map]
  by_cases hOp : op₁ = op₂
  · grind
  · simp only [VariableState.setResultValues_comm hOp]
    cases state; grind

/-!
## SSA Invariant at a Program Point
-/

/--
An interpreter state satisfies the SSA invariant at a program point if it satisfies the equation
lemma for all operations that dominate that program point.
In other words, all operations that dominate the given location have already been interpreted and
their results are present in the state.
-/
def InterpreterState.EquationLemmaAt (state : InterpreterState) (ctx : WfIRContext OpCode)
    (location : InsertPoint) (_locInBounds : location.InBounds ctx.raw := by grind) : Prop :=
  ∀ (op : OperationPtr) (_opInBounds : op.InBounds ctx.raw),
  op.Pure ctx →
  op.dominatesIp location ctx →
  state.EquationHolds ctx op

theorem interpretOp_equationLemmaAt (ctxDom : ctx.Dom)
    (stateWf : state.EquationLemmaAt ctx (InsertPoint.before op) opInBounds)
    (opHasParent : (op.get! ctx.raw).parent = some block) :
    interpretOp ctx op state = some (.ok (state', controlFlow)) →
    state'.EquationLemmaAt ctx (InsertPoint.after op ctx.raw block) := by
  intro hInterp
  simp only [InterpreterState.EquationLemmaAt] at stateWf ⊢
  intro op' op'InBounds hPure hDom
  simp [OperationPtr.dominatesIp_iff] at hDom
  simp [OperationPtr.dominates_iff_strictlyDominates_or_eq] at hDom
  rcases hDom with hDom | hDom
  · apply interpretOp_equationHolds_other ctxDom (by grind) hInterp
    · grind [OperationPtr.dominates_of_strictlyDominates]
    · grind [interpretOp_equationHolds_other]
  · grind [interpretOp_equationHolds_self]
