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
`state.EquationHolds ctx op` holds when `state` records the result of interpreting `op`.
This is encoded by stating that interpreting `op` in `state` produces `state` itself, which is
equivalent to saying that the results of interpreting `op` on the given `state` are present in
`state` itself.
-/
def InterpreterState.EquationHolds (state : InterpreterState) (ctx : WfIRContext OpCode)
    (op : OperationPtr) : Prop :=
  ∃ controlFlow, interpretOp ctx op state = some (state, controlFlow)

theorem interpretOp_equationHolds_self
    {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom) :
    interpretOp ctx op state = some (state', controlFlow) →
    state'.EquationHolds ctx op := by
  simp only [InterpreterState.EquationHolds]
  intro hInterp
  exists controlFlow
  have ⟨operandValues, resValues, hOperandValues, hInterp', hResValues⟩ := interpretOp_some_iff.mp hInterp
  grind [interpretOp]

theorem interpretOp_equationHolds_other
    {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom) :
    interpretOp ctx op₁ state = some (state', cf₁) →
    op₂.dominates op₁ ctx →
    state.EquationHolds ctx op₂ →
    state'.EquationHolds ctx op₂ := by
  intro hInterp₁ hDom
  simp only [InterpreterState.EquationHolds]
  rintro ⟨cf₂, hInterp₂⟩
  exists cf₂
  have ⟨operandValues₁, resValues₁, hOperandValues₁, hInterp₁', hResValues₁⟩ := interpretOp_some_iff.mp hInterp₁
  have ⟨operandValues₂, resValues₂, hOperandValues₂, hInterp₂', hResValues₂⟩ := interpretOp_some_iff.mp hInterp₂
  subst state'
  simp only [interpretOp, bind, Option.bind, Option.pure_def]
  simp only [InterpreterState.getOperandValues_setResultValues_of_dominates ctxDom hDom]
  simp only [hOperandValues₂, hInterp₂']
  simp only [Option.some.injEq, Prod.mk.injEq, and_true]
  by_cases hOp : op₁ = op₂
  · grind
  · simp [InterpreterState.setResultValues_comm hOp, ←hResValues₂]

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
  op.dominatesIp location ctx →
  state.EquationHolds ctx op

theorem interpretOp_equationLemmaAt (ctxDom : ctx.Dom)
    (stateWf : state.EquationLemmaAt ctx (InsertPoint.before op) opInBounds)
    (opHasParent : (op.get! ctx.raw).parent = some block) :
    interpretOp ctx op state = some (state', controlFlow) →
    state'.EquationLemmaAt ctx (InsertPoint.after op ctx.raw block) := by
  intro hInterp
  simp only [InterpreterState.EquationLemmaAt] at stateWf ⊢
  intro op' op'InBounds hDom
  simp [OperationPtr.dominatesIp_iff] at hDom
  simp [OperationPtr.dominates_iff_strictlyDominates_or_eq] at hDom
  rcases hDom with hDom | hDom
  · apply interpretOp_equationHolds_other ctxDom hInterp
    · grind [OperationPtr.dominates_of_strictlyDominates]
    · grind [interpretOp_equationHolds_other, OperationPtr.dominatesIp_before]
  · grind [interpretOp_equationHolds_self]
