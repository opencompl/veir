import Veir.DInterpreter.Basic
import Veir.DInterpreter.Lemmas
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

variable {OpInfo : Type} [HasOpInfo OpInfo] {ctx : WfIRContext OpCode}
variable {state : InterpreterState ctx}

/-!
## Equation Lemma
-/

/--
`state.EquationHolds ctx op` holds when `state` records the result of interpreting `op`.
This is encoded by stating that interpreting `op` in `state` produces `state` itself, which is
equivalent to saying that the results of interpreting `op` on the given `state` are present in
`state` itself.
-/
def InterpreterState.EquationHolds (ctx : WfIRContext OpCode) (state : InterpreterState ctx)
    (op : OperationPtr) : Prop :=
  ∃ controlFlow, interpretOp ctx op state = (state, controlFlow)

/-!
## SSA Invariant at a Program Point
-/

/--
An interpreter state satisfies the SSA invariant at a program point if it satisfies the equation
lemma for all operations that dominate that program point.
In other words, all operations that dominate the given location have already been interpreted and
their results are present in the state.
-/
def InterpreterState.EquationLemmaAt (ctx : WfIRContext OpCode) (state : InterpreterState ctx)
    (location : InsertPoint) (_locInBounds : location.InBounds ctx.raw := by grind) : Prop :=
  ∀ (op : OperationPtr) (_opInBounds : op.InBounds ctx.raw),
  op.dominatesIp location ctx →
  state.EquationHolds ctx op

theorem interpretOp_equationLemmaAt (ctxDom : ctx.Dom)
    (stateWf : state.EquationLemmaAt ctx (InsertPoint.before op) opInBounds)
    (opHasParent : (op.get! ctx.raw).parent = some block) :
    interpretOp ctx op state = (state', controlFlow) →
    state'.EquationLemmaAt ctx (InsertPoint.after op ctx.raw block) := by
  sorry
