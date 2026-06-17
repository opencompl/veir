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
def InterpreterState.EquationHolds {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (op : OperationPtr) (inBounds : op.InBounds ctx.raw := by grind) : Prop :=
  ∃ controlFlow, interpretOp op state = some (.ok (state, controlFlow))

theorem interpretOp_equationHolds_self
    {ctx : WfIRContext OpCode} {state state' : InterpreterState ctx} (ctxDom : ctx.Dom)
    (inBounds : op.InBounds ctx.raw) :
    op.Pure ctx →
    interpretOp op state = some (.ok (state', controlFlow)) →
    state'.EquationHolds op := by
  simp only [InterpreterState.EquationHolds]
  grind [OperationPtr.Pure.interpretOp'_eq_ok_implies_memory_eq, interpretOp_some_iff]

theorem interpretOp_equationHolds_other
    {ctx : WfIRContext OpCode} {state state' : InterpreterState ctx} (ctxDom : ctx.Dom)
    {inBounds₁ : op₁.InBounds ctx.raw} {inBounds₂ : op₂.InBounds ctx.raw} :
    op₂.Pure ctx →
    interpretOp op₁ state inBounds₁ = some (.ok (state', cf₁)) →
    op₂.dominates op₁ ctx →
    state.EquationHolds op₂ →
    state'.EquationHolds op₂ := by
  intro op₂Pure hInterp₁ hDom
  simp only [InterpreterState.EquationHolds]
  rintro ⟨cf₂, hInterp₂⟩
  exists cf₂
  have ⟨operandValues₁, resValues₁, memory₁, resState₂, hOperandValues₁, hInterp₁', hResValues₁, hState'⟩ := interpretOp_some_iff.mp hInterp₁
  have ⟨operandValues₂, resValues₂, memory₂, resState₁, hOperandValues₂, hInterp₂', hResValues₂, hState⟩ := interpretOp_some_iff.mp hInterp₂
  subst state state'; simp_all only
  simp only [interpretOp, bind, pure, liftM, monadLift, MonadLift.monadLift]
  simp only [VariableState.getOperandValues_setResultValues?_of_dominates ctxDom hDom hResValues₁]
  simp only [hOperandValues₂, OperationPtr.interpret]
  rw [OperationPtr.Pure.interpretOp'_eq_interpretOp'_other_memory op₂Pure memory₂]
  simp only [hInterp₂', Interp.map, Option.map, UBOr.map]
  by_cases hOp : op₂ = op₁
  · grind
  · have := VariableState.setResultValues?_comm hOp hResValues₂ hResValues₁
    grind

/-!
## SSA Invariant at a Program Point
-/

/--
An interpreter state satisfies the SSA invariant at a program point if it satisfies the equation
lemma for all operations that dominate that program point.
In other words, all operations that dominate the given location have already been interpreted and
their results are present in the state.
-/
def InterpreterState.EquationLemmaAt {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (location : InsertPoint) (_locInBounds : location.InBounds ctx.raw := by grind) : Prop :=
  ∀ (op : OperationPtr) (_opInBounds : op.InBounds ctx.raw),
  op.Pure ctx →
  op.dominatesIp location ctx →
  state.EquationHolds op

theorem interpretOp_equationLemmaAt {ctx : WfIRContext OpCode} {opInBounds} {state state' : InterpreterState ctx}
    (ctxDom : ctx.Dom)
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) opInBounds)
    (opHasParent : (op.get! ctx.raw).parent = some block) :
    interpretOp op state = some (.ok (state', controlFlow)) →
    state'.EquationLemmaAt (InsertPoint.after op ctx.raw block) := by
  intro hInterp
  simp only [InterpreterState.EquationLemmaAt] at stateWf ⊢
  intro op' op'InBounds hPure hDom
  simp [OperationPtr.dominatesIp_iff] at hDom
  simp [OperationPtr.dominates_iff_strictlyDominates_or_eq] at hDom
  rcases hDom with hDom | hDom
  · apply interpretOp_equationHolds_other ctxDom (by grind) hInterp
    · grind [OperationPtr.dominates_of_strictlyDominates]
    · grind [interpretOp_equationHolds_other]
    · grind
  · grind [interpretOp_equationHolds_self]

/-- An interpreter state satisfies the `DefinesDominating` invariant at a program point if it
defines all values that dominate that program point. This should be satisfied by any state in the
interpreter. -/
def InterpreterState.DefinesDominating {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (location : InsertPoint) (_locInBounds : location.InBounds ctx.raw := by grind) : Prop :=
  ∀ (value : ValuePtr) (_valueInBounds : value.InBounds ctx.raw),
  value.dominatesIp location ctx →
  (state.variables.getVar? value).isSome

/-- Getting a dominating value from a state satisfying `DefinesDominating` at a program point is
always successful. -/
theorem InterpreterState.DefinesDominating.isSome_getVar_of_dominatesIp
    {state : InterpreterState ctx}
    (eqLemma : state.DefinesDominating location locInBounds)
    {value : ValuePtr} (valueInBounds : value.InBounds ctx.raw)
    (valueDom : value.dominatesIp location ctx) :
    (state.variables.getVar? value).isSome := by
  grind [InterpreterState.DefinesDominating]

/-- Getting a dominating value from a state satisfying `DefinesDominating` at a program point is
always successful. -/
theorem InterpreterState.DefinesDominating.exists_getVar_of_dominatesIp
    {state : InterpreterState ctx}
    (eqLemma : state.DefinesDominating location locInBounds)
    {value : ValuePtr} (valueInBounds : value.InBounds ctx.raw)
    (valueDom : value.dominatesIp location ctx) :
    ∃ val, state.variables.getVar? value = some val := by
  simp only [← Option.isSome_iff_exists]
  grind [InterpreterState.DefinesDominating.isSome_getVar_of_dominatesIp]

/-- All operands operation in a well-dominated program exist in a state that is `DefinesDominating`
right before the operation. -/
theorem InterpreterState.DefinesDominating.exists_getOperandValues_eq_some
    {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom) {state : InterpreterState ctx}
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    (stateDom : state.DefinesDominating (InsertPoint.before op) opInBounds) :
    ∃ val, state.variables.getOperandValues op = some val := by
  simp only [VariableState.getOperandValues, Array.exists_mapM_option_eq_some_iff]
  intro i hi
  apply InterpreterState.DefinesDominating.exists_getVar_of_dominatesIp stateDom (by grind)
  grind [WfIRContext.Dom.operand_dominates_op]

/-- `InterpreterState.DefinesDominating` is preserved when interpreting an operation: if every value
dominating the program point *before* `op` is available in `state`, then after running `op` every
value dominating the point *after* `op` is available in the resulting state. -/
theorem interpretOp_DefinesDominating {ctx : WfIRContext OpCode} {opInBounds}
    (ctxDom : ctx.Dom) {state state' : InterpreterState ctx}
    (stateDom : state.DefinesDominating (InsertPoint.before op) opInBounds)
    (opHasParent : (op.get! ctx.raw).parent = some block) :
    interpretOp op state = some (.ok (state', controlFlow)) →
    state'.DefinesDominating (InsertPoint.after op ctx.raw block) := by
  intro hinterp
  simp only [InterpreterState.DefinesDominating] at stateDom ⊢
  simp only [interpretOp_some_iff] at hinterp
  have ⟨operandValues, resValues, mem', varState', hoperand, hinterp, hresValues, hstate⟩ := hinterp
  subst state'
  intro value valueInBounds valueDom
  cases (WfIRContext.Dom.value_dominatesIp_after_iff ctxDom).mp valueDom
  case inl =>
    have := stateDom value (by grind) (by grind)
    grind
  case inr =>
    grind [OperationPtr.getResults!.mem_iff_exists_index]

/-- Interpreting a verified operation never fails on a state satisfying `DefinesDominating` at the
operation's location. -/
theorem InterpreterState.DefinesDominating.interpretOp_ne_none
    (ctxDom : ctx.Dom) (opInBounds : op.InBounds ctx.raw) {state : InterpreterState ctx}
    (stateDom : state.DefinesDominating (InsertPoint.before op) opInBounds)
    (opVerif : op.Verified ctx opInBounds) :
    ∃ state', interpretOp op state opInBounds = some state' := by
  simp only [interpretOp]
  have ⟨operandValues, hOperandValues⟩ := stateDom.exists_getOperandValues_eq_some ctxDom opInBounds
  simp only [hOperandValues]
  have hconforms : RuntimeValue.ArrayConforms operandValues (op.getOperandTypes! ctx.raw) := by
    grind [VariableState.getOperandValues_conforms]
  have ⟨resValues, hresValues⟩ := exists_interpretOp'_eq_some opVerif hconforms state.memory
  simp only [hresValues, bind]
  rcases resValues with ⟨resValues, mem', act⟩ | _
  · simp only [liftM, monadLift, MonadLift.monadLift, pure, Interp]
    have := interpretOp'_results_conform opVerif hconforms hresValues
    have ⟨v, hv⟩ :=
      (VariableState.setResultValues?_isSome_iff_conforms state.variables opInBounds).mp this
    simp [hv]
  · simp [Interp]
