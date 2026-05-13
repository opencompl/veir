import Veir.Interpreter.Basic
import Veir.Dominance

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {state state' : InterpreterState}
variable {op op' : OperationPtr}

@[grind =]
theorem InterpreterState.getVar?_setVar :
    (InterpreterState.setVar state var' val).getVar? var =
    if var = var' then some val else state.getVar? var := by
  grind [InterpreterState.setVar, InterpreterState.getVar?]

theorem InterpreterState.getVar?_setResultValues_loop {ctx : IRContext OpInfo} :
    (state.setResultValues_loop ctx op resultValues idx).getVar? value =
    match value with
    | .opResult {op := op', index := index} =>
      if op' = op ∧ index < idx then
        some resultValues[index]!
       else
         state.getVar? value
    | _ =>
      state.getVar? value := by
  fun_induction InterpreterState.setResultValues_loop
  next => grind
  next => grind [cases OpResultPtr, OperationPtr.getResult_def, cases ValuePtr]

@[grind =]
theorem InterpreterState.getVar?_setResultValues {ctx : IRContext OpInfo} :
    (state.setResultValues ctx op resultValues).getVar? value =
    match value with
    | .opResult {op := op', index := index} =>
      if op' = op ∧ index < op.getNumResults! ctx then
        some resultValues[index]!
       else
         state.getVar? value
    | _ =>
      state.getVar? value := by
  simp [InterpreterState.setResultValues, InterpreterState.getVar?_setResultValues_loop]

@[grind =]
theorem InterpreterState.getVar?_setResultValues_of_value_inBounds
    {ctx : IRContext OpInfo} (valueInBounds : value.InBounds ctx) :
    (state.setResultValues ctx op resultValues).getVar? value =
    match value with
    | .opResult {op := op', index := index} =>
      if op' = op then
        some resultValues[index]!
       else
         state.getVar? value
    | _ =>
      state.getVar? value := by
  simp only [getVar?_setResultValues]
  cases value <;> grind

theorem interpretOp_some_iff :
  interpretOp ctx op state = some (.ok (state', cf)) ↔
  ∃ operandValues resValues,
    (state.getOperandValues ctx op) = some operandValues ∧
    interpretOp' (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
      (op.getResultTypes! ctx) operandValues (op.getSuccessors! ctx) = some (.ok (resValues, cf)) ∧
    state' = state.setResultValues ctx op resValues := by
  simp only [interpretOp, bind, pure]
  rcases hOps : state.getOperandValues ctx op with _ | operands
  · grind
  rcases hOp : interpretOp' (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
      (op.getResultTypes! ctx) operands (op.getSuccessors! ctx) with _ | u
  · grind
  cases u <;> grind

theorem InterpreterState.getOperandValues_eq_of_getVar?_eq {ctx : IRContext OpInfo} :
    (∀ val, val ∈ op.getOperands! ctx → state.getVar? val = state'.getVar? val) →
    state.getOperandValues ctx op = state'.getOperandValues ctx op := by
  intro h
  simp only [getOperandValues, Array.mapM_eq_mapM_toList]
  suffices H : ∀ (l : List _), (∀ val ∈ l, state.getVar? val = state'.getVar? val) →
               l.mapM state.getVar? = l.mapM state'.getVar? by grind
  intro l hl
  induction l <;> grind

theorem InterpreterState.setResultValues_comm {ctx : WfIRContext OpInfo}
    {state : InterpreterState} (hOp : op₁ ≠ op₂) :
    (state.setResultValues ctx.raw op₁ resValues₁).setResultValues ctx.raw op₂ resValues₂ =
    (state.setResultValues ctx.raw op₂ resValues₂).setResultValues ctx.raw op₁ resValues₁ := by
  ext val runtimeVal
  cases val <;> grind

theorem InterpreterState.getVar?_setResultValues_operand_of_dominates {ctx : WfIRContext OpInfo}
    (ctxDom : ctx.Dom) (hdom : op'.dominates op ctx) :
    value ∈ op'.getOperands! ctx.raw →
    (state.setResultValues ctx.raw op resValues).getVar? value =
    state.getVar? value := by
  intro valueInOperands
  simp only [InterpreterState.getVar?_setResultValues]
  have := IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom hdom value valueInOperands
  cases value
  case blockArgument blockArg => grind
  case opResult opRes =>
    simp only [ite_eq_right_iff, and_imp]
    simp only [OperationPtr.getResults!.mem_iff_exists_index, ValuePtr.opResult.injEq, not_exists,
      not_and] at this
    grind [OperationPtr.getResult_def, cases OpResultPtr]

@[grind =>]
theorem InterpreterState.getOperandValues_setResultValues_of_dominates {ctx : WfIRContext OpInfo}
    (ctxDom : ctx.Dom) (hdom : op'.dominates op ctx) :
    (state.setResultValues ctx.raw op resValues).getOperandValues ctx.raw op' =
    state.getOperandValues ctx.raw op' := by
  apply InterpreterState.getOperandValues_eq_of_getVar?_eq
  grind [InterpreterState.getVar?_setResultValues_operand_of_dominates]

@[grind =>]
theorem InterpreterState.getOperandValues_setResultValues_self {ctx : WfIRContext OpInfo}
    (ctxDom : ctx.Dom) :
    (state.setResultValues ctx.raw op resValues).getOperandValues ctx.raw op =
    state.getOperandValues ctx.raw op := by
  exact getOperandValues_setResultValues_of_dominates ctxDom OperationPtr.dominates_refl

@[grind = ]
theorem InterpreterState.setResultValues_setResultValues_self {ctx : WfIRContext OpCode} :
    (state.setResultValues ctx.raw op resValues).setResultValues ctx.raw op resValues' =
    state.setResultValues ctx.raw op resValues' := by
  ext val runtimeVal
  simp only [InterpreterState.getVar?_setResultValues]
  grind
