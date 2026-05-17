import Veir.Interpreter.Basic
import Veir.Dominance

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {varState varState' : VariableState}
variable {state state' : InterpreterState}
variable {op op' : OperationPtr}

@[grind =]
theorem VariableState.getVar?_setVar :
    (VariableState.setVar varState var' val).getVar? var =
    if var = var' then some val else varState.getVar? var := by
  grind [VariableState.setVar, VariableState.getVar?]

theorem VariableState.getVar?_setResultValues_loop {ctx : IRContext OpInfo} :
    (varState.setResultValues_loop ctx op resultValues idx).getVar? value =
    match value with
    | .opResult {op := op', index := index} =>
      if op' = op ∧ index < idx then
        some resultValues[index]!
       else
         varState.getVar? value
    | _ =>
      varState.getVar? value := by
  fun_induction VariableState.setResultValues_loop
  next => grind
  next => grind [cases OpResultPtr, OperationPtr.getResult_def, cases ValuePtr]

@[grind =]
theorem VariableState.getVar?_setResultValues {ctx : IRContext OpInfo} :
    (varState.setResultValues ctx op resultValues).getVar? value =
    match value with
    | .opResult {op := op', index := index} =>
      if op' = op ∧ index < op.getNumResults! ctx then
        some resultValues[index]!
       else
         varState.getVar? value
    | _ =>
      varState.getVar? value := by
  simp [VariableState.setResultValues, VariableState.getVar?_setResultValues_loop]

@[grind =]
theorem VariableState.getVar?_setResultValues_of_value_inBounds
    {ctx : IRContext OpInfo} (valueInBounds : value.InBounds ctx) :
    (varState.setResultValues ctx op resultValues).getVar? value =
    match value with
    | .opResult {op := op', index := index} =>
      if op' = op then
        some resultValues[index]!
       else
         varState.getVar? value
    | _ =>
      varState.getVar? value := by
  simp only [getVar?_setResultValues]
  cases value <;> grind

theorem interpretOp_some_iff :
  interpretOp ctx op state = some (.ok (state', cf)) ↔
  ∃ operandValues resValues mem',
    (state.variables.getOperandValues ctx op) = some operandValues ∧
    interpretOp' (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
      (op.getResultTypes! ctx) operandValues (op.getSuccessors! ctx) state.memory = some (.ok (resValues, mem', cf)) ∧
    state' = ⟨state.variables.setResultValues ctx op resValues, mem'⟩ := by
  simp only [interpretOp, bind, pure]
  grind

theorem VariableState.getOperandValues_eq_of_getVar?_eq {ctx : IRContext OpInfo} :
    (∀ val, val ∈ op.getOperands! ctx → varState.getVar? val = varState'.getVar? val) →
    varState.getOperandValues ctx op = varState'.getOperandValues ctx op := by
  intro h
  simp only [getOperandValues, Array.mapM_eq_mapM_toList]
  suffices H : ∀ (l : List _), (∀ val ∈ l, varState.getVar? val = varState'.getVar? val) →
               l.mapM varState.getVar? = l.mapM varState'.getVar? by grind
  intro l hl
  induction l <;> grind

theorem VariableState.setResultValues_comm {ctx : WfIRContext OpInfo}
    (hOp : op₁ ≠ op₂) :
    (varState.setResultValues ctx.raw op₁ resValues₁).setResultValues ctx.raw op₂ resValues₂ =
    (varState.setResultValues ctx.raw op₂ resValues₂).setResultValues ctx.raw op₁ resValues₁ := by
  ext val runtimeVal
  cases val <;> grind

theorem VariableState.getVar?_setResultValues_operand_of_dominates {ctx : WfIRContext OpInfo}
    (ctxDom : ctx.Dom) (hdom : op'.dominates op ctx) :
    value ∈ op'.getOperands! ctx.raw →
    (varState.setResultValues ctx.raw op resValues).getVar? value =
    varState.getVar? value := by
  intro valueInOperands
  simp only [VariableState.getVar?_setResultValues]
  have := IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom hdom value valueInOperands
  cases value
  case blockArgument blockArg => grind
  case opResult opRes =>
    simp only [ite_eq_right_iff, and_imp]
    simp only [OperationPtr.getResults!.mem_iff_exists_index, ValuePtr.opResult.injEq, not_exists,
      not_and] at this
    grind [OperationPtr.getResult_def, cases OpResultPtr]

@[grind =>]
theorem VariableState.getOperandValues_setResultValues_of_dominates {ctx : WfIRContext OpInfo}
    (ctxDom : ctx.Dom) (hdom : op'.dominates op ctx) :
    (varState.setResultValues ctx.raw op resValues).getOperandValues ctx.raw op' =
    varState.getOperandValues ctx.raw op' := by
  apply VariableState.getOperandValues_eq_of_getVar?_eq
  grind [VariableState.getVar?_setResultValues_operand_of_dominates]

@[grind =>]
theorem VariableState.getOperandValues_setResultValues_self {ctx : WfIRContext OpInfo}
    (ctxDom : ctx.Dom) :
    (varState.setResultValues ctx.raw op resValues).getOperandValues ctx.raw op =
    varState.getOperandValues ctx.raw op := by
  exact getOperandValues_setResultValues_of_dominates ctxDom OperationPtr.dominates_refl

@[grind = ]
theorem VariableState.setResultValues_setResultValues_self {ctx : WfIRContext OpCode} :
    (varState.setResultValues ctx.raw op resValues).setResultValues ctx.raw op resValues' =
    varState.setResultValues ctx.raw op resValues' := by
  ext val runtimeVal
  simp only [VariableState.getVar?_setResultValues]
  grind
