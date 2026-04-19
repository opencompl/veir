import Veir.Interpreter.Basic

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {state state' : InterpreterState}

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
  interpretOp ctx op state = some (state', cf) ↔
  ∃ operandValues resValues,
    (state.getOperandValues ctx op) = some operandValues ∧
    interpretOp' (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
      ((op.get! ctx).results.map (·.type)) operandValues = some (resValues, cf) ∧
    state' = state.setResultValues ctx op resValues := by
  simp only [interpretOp, bind, Option.bind]
  grind

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
