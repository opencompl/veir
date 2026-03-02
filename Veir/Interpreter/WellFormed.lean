import Veir.Interpreter.Basic

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

/--
  A proposition that states that the interpreter state has the execution of a given operation.
  This means that all the operand and result variables are in the interpreter state, and
  that the result values are correctly computed from the operand values according to the
  semantics of the operation.
-/
def InterpreterState.SatisfiesEquationLemma (state : InterpreterState) (ctx : IRContext OpCode)
    (op : OperationPtr) : Prop :=
  ∃ controlFlow, interpretOp ctx op state = some (state, controlFlow)

/--
  A well-formedness condition for the interpreter state. It states that every operation
  result that is in the state has been computed according to the semantics of its defining
  operation.
-/
def InterpreterState.WellFormed (state : InterpreterState) (ctx : IRContext OpCode) : Prop :=
  ∀ (opRes : OpResultPtr) (opResInBounds : opRes.InBounds ctx),
  ∀ val, state.getVar? opRes = some val →
  state.SatisfiesEquationLemma ctx (opRes.get! ctx).owner

@[grind =]
theorem InterpreterState.getVar?_setVar :
    (InterpreterState.setVar state var' val).getVar? var =
    if var = var' then some val else state.getVar? var := by
  grind [InterpreterState.setVar, InterpreterState.getVar?]

theorem InterpreterState.getVar?_setResultValues_loop
    {state : InterpreterState} {ctx : IRContext OpInfo} {op} {resultValues} {value}:
    (state.setResultValues_loop ctx op resultValues idx).getVar? value =
    match value with
    | .opResult {op := op', index := index} =>
      if op' = op ∧ index < idx then
        some resultValues[index]!
       else
         state.getVar? value
    | _ =>
      state.getVar? value := by
  induction idx generalizing state
  case zero => grind [InterpreterState.setResultValues_loop]
  case succ idx ih =>
    simp only [InterpreterState.setResultValues_loop, ih]
    grind [cases OpResultPtr, OperationPtr.getResult, cases ValuePtr]

@[grind =]
theorem InterpreterState.getVar?_setResultValues
    {ctx : IRContext OpInfo} {state : InterpreterState} {op} {resultValues}
    {value} (valueInBounds : value.InBounds ctx) :
    (state.setResultValues ctx op resultValues).getVar? value =
    match value with
    | .opResult {op := op', index := index} =>
      if op' = op then
        some resultValues[index]!
       else
         state.getVar? value
    | _ =>
      state.getVar? value := by
  simp only [InterpreterState.setResultValues, InterpreterState.getVar?_setResultValues_loop]
  cases value
  next opRes =>
    by_cases opRes.op = op <;> grind
  next =>
    grind

theorem InterpreterState.getVar?_of_interpretOp
    {state : InterpreterState} {op}
    (valueInBounds : value.InBounds ctx) :
    interpretOp ctx op state = some (state', controlFlow) →
    state'.getVar? value =
    match value with
    | .opResult {op := op', index := index} => do
      if op' = op then
        let operands := (state.getOperandValues ctx op).get!
        let opType := op.getOpType! ctx
        let (resultValues, _) ← interpretOp' opType (op.getProperties! ctx opType) ((op.get! ctx).results.map (·.type)) operands
        some resultValues[index]!
       else
         state.getVar? value
    | _ =>
      state.getVar? value := by
  intro h
  simp only [interpretOp, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq] at h
  have ⟨operandValues, hoperandValues, ⟨resValue, cf⟩, hInterp, hstate', hcf⟩ := h; clear h
  simp only at hcf
  subst cf state'
  simp only [InterpreterState.getVar?_setResultValues valueInBounds]
  cases value <;> grind

def InterpreterState.getOperandValues_inj {op} {ctx : IRContext OpInfo} {state state' : InterpreterState} :
    (∀ val, val ∈ op.getOperands! ctx → state.getVar? val = state'.getVar? val) →
    state.getOperandValues ctx op = state'.getOperandValues ctx op := by
  intro h
  simp only [getOperandValues]
  sorry -- Missing lemam in Lean to talk about `mapM`

def InterpreterState.eq_of_interpOp_of_no_results {state : InterpreterState} {op}
    (hNoResults : op.getNumResults! ctx = 0) :
    interpretOp ctx op state = some (state', cf) →
    state = state' := by
  simp [interpretOp, setResultValues, hNoResults, setResultValues_loop, Option.bind_eq_some_iff]

/--
  A proposition that states that the interpreter state has not yet interpreted a given operation.
-/
def InterpreterState.NotIntepreted (state : InterpreterState) (ctx : IRContext OpCode)
    (op : OperationPtr) : Prop :=
  ∀ idx, idx < op.getNumResults! ctx → state.getVar? (op.getResult idx) = none

theorem InterpreterState.SatisfiesEquationLemma_iff_not_NotIntepreted (state : InterpreterState)
    (wf : state.WellFormed ctx) (ctxWF : ctx.WellFormed)
    (op : OperationPtr) (opInBounds : op.InBounds ctx) (hasResults : op.getNumResults! ctx ≠ 0) :
    state.SatisfiesEquationLemma ctx op ↔ ¬ state.NotIntepreted ctx op := by
  simp only [InterpreterState.SatisfiesEquationLemma, InterpreterState.NotIntepreted]
  constructor
  · rintro ⟨controlFlow, hEqLemma'⟩ hNotInterp
    have hNotInterp := hNotInterp 0 (by grind)
    have : (op.getResult 0).InBounds ctx := by grind
    have hinterp := getVar?_of_interpretOp (value := op.getResult 0) (by grind) hEqLemma'
    simp only [hNotInterp, OperationPtr.getResult_op, ↓reduceIte, OperationPtr.getResult_index,
      Option.bind_eq_bind] at hinterp
    sorry -- Missing lemma about getOperandValues
  · simp only [Classical.not_forall, forall_exists_index, Option.ne_none_iff_exists]
    intro idx hidx value hvalue
    simp only [WellFormed] at wf
    have hEqLemma := wf (op.getResult idx) (by grind) value (by grind)
    simp only [InterpreterState.SatisfiesEquationLemma] at hEqLemma
    grind [IRContext.WellFormed, Operation.WellFormed]

theorem InterpreterState.SatisfiesEquationLemma_or_not_NotIntepreted {state : InterpreterState}
    (wf : state.WellFormed ctx) (ctxWF : ctx.WellFormed)
    {op : OperationPtr} (opInBounds : op.InBounds ctx)
    (hasResults : op.getNumResults! ctx ≠ 0) :
    state.SatisfiesEquationLemma ctx op ∨ state.NotIntepreted ctx op := by
  by_cases hEqLemma : state.SatisfiesEquationLemma ctx op
  · grind
  · grind [InterpreterState.SatisfiesEquationLemma_iff_not_NotIntepreted]

theorem interpretOp_satisfiesEquationLemma_self
    {state : InterpreterState} (wf : state.WellFormed ctx) {op}:
    interpretOp ctx op state = some (state', controlFlow) →
    state'.SatisfiesEquationLemma ctx op := by
  sorry -- This needs the fact that an operation result is not one of its operands

theorem interpretOp_satisfiesEquationLemma
    {state : InterpreterState} (wf : state.WellFormed ctx) (ctxWF : ctx.WellFormed)
    {op} (opInBounds : op.InBounds ctx) :
    interpretOp ctx op state = some (state', controlFlow) →
    state.SatisfiesEquationLemma ctx op' →
    state'.SatisfiesEquationLemma ctx op' := by
  intro hInterp hEqLemma
  by_cases hEq : op = op'
  · subst op
    grind [interpretOp_satisfiesEquationLemma_self]
  · by_cases hNumResults : op.getNumResults! ctx = 0
    · have := @InterpreterState.eq_of_interpOp_of_no_results
      grind
    · cases InterpreterState.SatisfiesEquationLemma_or_not_NotIntepreted wf ctxWF opInBounds hNumResults
      next hEqLemma' => grind [InterpreterState.SatisfiesEquationLemma]
      next hNotInterp =>
        simp [InterpreterState.SatisfiesEquationLemma] at ⊢ hEqLemma
        have ⟨controlFlow, hEqLemma'⟩ := hEqLemma; clear hEqLemma
        exists controlFlow
        simp only [interpretOp, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at ⊢ hEqLemma'
        have ⟨operandVal, hOperandVal, ⟨resVal, cf⟩, hResVal, hEqLemma⟩ := hEqLemma'; clear hEqLemma'
        simp only [Option.some.injEq, Prod.mk.injEq] at hEqLemma
        have ⟨hState, _⟩ := hEqLemma; clear hEqLemma
        subst cf
        exists operandVal
        have : (∀ val, val ∈ op'.getOperands! ctx → state'.getVar? val = state.getVar? val) := by sorry
        simp only [InterpreterState.getOperandValues_inj this, hOperandVal, Option.some.injEq,
          Prod.mk.injEq, Prod.exists, exists_eq_right_right, true_and]
        exists resVal
        simp only [hResVal, true_and]
        ext var value
        rw [InterpreterState.getVar?_setResultValues]
        · sorry
        · sorry
