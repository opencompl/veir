import Veir.Interpreter.Basic
import Veir.Dominance
import Veir.Interpreter.Refinement.Basic

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}
variable {varState varState' : VariableState ctx}
variable {state state' : InterpreterState ctx}
variable {op op' : OperationPtr}

@[grind =]
theorem Variable.setVar?_eq_some_setVar (h : val.Conforms (var.getType! ctx.raw)) :
    varState.setVar? var val inBounds = some (varState.setVar var val h inBounds) := by
  grind [VariableState.setVar?, VariableState.setVar]

theorem VariableState.setVar?_eq_none_iff_of_varState
    (varState₂ : VariableState ctx) :
    varState.setVar? var' val inBounds = none ↔ varState₂.setVar? var' val = none := by
  grind [VariableState.setVar?]

theorem VariableState.setResultValues?_loop_eq_none_iff_of_varState
    (varState₂ : VariableState ctx) :
    varState.setResultValues?_loop op resValues idx inBounds hi = none ↔
    varState₂.setResultValues?_loop op resValues idx = none := by
  induction idx generalizing varState varState₂ with
  | zero => grind [setResultValues?_loop]
  | succ i ih =>
    simp [setResultValues?_loop, Option.bind]
    grind [VariableState.setVar?_eq_none_iff_of_varState]

theorem VariableState.setResultValues?_eq_none_iff_of_varState
    (varState₂ : VariableState ctx) :
    varState.setResultValues? op resValues inBounds = none ↔
    varState₂.setResultValues? op resValues = none := by
  simp only [setResultValues?]
  grind [VariableState.setResultValues?_loop_eq_none_iff_of_varState]

theorem VariableState.setVar?_eq_some_of_varState
    (varState₂ : VariableState ctx) :
    varState.setVar? var' val inBounds = some varStateA →
    ∃ varStateB, varState₂.setVar? var' val = some varStateB := by
  grind [VariableState.setVar?]

theorem VariableState.setResultValues?_loop_eq_some_of_varState
    (varState₂ : VariableState ctx) :
    varState.setResultValues?_loop op resValues idx inBounds hi = some varStateA →
    ∃ varStateB, varState₂.setResultValues?_loop op resValues idx = some varStateB := by
  cases hc : varState₂.setResultValues?_loop op resValues idx
  · grind [VariableState.setResultValues?_loop_eq_none_iff_of_varState]
  · grind

theorem VariableState.setResultValues?_eq_some_of_varState
    (varState₂ : VariableState ctx) :
    varState.setResultValues? op resValues inBounds = some varStateA →
    ∃ varStateB, varState₂.setResultValues? op resValues = some varStateB := by
  rcases hc : varState₂.setResultValues? op resValues
  · grind [VariableState.setResultValues?_eq_none_iff_of_varState]
  · grind

@[grind =>]
theorem VariableState.getVar?_of_setVar? :
    VariableState.setVar? varState var' val inBounds = some varState' →
    varState'.getVar? var =
    if var = var' then some val else varState.getVar? var := by
  grind [VariableState.setVar?, VariableState.getVar?]

@[grind =]
theorem VariableState.getVar?_of_setVar :
    VariableState.getVar? (varState.setVar var' val h inBounds) var =
    if var = var' then some val else varState.getVar? var := by
  grind [VariableState.setVar, VariableState.getVar?]

theorem VariableState.getVar?_setResultValues?_loop :
    varState.setResultValues?_loop op resultValues idx inBounds hi = some varState' →
    varState'.getVar? value =
    match value with
    | .opResult {op := op', index := index} =>
      if op' = op ∧ index < idx then
        some resultValues[index]!
       else
        varState.getVar? value
    | _ =>
      varState.getVar? value := by
  fun_induction VariableState.setResultValues?_loop
  next => grind
  next =>
    simp only [Option.bind_eq_bind, Nat.succ_eq_add_one, Option.bind]
    grind [cases OpResultPtr, OperationPtr.getResult_def, cases ValuePtr]

@[grind =>]
theorem VariableState.getVar?_setResultValues? :
    varState.setResultValues? op resultValues inBounds = some varState' →
    varState'.getVar? value =
    match value with
    | .opResult {op := op', index := index} =>
      if op' = op ∧ index < op.getNumResults! ctx.raw then
        some resultValues[index]!
       else
         varState.getVar? value
    | _ =>
      varState.getVar? value := by
  grind [VariableState.setResultValues?, VariableState.getVar?_setResultValues?_loop]

theorem VariableState.getVar?_setResultValues?_of_notMem_getResults! {value resultValues} :
    value ∉ op.getResults! ctx.raw →
    varState.setResultValues? op resultValues inBounds = some varState' →
    varState'.getVar? value = varState.getVar? value := by
  intro hNotMemResults hSetResults
  simp only [VariableState.getVar?_setResultValues? hSetResults]
  rcases value with ⟨op₂, index⟩ | _
  · simp only [OperationPtr.getResults!.mem_iff_exists_index, ValuePtr.opResult.injEq, not_exists,
    not_and] at hNotMemResults
    grind [OperationPtr.getResult_def]
  · grind

grind_pattern VariableState.getVar?_setResultValues?_of_notMem_getResults! =>
  op.getResults! ctx, varState.setResultValues? op resultValues, varState'.getVar? value

@[grind =>]
theorem VariableState.getVar?_setResultValues?_of_value_inBounds
    (valueInBounds : value.InBounds ctx.raw) :
    varState.setResultValues? op resultValues inBounds = some varState' →
    varState'.getVar? value =
    match value with
    | .opResult {op := op', index := index} =>
      if op' = op then
        some resultValues[index]!
       else
         varState.getVar? value
    | _ =>
      varState.getVar? value := by
  intro h
  simp only [getVar?_setResultValues? h]
  cases value <;> grind

theorem interpretOp_some_iff {ctx : WfIRContext OpCode} {state state' : InterpreterState ctx}
  {inBounds : op.InBounds ctx.raw} :
  interpretOp op state inBounds = some (.ok (state', cf)) ↔
  ∃ operandValues resValues mem' varState',
    (state.variables.getOperandValues op) = some operandValues ∧
    interpretOp' (op.getOpType! ctx.raw) (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
      (op.getResultTypes! ctx.raw) operandValues (op.getSuccessors! ctx.raw) state.memory =
      some (.ok (resValues, mem', cf)) ∧
    state.variables.setResultValues? op resValues = some varState' ∧
    state' = ⟨varState', mem'⟩ := by
  simp only [interpretOp, bind, pure, liftM, monadLift, MonadLift.monadLift]
  grind

theorem VariableState.getOperandValues_eq_of_getVar?_eq :
    (∀ val, val ∈ op.getOperands! ctx.raw → varState.getVar? val = varState'.getVar? val) →
    varState.getOperandValues op = varState'.getOperandValues op := by
  intro h
  simp only [getOperandValues, Array.mapM_eq_mapM_toList]
  suffices H : ∀ (l : List _), (∀ val ∈ l, varState.getVar? val = varState'.getVar? val) →
               l.mapM varState.getVar? = l.mapM varState'.getVar? by grind
  intro l hl
  induction l <;> grind

theorem VariableState.setResultValues?_comm
    (hOp : op₁ ≠ op₂) :
    varState.setResultValues? op₁ resValues₁ inBounds₁ = some varState' →
    varState'.setResultValues? op₂ resValues₂ inBounds₂ = some varState'' →
    ∃ varState₂, varState.setResultValues? op₂ resValues₂ inBounds₂ = some varState₂ ∧
    varState₂.setResultValues? op₁ resValues₁ inBounds₁ = some varState'' := by
  intros h₁ h₂
  have ⟨varState₂, hvs₂⟩ := setResultValues?_eq_some_of_varState varState h₂
  have ⟨varState₂', hvs₂'⟩ := setResultValues?_eq_some_of_varState varState₂ h₁
  exists varState₂
  constructor; grind
  simp only [hvs₂', Option.some.injEq]
  ext val value
  cases val <;> grind [getVar?_setResultValues?]

theorem VariableState.getVar?_setResultValues?_operand_of_dominates
    (ctxDom : ctx.Dom) (hdom : op'.dominates op ctx) :
    value ∈ op'.getOperands! ctx.raw →
    varState.setResultValues? op resValues inBounds = some varState' →
    varState'.getVar? value =
    varState.getVar? value := by
  intro valueInOperands h
  simp only [VariableState.getVar?_setResultValues? h]
  have := IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom hdom value valueInOperands
  cases value
  case blockArgument blockArg => grind
  case opResult opRes =>
    simp only [ite_eq_right_iff, and_imp]
    simp only [OperationPtr.getResults!.mem_iff_exists_index, ValuePtr.opResult.injEq, not_exists,
      not_and] at this
    grind [OperationPtr.getResult_def, cases OpResultPtr]

@[grind =>]
theorem VariableState.getOperandValues_setResultValues?_of_dominates
    (ctxDom : ctx.Dom) (hdom : op'.dominates op ctx) :
    varState.setResultValues? op resValues inBounds = some varState' →
    varState'.getOperandValues op' = varState.getOperandValues op' := by
  intro h
  apply VariableState.getOperandValues_eq_of_getVar?_eq
  grind [VariableState.getVar?_setResultValues?_operand_of_dominates]

@[grind =>]
theorem VariableState.getOperandValues_setResultValues?_self
    (ctxDom : ctx.Dom) :
    (varState.setResultValues? op resValues inBounds) = varState' →
    varState'.getOperandValues op = varState.getOperandValues op := by
  exact getOperandValues_setResultValues?_of_dominates ctxDom OperationPtr.dominates_refl

@[grind =>]
theorem VariableState.setResultValues?_setResultValues?_self :
    varState.setResultValues? op resValues inBounds = some varState' →
    varState'.setResultValues? op resValues' inBounds' =
    varState.setResultValues? op resValues' inBounds' := by
  intro h
  rcases hopt : varState.setResultValues? op resValues' with _ | vs2
  · grind [VariableState.setResultValues?_eq_none_iff_of_varState]
  · have ⟨varState₂, hvs₂⟩ := setResultValues?_eq_some_of_varState varState' hopt
    simp only [hvs₂, Option.some.injEq]
    ext
    grind [VariableState.getVar?_setResultValues?]

section interpretOpList

variable {ctx : WfIRContext OpCode}
variable {state : InterpreterState ctx}

@[simp, grind =]
theorem interpretOpList_nil :
    interpretOpList [] state inBounds = some (.ok (state, none)) := by
  simp [interpretOpList, pure]

theorem interpretOpList_cons :
    interpretOpList (op :: l) state inBounds =
    match interpretOp op state with
    | none => none
    | some .ub => some .ub
    | some (.ok (state', none)) => interpretOpList l state' (by grind)
    | some (.ok (state', some cf)) => some (.ok (state', some cf)) := by
  simp [interpretOpList, bind, pure]
  grind

theorem interpretOpList_append :
    interpretOpList (l₁ ++ l₂) state inBounds =
    match interpretOpList l₁ state (by grind) with
    | some (.ok (state', none)) => interpretOpList l₂ state' (by grind)
    | some (.ok (state', some cf)) => some (.ok (state', some cf))
    | some .ub => some .ub
    | none => none := by
  induction l₁ generalizing state
  · simp
  · grind [interpretOpList_cons]

@[simp, grind =]
theorem interpretTerminatedOpList_nil :
    interpretTerminatedOpList [] state inBounds = none := by
  simp [interpretTerminatedOpList, interpretOpList_nil, bind]

theorem interpretTerminatedOpList_cons {ctx : WfIRContext OpCode}
    {op : OperationPtr} {l : List OperationPtr}
    {state : InterpreterState ctx}
    {inBounds : ∀ op' ∈ op :: l, op'.InBounds ctx.raw} :
    interpretTerminatedOpList (op :: l) state inBounds =
    match interpretOp op state with
    | none => none
    | some .ub => some .ub
    | some (.ok (state', none)) => interpretTerminatedOpList l state' (by grind)
    | some (.ok (state', some cf)) => some (.ok (state', cf)) := by
  simp [interpretTerminatedOpList, interpretOpList_cons, bind, pure]
  grind

theorem interpretTerminatedOpList_append :
    interpretTerminatedOpList (l₁ ++ l₂) state inBounds =
    match interpretOpList l₁ state (by grind) with
    | some (.ok (state', none)) => interpretTerminatedOpList l₂ state' (by grind)
    | some (.ok (state', some cf))=> some (.ok (state', cf))
    | some .ub => some .ub
    | none => none := by
  simp [interpretTerminatedOpList, interpretOpList_append, bind, pure]
  grind

theorem interpretOpChain_of_next!_eq_some {state' : InterpreterState ctx}
    (hnext : (op.get! ctx.raw).next = some op') :
    interpretOpChain op state' inBounds =
    match interpretOp op state' (by grind) with
    | none => none
    | some .ub => some .ub
    | some (.ok (state'', none)) => interpretOpChain op' state'' (by grind)
    | some (.ok (state'', some cf)) => some (.ok (state'', cf)) := by
  rw [interpretOpChain]
  simp [bind, pure]
  grind

theorem interpretOpChain_of_next!_eq_none {state' : InterpreterState ctx}
    (hnext : (op.get! ctx.raw).next = none) :
    interpretOpChain op state' inBounds =
    match interpretOp op state' (by grind) with
    | none => none
    | some .ub => some .ub
    | some (.ok (_, none)) => none
    | some (.ok (state'', some cf)) => some (.ok (state'', cf)) := by
  rw [interpretOpChain]
  simp [bind, pure]
  grind

@[simp, grind =]
theorem Laeu {l : Array α} : List.drop l.size l.toList = [] := by
  induction l <;> simp

theorem interpretOpChain_getElem_array_eq_interpretTerminatedOpList_of_opChain
    (hchain : BlockPtr.OpChain block ctx.raw array) (n : Nat) :
    ∀ (i : Nat) (state' : InterpreterState ctx)
      (_hni : i + n = array.size) (hi : i < array.size),
      interpretOpChain array[i] state' (hchain.arrayInBounds (Array.getElem_mem hi)) =
      interpretTerminatedOpList (array.toList.drop i) state' (by grind [BlockPtr.OpChain]) := by
  induction n
  case zero => grind
  case succ n ih =>
    intros i state' hni hi
    have hnext := hchain.next hi
    grind [interpretOpChain_of_next!_eq_none, interpretOpChain_of_next!_eq_some,
      interpretTerminatedOpList_cons, List.drop_eq_getElem_cons]

theorem interpretOpChain_eq_interpretTerminatedOpList_of_firstOp
    {block : BlockPtr} (blockInBounds : block.InBounds ctx.raw) :
    (block.get! ctx.raw).firstOp = some op →
    interpretOpChain op state opInBounds =
    interpretTerminatedOpList (block.operationList ctx.raw).toList state
      (by grind [BlockPtr.operationListWF, BlockPtr.OpChain]) := by
  intro hfirst
  have hchain := BlockPtr.operationListWF ctx.raw block blockInBounds ctx.wellFormed
  have := interpretOpChain_getElem_array_eq_interpretTerminatedOpList_of_opChain hchain
    (block.operationList ctx.raw).size 0 state (by omega) (by grind [BlockPtr.OpChain])
  grind [BlockPtr.OpChain]

end interpretOpList

set_option warn.sorry false in
def interpretOp'_monotone {operands operands' : Array RuntimeValue} :
    operands ⊒ operands' →
    Interp.isRefinedBy (α := Array RuntimeValue × MemoryState × Option ControlFlowAction)
      (fun r₁ r₂ => r₁.1 ⊒ r₂.1 ∧ r₁.2 = r₂.2)
      (interpretOp' opType properties resultTypes operands blockOperands mem)
      (interpretOp' opType properties resultTypes operands' blockOperands mem) := by
  sorry
