import Veir.Interpreter.Basic
import Veir.Dominance
import Veir.Interpreter.Refinement.Basic
import Veir.Interpreter.Refinement.Lemmas
import Veir.Verifier

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx' : WfIRContext OpInfo}
variable {varState varState' : VariableState ctx}
variable {state state' : InterpreterState ctx}
variable {op op' : OperationPtr}

/-- The value stored for `var` conforms to `var`'s type. -/
theorem VariableState.getVar?_conforms {ctx : WfIRContext OpInfo} {state : VariableState ctx}
    {var : ValuePtr} {val : RuntimeValue} (h : state.getVar? var = some val) :
    val.Conforms (var.getType! ctx.raw) := by
  grind [VariableState.getVar?, state.conforms var val]

/-- The operand values gathered by `getOperandValues` conform to `op`'s declared operand types. -/
theorem VariableState.getOperandValues_conforms
    (h : varState.getOperandValues op = some values) :
    RuntimeValue.ArrayConforms values (op.getOperandTypes! ctx.raw) := by
  simp only [VariableState.getOperandValues] at h
  simp only [RuntimeValue.ArrayConforms]
  constructor; grind
  intro i hi
  grind [VariableState.getVar?_conforms, Array.mapM_option_eq_some_implies h i (by grind)]

@[grind =]
theorem VariableState.setVar?_eq_some_setVar (h : val.Conforms (var.getType! ctx.raw)) :
    varState.setVar? var val inBounds = some (varState.setVar var val h inBounds) := by
  grind [VariableState.setVar?, VariableState.setVar]

/-- `setVar?` succeeds iff the value conforms to the variable's type -/
theorem RuntimeValue.Conforms_iff_setVar?_eq_some :
    val.Conforms (var.getType! ctx.raw) ↔
    (∃ varState', varState.setVar? var val inBounds = some varState') := by
  simp only [VariableState.setVar?]
  constructor
  · intro h; simp [h]
  · grind

@[grind .]
theorem RuntimeValue.Conforms_of_setVar?_eq_some :
    varState.setVar? var val inBounds = some varState' →
    val.Conforms (var.getType! ctx.raw) := by
  grind [VariableState.setVar?]

theorem VariableState.setVar?_eq_none_iff_of_varState
    (varState₂ : VariableState ctx) :
    varState.setVar? var' val inBounds = none ↔ varState₂.setVar? var' val = none := by
  grind [VariableState.setVar?]

theorem VariableState.setResultValues?_loop_eq_none_iff_of_varState
    (varState₂ : VariableState ctx) :
    varState.setResultValues?_loop op resValues idx inBounds hi hsize = none ↔
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
    varState.setResultValues?_loop op resValues idx inBounds hi hsize = some varStateA →
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
    varState.setResultValues?_loop op resultValues idx inBounds hi hsize = some varState' →
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

/-- `op` operation results are exactly the values set by `setResultValues? op` in the new state. -/
theorem VariableState.getVar?_getResult_of_setResultValues? :
    i < op.getNumResults! ctx.raw →
    varState.setResultValues? op resultValues inBounds = some varState' →
    varState'.getVar? (op.getResult i) = resultValues[i]! := by
  intro hNotMemResults hSetResults
  simp only [VariableState.getVar?_setResultValues? hSetResults]
  grind

grind_pattern VariableState.getVar?_getResult_of_setResultValues? =>
  i < op.getNumResults! ctx.raw, varState.setResultValues? op resultValues,
  varState'.getVar? (op.getResult i)

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

/--
Assert equality between two `interpretOp'` calls that have the same operation type and properties.
This lemma is useful to avoid introducing extra casts on the `interpretOp'` arguments.
-/
theorem interpretOp'_opType_cast
    (hOpType : opType = opType')
    (hProps : props = hOpType ▸ props') :
    interpretOp' opType props resultTypes operands successors mem =
    interpretOp' opType' props' resultTypes operands successors mem := by
  subst opType
  grind

theorem interpretOp_some_iff {ctx : WfIRContext OpCode} {state state' : InterpreterState ctx}
  {inBounds : op.InBounds ctx.raw} :
  interpretOp op state inBounds = some (.ok (state', cf)) ↔
  ∃ operandValues resValues mem' varState',
    (state.variables.getOperandValues op) = some operandValues ∧
    op.interpret ctx operandValues state.memory = some (.ok (resValues, mem', cf)) ∧
    state.variables.setResultValues? op resValues = some varState' ∧
    state' = ⟨varState', mem'⟩ := by
  simp only [interpretOp, bind, pure, liftM, monadLift, MonadLift.monadLift]
  grind

/--
Given that getting the operands from the interpreter state succeeds, interpreting an operation
with `interpretOp` returns `ok` iff interpreting the operation with `interpretOp'` returns `ok` and
setting the result values in the state succeeds.
-/
theorem interpretOp_ok_iff_of_getOperandValues_eq_some
  {ctx : WfIRContext OpCode} {state state' : InterpreterState ctx} {inBounds : op.InBounds ctx.raw}
  (hoperandValues : state.variables.getOperandValues op = some operandValues) :
  interpretOp op state inBounds = some (.ok (state', cf)) ↔
  ∃ resValues,
    op.interpret ctx operandValues state.memory = some (.ok (resValues, state'.memory, cf)) ∧
    state.variables.setResultValues? op resValues = some state'.variables := by
  simp only [interpretOp, hoperandValues, bind, pure, liftM, monadLift, MonadLift.monadLift]
  grind [cases InterpreterState]

/--
If interpreting an operation triggers `ub`, then we know that the operands were correctly fetched,
and that the underlying `interpretOp'` call triggered `ub`.
-/
theorem interpretOp_ub_iff {ctx : WfIRContext OpCode} {state : InterpreterState ctx}
  {inBounds : op.InBounds ctx.raw} :
  interpretOp op state inBounds = some .ub ↔
  ∃ operandValues,
    (state.variables.getOperandValues op) = some operandValues ∧
    op.interpret ctx operandValues state.memory = some .ub := by
  simp only [interpretOp, bind, pure, liftM, monadLift, MonadLift.monadLift]
  grind

/-- `interpretOp` is `ub` iff `interpretOp'` is `ub` if the operands are correctly fetched from
the variable state. -/
theorem interpretOp_ub_iff_op_interpret_of_getOperandValues_eq_some
  {ctx : WfIRContext OpCode} {state : InterpreterState ctx} {inBounds : op.InBounds ctx.raw}
  (hoperandValues : state.variables.getOperandValues op = some operandValues) :
  interpretOp op state inBounds = some .ub ↔
  op.interpret ctx.raw operandValues state.memory = some .ub := by
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

/-- Getting `op` operands from the variable state returns an `array` of values iff `array` has
the same size as the number of operands, and each operand value maps to the `array` elements. -/
theorem VariableState.getOperandValues_eq_some_iff :
    (varState.getOperandValues op = some array ↔
    op.getNumOperands! ctx.raw = array.size ∧
    (∀ i, i < op.getNumOperands! ctx.raw →
      varState.getVar? (op.getOperand! ctx.raw i) = some array[i]!)) := by
  simp only [VariableState.getOperandValues]
  grind [Array.mapM_eq_some_iff_of_size_eq]

@[grind →]
theorem VariableState.setResultValues?.getNumRseults!_eq_size :
    varState.setResultValues? op resValues inBounds = some varState' →
    op.getNumResults! ctx.raw = resValues.size := by
  grind [VariableState.setResultValues?]

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

/-! ## Conformance and VariableState -/

/-- `setResultValues?_loop` succeeds iff every result value it binds conforms to its result type. -/
theorem RuntimeValue.ArrayConforms_iff_setResultValues?_loop_eq_some :
    RuntimeValue.ArrayConforms (resValues.take idx) ((op.getResultTypes! ctx.raw).take idx) ↔
    (∃ v, varState.setResultValues?_loop op resValues idx inBounds hi hsize = some v) := by
  fun_induction VariableState.setResultValues?_loop
  next => simp [RuntimeValue.ArrayConforms]
  next varState hsize hOpIn k hkBound result value ih =>
    rw [RuntimeValue.ArrayConforms.take_succ_eq (by grind) (by grind)]
    simp only [Option.bind_eq_bind]
    constructor
    · rintro ⟨hv, hconform⟩
      rw [VariableState.setVar?_eq_some_setVar (by grind)]
      simp only [Option.bind_some]
      grind [ih (varState.setVar (ValuePtr.opResult result) value)]
    · rintro ⟨v, hv⟩
      simp only [Option.bind_eq_some_iff] at hv
      have ⟨varState', hvarState', hv⟩ := hv
      grind [ih varState']

/-- `setResultValues?` succeeds iff every result value conforms to its result type. -/
theorem VariableState.setResultValues?_isSome_iff_conforms (varState : VariableState ctx) inBounds :
    RuntimeValue.ArrayConforms resValues (op.getResultTypes! ctx.raw) ↔
    (∃ v, varState.setResultValues? op resValues inBounds = some v) := by
  simp only [setResultValues?]
  split
  · rw [←RuntimeValue.ArrayConforms_iff_setResultValues?_loop_eq_some]
    simp only [Array.take_eq_extract]
    rw [Array.extract_eq_self_of_le (by grind), Array.extract_eq_self_of_le (by grind)]
  · grind [RuntimeValue.ArrayConforms]

/--
  If `setResultValues?` succeeds, then the runtime values conform to the operation result types, if there is
  as many result values as result types.
-/
@[grind .]
theorem RuntimeValue.ArrayConforms_of_setResultValues?_eq_some
    (h : varState.setResultValues? op resValues inBounds = some varState') :
    RuntimeValue.ArrayConforms resValues (op.getResultTypes! ctx.raw) := by
  rw [VariableState.setResultValues?_isSome_iff_conforms (inBounds := inBounds) (varState := varState)]
  grind

/--
Given that `OperationPtr.interpret` succeeds, that the operands are available in the interpreter
state, and that the result values conform to the operation's result types, then `interpretOp`
succeeds, and the variables in the resulting state are exactly the result values o
`OperationPtr.interpret`.
-/
theorem interpretOp_forward
    {ctx : WfIRContext OpCode} {op : OperationPtr} {state : InterpreterState ctx}
    {inBounds : op.InBounds ctx.raw} {vals results : Array RuntimeValue} {mem' : MemoryState}
    (hVals : state.variables.getOperandValues op = some vals)
    (hInterp : op.interpret ctx vals state.memory = some (.ok (results, mem', none)))
    (hConf : RuntimeValue.ArrayConforms results (op.getResultTypes! ctx.raw)) :
    ∃ state', interpretOp op state inBounds = some (.ok (state', none)) ∧
      state'.memory = mem' ∧
      state.variables.setResultValues? op results = some state'.variables := by
  obtain ⟨varState', hSet⟩ :=
    (VariableState.setResultValues?_isSome_iff_conforms state.variables inBounds).mp hConf
  have hsize : op.getNumResults! ctx.raw = results.size := by grind
  exists ⟨varState', mem'⟩
  grind [interpretOp_ok_iff_of_getOperandValues_eq_some]

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
/-- An operation that verifies does not fail interpretation as long as the operands conform to
the declared operand types. -/
theorem exists_interpretOp'_eq_some {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opInBounds : op.InBounds ctx.raw} (opVerify : OperationPtr.Verified ctx op opInBounds)
    (operandConforms : RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw))
    (mem : MemoryState) :
  ∃ res, op.interpret ctx.raw operands mem = some res := by sorry

/-- The relation `interpretOp'_monotone` establishes between two interpretation results. -/
abbrev InterpretResultIsRefinedBy :
    Array RuntimeValue × MemoryState × Option ControlFlowAction →
    Array RuntimeValue × MemoryState × Option ControlFlowAction → Prop :=
  fun r₁ r₂ => r₁.1 ⊒ r₂.1 ∧ r₁.2.1 = r₂.2.1 ∧
    ControlFlowAction.optionIsRefinedBy r₁.2.2 r₂.2.2

/-- `InterpretResultIsRefinedBy` is reflexive, so an interpretation result always refines itself. -/
@[grind .]
theorem interpretResult_isRefinedBy_refl
    (x : Interp (Array RuntimeValue × MemoryState × Option ControlFlowAction)) :
    Interp.isRefinedBy InterpretResultIsRefinedBy x x := by
  rcases x with _ | (x | _) <;> grind [Interp.isRefinedBy]

/--
A register runtime value can only be refined by itself, so operand arrays that consist purely of
registers are refined only by themselves. This makes every dialect whose operands are registers
(`riscv`, `riscv_cf`, `riscv_stack`, `rv64`) monotone for free: the refined operands are the
original ones, so both sides interpret to the very same result.
-/
theorem RuntimeValue.eq_of_arrayIsRefinedBy_of_regs {a b : Array RuntimeValue}
    (h : a ⊒ b) (hregs : ∀ v ∈ a, ∃ r, v = .reg r) : b = a := by
  obtain ⟨hsize, helem⟩ := h
  apply Array.ext hsize.symm
  intro i hib hia
  obtain ⟨r, hr⟩ := hregs a[i] (Array.getElem_mem hia)
  have hrefines := helem i hia
  rw [getElem!_pos a i hia, getElem!_pos b i hib, hr] at hrefines
  rw [hr]
  exact RuntimeValue.reg_of_isRefinedBy hrefines

/-- Destructure a refined one-element operand array. -/
theorem RuntimeValue.arrayIsRefinedBy_one {a b : Array RuntimeValue} {x : RuntimeValue}
    (h : a ⊒ b) (ha : a.toList = [x]) :
    ∃ x', b.toList = [x'] ∧ x ⊒ x' := by
  have ha2 : a = #[x] := Array.ext' (by simp [ha])
  subst ha2
  obtain ⟨hsize, helem⟩ := h
  simp at hsize
  have hlen : b.toList.length = 1 := by rw [Array.length_toList]; omega
  match hb : b.toList with
  | [x'] =>
    have hb2 : b = #[x'] := Array.ext' (by simp [hb])
    subst hb2
    have h0 := helem 0 (by simp)
    simp at h0
    exact ⟨x', by simp, h0⟩
  | [] => rw [hb] at hlen; simp at hlen
  | _ :: _ :: _ => rw [hb] at hlen; simp at hlen

/-- Destructure a refined two-element operand array. -/
theorem RuntimeValue.arrayIsRefinedBy_two {a b : Array RuntimeValue} {x y : RuntimeValue}
    (h : a ⊒ b) (ha : a.toList = [x, y]) :
    ∃ x' y', b.toList = [x', y'] ∧ x ⊒ x' ∧ y ⊒ y' := by
  have ha2 : a = #[x, y] := Array.ext' (by simp [ha])
  subst ha2
  obtain ⟨hsize, helem⟩ := h
  simp at hsize
  have hlen : b.toList.length = 2 := by rw [Array.length_toList]; omega
  match hb : b.toList with
  | [x', y'] =>
    have hb2 : b = #[x', y'] := Array.ext' (by simp [hb])
    subst hb2
    have h0 := helem 0 (by simp)
    have h1 := helem 1 (by simp)
    simp at h0 h1
    exact ⟨x', y', by simp, h0, h1⟩
  | [] => rw [hb] at hlen; simp at hlen
  | [_] => rw [hb] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [hb] at hlen; simp at hlen

/-- `Array.extract` preserves operand refinement (used for branch arguments). -/
theorem RuntimeValue.arrayIsRefinedBy_extract {a b : Array RuntimeValue} (h : a ⊒ b) (i j : Nat) :
    a.extract i j ⊒ b.extract i j := by
  obtain ⟨hsize, helem⟩ := h
  refine ⟨by simp [hsize], ?_⟩
  intro k hk
  simp only [Array.size_extract] at hk
  have hka : i + k < a.size := by omega
  have hkb : i + k < b.size := by omega
  rw [getElem!_pos _ k (by simp only [Array.size_extract]; omega),
      getElem!_pos _ k (by simp only [Array.size_extract]; omega)]
  simp only [Array.getElem_extract]
  have := helem (i + k) hka
  rwa [getElem!_pos a _ hka, getElem!_pos b _ hkb] at this

/-- A refined operand array agrees on `getElem?`, up to refinement of the element. -/
theorem RuntimeValue.arrayIsRefinedBy_getElem? {a b : Array RuntimeValue} (h : a ⊒ b) {i : Nat}
    {v : RuntimeValue} (hv : a[i]? = some v) : ∃ w, b[i]? = some w ∧ v ⊒ w := by
  obtain ⟨hsize, helem⟩ := h
  have hia : i < a.size := by
    rcases Nat.lt_or_ge i a.size with hlt | hge
    · exact hlt
    · rw [Array.getElem?_eq_none hge] at hv
      exact absurd hv (by simp)
  have hib : i < b.size := by omega
  have hveq : a[i] = v := by
    rw [Array.getElem?_eq_getElem hia] at hv
    exact Option.some.inj hv
  refine ⟨b[i], by rw [Array.getElem?_eq_getElem hib], ?_⟩
  have := helem i hia
  rwa [getElem!_pos a _ hia, getElem!_pos b _ hib, hveq] at this

set_option warn.sorry false in
/--
`Llvm.interpretOp'` is monotone in its operands, except for `llvm.store`.

`llvm.store` is genuinely *not* monotone for this relation, which requires the resulting memories
to be *equal*: storing a poison value empoisons the target bytes (`MemoryState.empoison`), while
storing the concrete value that refines it writes those bytes and clears their poison mask
(`MemoryState.store`). Both stores succeed, but the two memories differ, so the relation fails.
Monotonicity of `llvm.store` would need the resulting memories to be related by
`MemoryState.isRefinedBy` rather than by equality.
-/
theorem Llvm.interpretOp'_monotone {operands operands' : Array RuntimeValue}
    (notStore : opType ≠ Llvm.store) :
    operands ⊒ operands' →
    Interp.isRefinedBy InterpretResultIsRefinedBy
      (Llvm.interpretOp' opType properties resultTypes operands blockOperands mem)
      (Llvm.interpretOp' opType properties resultTypes operands' blockOperands mem) := by
  sorry

/--
`Riscv.interpretOp'` is monotone in its operands.

RISC-V operands are registers, which carry no poison, so refinement on them is equality: either
every operand is a register -- and then the refined operands are the original ones and both sides
interpret to the very same result -- or some operand is not a register, and every opcode that
reads its operands fails to interpret (opcodes that ignore their operands, such as `li`, again
produce the very same result on both sides).
-/
theorem Riscv.interpretOp'_monotone {operands operands' : Array RuntimeValue} :
    operands ⊒ operands' →
    Interp.isRefinedBy InterpretResultIsRefinedBy
      (Riscv.interpretOp' opType properties resultTypes operands blockOperands mem)
      (Riscv.interpretOp' opType properties resultTypes operands' blockOperands mem) := by
  intro h
  by_cases hregs : ∀ v ∈ operands, ∃ r, v = .reg r
  · have hb : operands' = operands := RuntimeValue.eq_of_arrayIsRefinedBy_of_regs h hregs
    subst hb
    apply interpretResult_isRefinedBy_refl
  · cases opType <;>
      simp only [Riscv.interpretOp'] <;>
      first
        | apply interpretResult_isRefinedBy_refl
        | (split
           · exfalso
             rename_i heq
             refine hregs (fun v hv => ?_)
             have hv' : v ∈ operands.toList := hv.val
             rw [heq] at hv'
             simp at hv'
             grind
           · simp [Interp.isRefinedBy])

/-! ## Monotonicity of the `arith` dialect interpreter

`Arith.interpretOp'` is monotone with respect to operand refinement: interpreting an `arith`
operation on refined operands yields a refined result. Every `arith` opcode is either a pure
function of its (integer) operands, computed with a data-level operation that is itself monotone
(`LLVM.Int.add_mono` and friends), or it is a division/remainder, whose source interpretation is
UB exactly when the refining target could misbehave (poison or zero divisor, and signed
overflow), and UB is refined by anything.
-/

section ArithMonotone

open Veir.Data

/-- The refinement relation on the results of `Arith.interpretOp'`: the result values refine
pointwise, and the control flow actions refine. -/
private abbrev ArithResultIsRefinedBy :
    (Array RuntimeValue × Option ControlFlowAction) →
    (Array RuntimeValue × Option ControlFlowAction) → Prop :=
  fun r₁ r₂ => r₁.1 ⊒ r₂.1 ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2

private theorem toArray_of_toList_eq {a : Array RuntimeValue} {l : List RuntimeValue}
    (ha : a.toList = l) : a = l.toArray := by
  rw [← ha]

private theorem list_length_eq_one {α : Type} {l : List α} (h : l.length = 1) :
    ∃ x, l = [x] := by
  match l, h with
  | [x], _ => exact ⟨x, rfl⟩

private theorem list_length_eq_two {α : Type} {l : List α} (h : l.length = 2) :
    ∃ x y, l = [x, y] := by
  match l, h with
  | [x, y], _ => exact ⟨x, y, rfl⟩

private theorem list_length_eq_three {α : Type} {l : List α} (h : l.length = 3) :
    ∃ x y z, l = [x, y, z] := by
  match l, h with
  | [x, y, z], _ => exact ⟨x, y, z, rfl⟩

/-- An array refining a one-element array is a one-element array whose element refines. -/
private theorem arrayIsRefinedBy_toList_one {a b : Array RuntimeValue} {x : RuntimeValue}
    (h : a ⊒ b) (ha : a.toList = [x]) : ∃ x', b.toList = [x'] ∧ x ⊒ x' := by
  have ha' : a = #[x] := toArray_of_toList_eq ha
  subst ha'
  obtain ⟨hs, hr⟩ := h
  simp at hs
  obtain ⟨x', hx'⟩ :=
    list_length_eq_one (l := b.toList) (by simp only [Array.length_toList]; omega)
  have hb : b = #[x'] := toArray_of_toList_eq hx'
  subst hb
  exact ⟨x', by simp, by simpa using hr 0 (by simp)⟩

/-- An array refining a two-element array is a two-element array whose elements refine. -/
private theorem arrayIsRefinedBy_toList_two {a b : Array RuntimeValue} {x y : RuntimeValue}
    (h : a ⊒ b) (ha : a.toList = [x, y]) :
    ∃ x' y', b.toList = [x', y'] ∧ x ⊒ x' ∧ y ⊒ y' := by
  have ha' : a = #[x, y] := toArray_of_toList_eq ha
  subst ha'
  obtain ⟨hs, hr⟩ := h
  simp at hs
  obtain ⟨x', y', hx'⟩ :=
    list_length_eq_two (l := b.toList) (by simp only [Array.length_toList]; omega)
  have hb : b = #[x', y'] := toArray_of_toList_eq hx'
  subst hb
  exact ⟨x', y', by simp, by simpa using hr 0 (by simp), by simpa using hr 1 (by simp)⟩

/-- An array refining a three-element array is a three-element array whose elements refine. -/
private theorem arrayIsRefinedBy_toList_three {a b : Array RuntimeValue} {x y z : RuntimeValue}
    (h : a ⊒ b) (ha : a.toList = [x, y, z]) :
    ∃ x' y' z', b.toList = [x', y', z'] ∧ x ⊒ x' ∧ y ⊒ y' ∧ z ⊒ z' := by
  have ha' : a = #[x, y, z] := toArray_of_toList_eq ha
  subst ha'
  obtain ⟨hs, hr⟩ := h
  simp at hs
  obtain ⟨x', y', z', hx'⟩ :=
    list_length_eq_three (l := b.toList) (by simp only [Array.length_toList]; omega)
  have hb : b = #[x', y', z'] := toArray_of_toList_eq hx'
  subst hb
  exact ⟨x', y', z', by simp, by simpa using hr 0 (by simp), by simpa using hr 1 (by simp),
    by simpa using hr 2 (by simp)⟩

/-- Two single-integer-result interpretations refine each other as soon as the integers do. -/
private theorem interp_pure_int_isRefinedBy {bw : Nat} {v v' : LLVM.Int bw} (h : v ⊒ v') :
    Interp.isRefinedBy ArithResultIsRefinedBy
      (pure (#[RuntimeValue.int bw v], none)) (pure (#[RuntimeValue.int bw v'], none)) := by
  refine ⟨?_, ?_⟩
  · simp only [RuntimeValue.arrayIsRefinedBy_singleton]
    exact ⟨rfl, by simpa using h⟩
  · trivial

/-- An interpretation refines itself (used for the operand-independent `arith.constant`). -/
private theorem interp_isRefinedBy_self
    (x : Interp (Array RuntimeValue × Option ControlFlowAction)) :
    Interp.isRefinedBy ArithResultIsRefinedBy x x := by
  rcases x with _ | (x | _) <;> simp only [Interp.isRefinedBy]
  exact ⟨RuntimeValue.arrayIsRefinedBy_refl _, ControlFlowAction.optionIsRefinedBy_refl _⟩

/-- Only a concrete integer refines a concrete integer, and it must be the very same one. -/
private theorem int_eq_of_val_isRefinedBy {w : Nat} {v : BitVec w} {x : LLVM.Int w}
    (h : LLVM.Int.val v ⊒ x) : x = .val v := by
  cases x <;> simp_all [isRefinedBy]

/--
`Arith.interpretOp'` is monotone with respect to operand refinement: if the source operands are
refined by the target operands, the source interpretation is refined by the target interpretation.
-/
theorem Arith.interpretOp'_monotone
    (op : Arith) (properties : HasDialectOpInfo.propertiesOf op) (resultTypes : Array TypeAttr)
    (operands operands' : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (h : operands ⊒ operands') :
    Interp.isRefinedBy
      (fun (r₁ r₂ : Array RuntimeValue × Option ControlFlowAction) =>
        r₁.1 ⊒ r₂.1 ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (Arith.interpretOp' op properties resultTypes operands blockOperands)
      (Arith.interpretOp' op properties resultTypes operands' blockOperands) := by
  cases op
  /- `arith.constant` does not read its operands. -/
  case constant =>
    simp only [Arith.interpretOp']
    exact interp_isRefinedBy_self _
  /- The binary integer opcodes: their data-level operation is monotone. -/
  case addi | subi | muli | shli | shrsi | shrui | andi | ori | xori =>
    all_goals
      simp only [Arith.interpretOp']
      split
      · next bw lhs bw' rhs heq =>
        obtain ⟨_, _, heq', hx, hy⟩ := arrayIsRefinedBy_toList_two h heq
        obtain ⟨lhs', rfl, hl⟩ := RuntimeValue.int_of_isRefinedBy hx
        obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy hy
        rw [heq']
        dsimp only
        split
        · exact Interp.isRefinedBy_none_target
        · next hbw =>
          have hbw' : bw' = bw := by omega
          subst hbw'
          simp only [LLVM.Int.cast_self]
          exact interp_pure_int_isRefinedBy (by grind)
      · exact Interp.isRefinedBy_none_target
  /- The unsigned division/remainder opcodes: a poison or zero divisor is UB in the source. -/
  case divui | remui =>
    all_goals
      simp only [Arith.interpretOp']
      split
      · next bw lhs bw' rhs heq =>
        obtain ⟨_, _, heq', hx, hy⟩ := arrayIsRefinedBy_toList_two h heq
        obtain ⟨lhs', rfl, hl⟩ := RuntimeValue.int_of_isRefinedBy hx
        obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy hy
        rw [heq']
        dsimp only
        split
        · exact Interp.isRefinedBy_none_target
        · next hbw =>
          have hbw' : bw' = bw := by omega
          subst hbw'
          simp only [LLVM.Int.cast_self]
          cases hrhs : rhs with
          | poison => exact Interp.isRefinedBy_ub_target
          | val v' =>
            rw [hrhs] at hr
            rw [int_eq_of_val_isRefinedBy hr]
            dsimp only
            split
            · exact Interp.isRefinedBy_ub_target
            · exact interp_pure_int_isRefinedBy (by grind)
      · exact Interp.isRefinedBy_none_target
  /- The signed division/remainder opcodes: additionally, the overflowing `intMin / -1` is UB. -/
  case divsi | remsi =>
    all_goals
      simp only [Arith.interpretOp']
      split
      · next bw lhs bw' rhs heq =>
        obtain ⟨_, _, heq', hx, hy⟩ := arrayIsRefinedBy_toList_two h heq
        obtain ⟨lhs', rfl, hl⟩ := RuntimeValue.int_of_isRefinedBy hx
        obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy hy
        rw [heq']
        dsimp only
        split
        · exact Interp.isRefinedBy_none_target
        · next hbw =>
          have hbw' : bw' = bw := by omega
          subst hbw'
          simp only [LLVM.Int.cast_self]
          cases hrhs : rhs with
          | poison => exact Interp.isRefinedBy_ub_target
          | val v' =>
            rw [hrhs] at hr
            rw [int_eq_of_val_isRefinedBy hr]
            dsimp only
            split
            · exact Interp.isRefinedBy_ub_target
            · split
              · cases hlhs : lhs with
                | poison => exact Interp.isRefinedBy_ub_target
                | val v =>
                  rw [hlhs] at hl
                  rw [int_eq_of_val_isRefinedBy hl]
                  dsimp only
                  split
                  · exact Interp.isRefinedBy_ub_target
                  · exact interp_pure_int_isRefinedBy (by grind)
              · exact interp_pure_int_isRefinedBy (by grind)
      · exact Interp.isRefinedBy_none_target
  /- The cast opcodes: one integer operand, and a monotone data-level cast. -/
  case trunci | extui | extsi =>
    all_goals
      simp only [Arith.interpretOp']
      split
      · next w val heq =>
        obtain ⟨_, heq', hx⟩ := arrayIsRefinedBy_toList_one h heq
        obtain ⟨val', rfl, hv⟩ := RuntimeValue.int_of_isRefinedBy hx
        rw [heq']
        dsimp only
        split
        · split
          · split
            · exact Interp.isRefinedBy_none_target
            · exact interp_pure_int_isRefinedBy (by grind)
          · exact Interp.isRefinedBy_none_target
        · exact Interp.isRefinedBy_none_target
      · exact Interp.isRefinedBy_none_target
  /- `arith.select`: three integer operands, and `LLVM.Int.select` is monotone. -/
  case select =>
    simp only [Arith.interpretOp']
    split
    · next cond bw lhs bw' rhs heq =>
      obtain ⟨_, _, _, heq', hc, hx, hy⟩ := arrayIsRefinedBy_toList_three h heq
      obtain ⟨cond', rfl, hcond⟩ := RuntimeValue.int_of_isRefinedBy hc
      obtain ⟨lhs', rfl, hl⟩ := RuntimeValue.int_of_isRefinedBy hx
      obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy hy
      rw [heq']
      simp only []
      split
      · exact Interp.isRefinedBy_none_target
      · next hbw =>
        have hbw' : bw' = bw := by omega
        subst hbw'
        simp only [LLVM.Int.cast_self]
        exact interp_pure_int_isRefinedBy
          (LLVM.Int.select_mono lhs rhs lhs' rhs' cond cond' hl hr hcond)
    · exact Interp.isRefinedBy_none_target
  /- All remaining `arith` opcodes are not interpreted, so the source interpretation fails. -/
  all_goals exact Interp.isRefinedBy_none_target

/--
`interpretOp'` is monotone with respect to operand refinement on the `arith` dialect: the memory
is threaded through unchanged, so it is left untouched (and hence equal) on both sides.
-/
theorem interpretOp'_monotone_arith
    (op : Arith) (properties : propertiesOf (OpCode.arith op)) (resultTypes : Array TypeAttr)
    (operands operands' : Array RuntimeValue) (blockOperands : Array BlockPtr) (mem : MemoryState)
    (h : operands ⊒ operands') :
    Interp.isRefinedBy (α := Array RuntimeValue × MemoryState × Option ControlFlowAction)
      (fun r₁ r₂ => r₁.1 ⊒ r₂.1 ∧ r₁.2.1 = r₂.2.1 ∧
        ControlFlowAction.optionIsRefinedBy r₁.2.2 r₂.2.2)
      (interpretOp' (.arith op) properties resultTypes operands blockOperands mem)
      (interpretOp' (.arith op) properties resultTypes operands' blockOperands mem) := by
  have hmono :=
    Arith.interpretOp'_monotone op properties resultTypes operands operands' blockOperands h
  simp only [interpretOp', bind]
  rcases hsrc : Arith.interpretOp' op properties resultTypes operands blockOperands with
    _ | (⟨vals, act⟩ | _)
  · exact Interp.isRefinedBy_none_target
  · simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at hmono
    obtain ⟨⟨vals', act'⟩, htgt, hvals, hact⟩ := hmono
    simp only [htgt]
    exact ⟨hvals, rfl, hact⟩
  · exact Interp.isRefinedBy_ub_target

end ArithMonotone


/--
Lift monotonicity of a dialect interpreter that does not touch memory (its result is a
`(values, action)` pair) to the memory-carrying result of `interpretOp'`, which threads the
unchanged input memory through.
-/
theorem interpretResult_isRefinedBy_of_memFree
    {x y : Interp (Array RuntimeValue × Option ControlFlowAction)} (mem : MemoryState)
    (h : Interp.isRefinedBy
      (fun (r₁ r₂ : Array RuntimeValue × Option ControlFlowAction) =>
        r₁.1 ⊒ r₂.1 ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2) x y) :
    Interp.isRefinedBy InterpretResultIsRefinedBy
      (do let (vals, act) ← x; return (vals, mem, act))
      (do let (vals, act) ← y; return (vals, mem, act)) := by
  rcases x with _ | (⟨v, a⟩ | _) <;> rcases y with _ | (⟨v', a'⟩ | _) <;>
    simp_all [Interp.isRefinedBy, pure, bind]
  exact ⟨h.1, rfl, h.2⟩

set_option warn.sorry false in
/--
`interpretOp'` is monotone in its operands, except for two opcodes that materialise poison into a
representation that cannot hold it, and so are genuinely *not* monotone for this relation:

* `llvm.store` writes poison into memory as an empoisoned byte range, while storing the concrete
  value that refines it clears that poison mask, and the relation requires the resulting memories
  to be *equal* (see `Llvm.interpretOp'_monotone`).
* `builtin.unrealized_conversion_cast` from an integer to a register maps poison to the register
  `0` (`LLVM.Int.toReg`), while the concrete value that refines it maps to a different register,
  and refinement on registers is equality (registers cannot be poison).
-/
theorem interpretOp'_monotone
    (opType : OpCode) (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands operands' : Array RuntimeValue) (blockOperands : Array BlockPtr) (mem : MemoryState)
    (notStore : opType ≠ .llvm .store)
    (notCast : opType ≠ .builtin .unrealized_conversion_cast) :
    operands ⊒ operands' →
    Interp.isRefinedBy (α := Array RuntimeValue × MemoryState × Option ControlFlowAction)
      (fun r₁ r₂ => r₁.1 ⊒ r₂.1 ∧ r₁.2.1 = r₂.2.1 ∧
        ControlFlowAction.optionIsRefinedBy r₁.2.2 r₂.2.2)
      (interpretOp' opType properties resultTypes operands blockOperands mem)
      (interpretOp' opType properties resultTypes operands' blockOperands mem) := by
  intro h
  cases opType
  case riscv =>
    simp only [interpretOp']
    exact Riscv.interpretOp'_monotone h
  case llvm =>
    simp only [interpretOp']
    exact Llvm.interpretOp'_monotone (by grind) h
  /- `rv64`, `riscv_stack` and `hw` ignore their operands entirely, so both sides interpret to the
  very same result. -/
  case rv64 op =>
    cases op <;> simp only [interpretOp', Rv64.interpretOp'] <;>
      apply interpretResult_isRefinedBy_refl
  case riscv_stack op =>
    cases op <;> simp only [interpretOp', Riscv_Stack.interpretOp'] <;>
      apply interpretResult_isRefinedBy_refl
  case hw op =>
    cases op <;> simp only [interpretOp', HW.interpretOp'] <;>
      apply interpretResult_isRefinedBy_refl
  /- `func.return` hands its operands straight to the `return` action, which refines pointwise. -/
  case func op =>
    cases op
    case «return» =>
      simpa [interpretOp', Interp.isRefinedBy, pure, ControlFlowAction.optionIsRefinedBy,
        ControlFlowAction.isRefinedBy] using h
    all_goals simp [interpretOp', Interp.isRefinedBy]
  /- The only `builtin` opcode that interprets is the (excluded) cast; the others fail. -/
  case builtin op =>
    cases op <;> simp_all [interpretOp', Interp.isRefinedBy]
  /- `arith` does not touch memory: lift its own monotonicity through the memory threading. -/
  case arith op =>
    simp only [interpretOp']
    exact interpretResult_isRefinedBy_of_memFree mem
      (Arith.interpretOp'_monotone op properties resultTypes operands operands' blockOperands h)
  all_goals sorry

set_option warn.sorry false in
/--
A successful operation interpretation returns result values that conform to the declared
`resultTypes` when the operation verifies.
-/
theorem interpretOp'_results_conform {ctx : WfIRContext OpCode}
    {opInBounds : op.InBounds ctx.raw} (opVerif : op.Verified ctx opInBounds)
    (conforms : RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw))
    (h : op.interpret ctx.raw operands mem = some (.ok (vals, mem', act))) :
    RuntimeValue.ArrayConforms vals (op.getResultTypes! ctx.raw) := by
  sorry
