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

/-! ## Monotonicity of the `cf`, `riscv_cf` and `comb` dialect interpreters

None of these three dialects touches memory, so they interpret to a `(values, action)` pair that
`interpretOp'` pairs with the unchanged input memory (see `interpretResult_isRefinedBy_of_memFree`).
All three are monotone with respect to operand refinement:

* `cf.br` and `riscv_cf.branch` hand their operands straight to a `branch` action, which refines
  because the operands do;
* `cf.cond_br` is undefined behaviour on a poison condition (and UB is refined by anything), while
  a concrete condition is refined only by itself, so both sides take the same branch and pass it
  refining `Array.extract` slices of their operands;
* the `riscv_cf` comparisons branch on registers, which carry no poison and hence refine only
  themselves, so again both sides take the same branch;
* `comb.add` is a pure function of its integer operands, and `Veir.Data.Comb.add` is monotone: it
  is poison as soon as one of its arguments is, and otherwise all its arguments are concrete and
  the refining ones are the very same.
-/

section MemFreeMonotone

open Veir.Data

/-- The refinement relation on the results of a memory-free dialect interpreter: the result values
refine pointwise, and the control flow actions refine. -/
private abbrev MemFreeResultIsRefinedBy :
    (Array RuntimeValue × Option ControlFlowAction) →
    (Array RuntimeValue × Option ControlFlowAction) → Prop :=
  fun r₁ r₂ => r₁.1 ⊒ r₂.1 ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2

/-- A memory-free interpretation refines itself. -/
private theorem memFree_isRefinedBy_self
    (x : Interp (Array RuntimeValue × Option ControlFlowAction)) :
    Interp.isRefinedBy MemFreeResultIsRefinedBy x x := by
  rcases x with _ | (x | _) <;> simp only [Interp.isRefinedBy]
  exact ⟨RuntimeValue.arrayIsRefinedBy_refl _, ControlFlowAction.optionIsRefinedBy_refl _⟩

/-- Branching to the same destination with refining arguments refines. -/
private theorem interp_branch_isRefinedBy {vals vals' : Array RuntimeValue} (dest : BlockPtr)
    (h : vals ⊒ vals') :
    Interp.isRefinedBy MemFreeResultIsRefinedBy
      (pure (#[], some (.branch vals dest)))
      (pure (#[], some (.branch vals' dest))) :=
  ⟨RuntimeValue.arrayIsRefinedBy_nil, rfl, h⟩

/-- The suffix slices of refined operand arrays refine: the two arrays have the same size. -/
private theorem arrayIsRefinedBy_extract_size {a b : Array RuntimeValue} (h : a ⊒ b) (i : Nat) :
    a.extract i a.size ⊒ b.extract i b.size := by
  have hsize : a.size = b.size := h.1
  rw [← hsize]
  exact RuntimeValue.arrayIsRefinedBy_extract h i a.size

/-- Both sides of a conditional branch on the same condition pick the same successor, and the
branch arguments they pass to it are refining slices of the operands. -/
private theorem interp_condBranch_isRefinedBy {operands operands' : Array RuntimeValue}
    (h : operands ⊒ operands') (c : Prop) [Decidable c] (s t : Nat)
    (destTrue destFalse : BlockPtr) :
    Interp.isRefinedBy MemFreeResultIsRefinedBy
      (if c then pure (#[], some (.branch (operands.extract s (t + s)) destTrue))
        else pure (#[], some (.branch (operands.extract (t + s) operands.size) destFalse)))
      (if c then pure (#[], some (.branch (operands'.extract s (t + s)) destTrue))
        else pure (#[], some (.branch (operands'.extract (t + s) operands'.size) destFalse))) := by
  split
  · exact interp_branch_isRefinedBy _ (RuntimeValue.arrayIsRefinedBy_extract h _ _)
  · exact interp_branch_isRefinedBy _ (arrayIsRefinedBy_extract_size h _)

/--
`Cf.interpretOp'` is monotone with respect to operand refinement.

`cf.br` passes its operands straight to the `branch` action. `cf.cond_br` is undefined behaviour
when the condition is poison, and a concrete condition is refined only by itself, so both sides
take the same branch and pass refining slices of their operands to it.
-/
theorem Cf.interpretOp'_monotone
    (op : Cf) (properties : HasDialectOpInfo.propertiesOf op) (resultTypes : Array TypeAttr)
    (operands operands' : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (h : operands ⊒ operands') :
    Interp.isRefinedBy
      (fun (r₁ r₂ : Array RuntimeValue × Option ControlFlowAction) =>
        r₁.1 ⊒ r₂.1 ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (Cf.interpretOp' op properties resultTypes operands blockOperands)
      (Cf.interpretOp' op properties resultTypes operands' blockOperands) := by
  cases op
  /- `cf.br` hands its operands to the branch action. -/
  case br =>
    simp only [Cf.interpretOp']
    split
    · exact ⟨RuntimeValue.arrayIsRefinedBy_nil, rfl, h⟩
    · exact Interp.isRefinedBy_none_target
  /- `cf.cond_br`: a poison condition is UB, a concrete one is refined only by itself. -/
  case cond_br =>
    simp only [Cf.interpretOp']
    split
    · split
      · next condVal hcond =>
        obtain ⟨w, hw, hcw⟩ := RuntimeValue.arrayIsRefinedBy_getElem? h hcond
        rw [hw]
        dsimp only
        split
        · split
          · next _ v =>
            obtain ⟨t, rfl, ht⟩ := RuntimeValue.int_of_isRefinedBy hcw
            rw [int_eq_of_val_isRefinedBy ht]
            exact interp_condBranch_isRefinedBy h _ 1 _ _ _
          · exact Interp.isRefinedBy_ub_target
          · exact Interp.isRefinedBy_none_target
        · exact Interp.isRefinedBy_none_target
      · exact Interp.isRefinedBy_none_target
    · exact Interp.isRefinedBy_none_target

/--
`Riscv_Cf.interpretOp'` is monotone with respect to operand refinement.

`riscv_cf.branch` hands its operands to the branch action. Every conditional jump compares
registers, which carry no poison and are hence refined only by themselves, so both sides compare
the very same values, take the same branch, and pass refining slices of their operands to it.
-/
theorem Riscv_Cf.interpretOp'_monotone
    (op : Riscv_Cf) (properties : HasDialectOpInfo.propertiesOf op) (resultTypes : Array TypeAttr)
    (operands operands' : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (h : operands ⊒ operands') :
    Interp.isRefinedBy
      (fun (r₁ r₂ : Array RuntimeValue × Option ControlFlowAction) =>
        r₁.1 ⊒ r₂.1 ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (Riscv_Cf.interpretOp' op properties resultTypes operands blockOperands)
      (Riscv_Cf.interpretOp' op properties resultTypes operands' blockOperands) := by
  cases op
  case branch =>
    simp only [Riscv_Cf.interpretOp']
    split
    · exact ⟨RuntimeValue.arrayIsRefinedBy_nil, rfl, h⟩
    · exact Interp.isRefinedBy_none_target
  /- The two-register comparisons. -/
  case beq | bne | blt | bge | bltu | bgeu =>
    all_goals
      simp only [Riscv_Cf.interpretOp']
      split
      · split
        · next lhs hlhs =>
          obtain ⟨u, hu, hru⟩ := RuntimeValue.arrayIsRefinedBy_getElem? h hlhs
          rw [RuntimeValue.reg_of_isRefinedBy hru] at hu
          rw [hu]
          dsimp only
          split
          · next rhs hrhs =>
            obtain ⟨v, hv, hrv⟩ := RuntimeValue.arrayIsRefinedBy_getElem? h hrhs
            rw [RuntimeValue.reg_of_isRefinedBy hrv] at hv
            rw [hv]
            dsimp only
            split
            · exact interp_condBranch_isRefinedBy h _ 2 _ _ _
            · exact Interp.isRefinedBy_none_target
          · exact Interp.isRefinedBy_none_target
        · exact Interp.isRefinedBy_none_target
      · exact Interp.isRefinedBy_none_target
  /- The single-register comparisons against zero. -/
  case beqz | bnez =>
    all_goals
      simp only [Riscv_Cf.interpretOp']
      split
      · split
        · next cond hcond =>
          obtain ⟨u, hu, hru⟩ := RuntimeValue.arrayIsRefinedBy_getElem? h hcond
          rw [RuntimeValue.reg_of_isRefinedBy hru] at hu
          rw [hu]
          dsimp only
          split
          · exact interp_condBranch_isRefinedBy h _ 1 _ _ _
          · exact Interp.isRefinedBy_none_target
        · exact Interp.isRefinedBy_none_target
      · exact Interp.isRefinedBy_none_target

/-- Refined operand arrays refine element-wise, also as lists. -/
private theorem toList_getElem!_isRefinedBy {a b : Array RuntimeValue} (h : a ⊒ b) (i : Nat)
    (hi : i < a.size) : a.toList[i]! ⊒ b.toList[i]! := by
  obtain ⟨hs, he⟩ := h
  have hrefine := he i hi
  rw [getElem!_pos a i hi, getElem!_pos b i (by omega)] at hrefine
  rw [getElem!_pos a.toList i (by simpa using hi), getElem!_pos b.toList i (by simp; omega)]
  simpa using hrefine

/-- Monotonicity of an `Option`-valued interpreter lifts to the `Interp` monad it is lifted into
(`Comb.interpretOp'` cannot signal undefined behaviour, so it returns an `Option`). -/
private theorem interp_isRefinedBy_liftOption {α β : Type} {R : α → β → Prop} {x : Option α}
    {y : Option β} (hxy : ∀ a, x = some a → ∃ b, y = some b ∧ R a b) :
    Interp.isRefinedBy R (liftM x) (liftM y) := by
  cases x with
  | none => exact Interp.isRefinedBy_none_target
  | some a =>
    obtain ⟨b, hb, hR⟩ := hxy a rfl
    rw [hb]
    exact hR

/-- `Veir.Data.Comb.add` of a list that starts with poison is poison. -/
private theorem comb_add_cons_poison {w : Nat} (xs : List (LLVM.Int w)) :
    Data.Comb.add (.poison :: xs) = .poison := by
  simp [Data.Comb.add, Id.run]
  rfl

/-- `Veir.Data.Comb.add` of a list whose second element is poison is poison. -/
private theorem comb_add_val_cons_poison {w : Nat} (acc : BitVec w) (xs : List (LLVM.Int w)) :
    Data.Comb.add (.val acc :: .poison :: xs) = .poison := by
  simp [Data.Comb.add, Id.run]
  rfl

/-- Absorbing the second element of the list into the accumulator of `Veir.Data.Comb.add`. -/
private theorem comb_add_val_cons_val {w : Nat} (acc u : BitVec w) (xs : List (LLVM.Int w)) :
    Data.Comb.add (.val acc :: .val u :: xs) = Data.Comb.add (.val (acc + u) :: xs) := by
  simp [Data.Comb.add, Id.run]

/-- `Veir.Data.Comb.add` of a list containing a poison value is poison. -/
private theorem comb_add_eq_poison {w : Nat} :
    ∀ (l : List (LLVM.Int w)), LLVM.Int.poison ∈ l → Data.Comb.add l = .poison := by
  have hgen : ∀ (xs : List (LLVM.Int w)) (acc : BitVec w), LLVM.Int.poison ∈ xs →
      Data.Comb.add (.val acc :: xs) = .poison := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      intro acc hmem
      match x with
      | .poison => exact comb_add_val_cons_poison acc xs
      | .val u =>
        rw [comb_add_val_cons_val]
        exact ih (acc + u) (by simpa using hmem)
  intro l hmem
  match l with
  | [] => simp at hmem
  | .poison :: xs => exact comb_add_cons_poison xs
  | .val u :: xs => exact hgen xs u (by simpa using hmem)

/-- A concrete integer is refined only by itself, so a refined integer is either poison in the
source, or the very same value on both sides. -/
private theorem int_eq_or_poison_of_isRefinedBy {w : Nat} {a b : LLVM.Int w} (h : a ⊒ b) :
    a = .poison ∨ b = a := by
  cases a with
  | poison => exact Or.inl rfl
  | val v => exact Or.inr (int_eq_of_val_isRefinedBy h)

/-- Mapping refining operand lists with the same partial function succeeds on both sides, and
yields lists that are either equal, or a source list that contains a poison value (and hence sums
to poison). -/
private theorem mapM_isRefinedBy {w : Nat} {f : RuntimeValue → Option (LLVM.Int w)}
    (hf : ∀ (x y : RuntimeValue) (a : LLVM.Int w), RuntimeValue.isRefinedBy x y → f x = some a →
      ∃ b, f y = some b ∧ _root_.isRefinedBy a b) :
    ∀ (l l' : List RuntimeValue) (as : List (LLVM.Int w)),
      RuntimeValue.arrayIsRefinedBy l.toArray l'.toArray → l.mapM f = some as →
      ∃ bs, l'.mapM f = some bs ∧ (as = bs ∨ LLVM.Int.poison ∈ as) := by
  intro l
  induction l with
  | nil =>
    intro l' as harr hmap
    have hnil : l' = [] := by
      have hlen := harr.1
      simp at hlen
      exact List.eq_nil_of_length_eq_zero hlen.symm
    subst hnil
    simp at hmap
    exact ⟨[], by simp, Or.inl hmap⟩
  | cons x xs ih =>
    intro l' as harr hmap
    match l' with
    | [] =>
      have hlen := harr.1
      simp at hlen
    | y :: ys =>
      rw [RuntimeValue.arrayIsRefinedBy_cons] at harr
      obtain ⟨hxy, hxys⟩ := harr
      cases hfx : f x with
      | none => rw [List.mapM_cons] at hmap; simp [hfx] at hmap
      | some a =>
        cases hfxs : xs.mapM f with
        | none => rw [List.mapM_cons] at hmap; simp [hfx, hfxs] at hmap
        | some as₀ =>
          rw [List.mapM_cons, hfx, hfxs] at hmap
          simp at hmap
          obtain ⟨b, hfb, hab⟩ := hf x y a hxy hfx
          obtain ⟨bs₀, hbs₀, hrel⟩ := ih ys as₀ hxys hfxs
          refine ⟨b :: bs₀, ?_, ?_⟩
          · rw [List.mapM_cons]
            simp [hfb, hbs₀]
          · subst hmap
            rcases int_eq_or_poison_of_isRefinedBy hab with hpoison | hba
            · exact Or.inr (by simp [hpoison])
            · rcases hrel with heq | hmem
              · exact Or.inl (by rw [hba, heq])
              · exact Or.inr (by simp [hmem])

/--
`Comb.interpretOp'` is monotone with respect to operand refinement.

`comb.add` is the only interpreted `comb` opcode. Its operands are integers of a common width, and
`Veir.Data.Comb.add` is monotone: it is poison as soon as one of its arguments is poison (and
poison is refined by anything), and otherwise every argument is concrete, so the refining arguments
are the very same ones and both sides compute the same sum.
-/
theorem Comb.interpretOp'_monotone
    (op : Comb) (properties : HasDialectOpInfo.propertiesOf op)
    (operands operands' : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (h : operands ⊒ operands') :
    Interp.isRefinedBy
      (fun (r₁ r₂ : Array RuntimeValue × Option ControlFlowAction) =>
        r₁.1 ⊒ r₂.1 ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (liftM (Comb.interpretOp' op properties operands blockOperands))
      (liftM (Comb.interpretOp' op properties operands' blockOperands)) := by
  cases op
  case add =>
    /- Empty operand arrays: both sides interpret to the very same result. -/
    by_cases hsize : operands.size = 0
    · have hempty : operands = #[] := by
        simpa using hsize
      have hempty' : operands' = #[] := by
        have hsize' := h.1
        simp [hempty] at hsize'
        simpa using hsize'.symm
      rw [hempty, hempty']
      exact memFree_isRefinedBy_self _
    apply interp_isRefinedBy_liftOption
    intro res hres
    have hpos : 0 < operands.size := by omega
    have h0 := toList_getElem!_isRefinedBy h 0 hpos
    simp only [Comb.interpretOp'] at hres ⊢
    split at hres
    /- The first operand is an integer of width `w`, and so is the refining one. -/
    · next w fst heq0 =>
      rw [heq0] at h0
      obtain ⟨fst', hfst', hrfst⟩ := RuntimeValue.int_of_isRefinedBy h0
      rw [hfst']
      dsimp only
      split at hres
      /- Every operand is an integer of width `w`, and so is every refining one. -/
      · next nl hmap =>
        obtain ⟨bs, hbs, hrel⟩ := mapM_isRefinedBy (w := w)
          (by
            intro x y a hxy hfx
            cases x with
            | int w' val =>
              obtain ⟨t, rfl, ht⟩ := RuntimeValue.int_of_isRefinedBy hxy
              simp only at hfx ⊢
              split at hfx
              · exact absurd hfx (by simp)
              · next hw =>
                have hw' : w' = w := by simpa using hw
                subst hw'
                simp only [LLVM.Int.cast_self] at hfx ⊢
                refine ⟨t, by simp, ?_⟩
                have hav : val = a := by simpa using hfx
                subst hav
                exact ht
            | _ => exact absurd hfx (by simp))
          operands.toList operands'.toList nl (by simpa using h) hmap
        rw [show operands'.toList.mapM _ = some bs from hbs]
        have hres' : res = (#[RuntimeValue.int w (Data.Comb.add nl)], none) := by
          simpa using hres.symm
        subst hres'
        have hadd : Data.Comb.add nl ⊒ Data.Comb.add bs := by
          rcases hrel with heq | hmem
          · rw [heq]
            exact isRefinedBy_refl _
          · rw [comb_add_eq_poison nl hmem]
            trivial
        refine ⟨_, rfl, ?_, ?_⟩
        · simp only [RuntimeValue.arrayIsRefinedBy_singleton]
          exact ⟨rfl, by simpa using hadd⟩
        · trivial
      · exact absurd hres (by simp)
    · exact absurd hres (by simp)
  /- No other `comb` opcode is interpreted, so the source interpretation fails. -/
  all_goals
    simp only [Comb.interpretOp']
    exact Interp.isRefinedBy_none_target

end MemFreeMonotone

section LlvmMonotone

open Veir.Data

/-! ### Data-level monotonicity of the `LLVM.Int` intrinsics

`Veir/Data/LLVM/Int/Bitblast.lean` already proves monotonicity of the arithmetic, bitwise, cast,
comparison and selection operations. The intrinsics below are the remaining `LLVM.Int` functions
used by `Llvm.interpretOp'`; each is monotone for the same reason (poison propagates, and on
poison-free inputs refinement is equality), and `grind` closes them from the registered
`isPoison_*`/`getValue_*` equations.
-/

private theorem int_fshl_mono {w : Nat} (a₁ b₁ c₁ a₂ b₂ c₂ : LLVM.Int w)
    (ha : a₁ ⊒ a₂) (hb : b₁ ⊒ b₂) (hc : c₁ ⊒ c₂) :
    LLVM.Int.fshl a₁ b₁ c₁ ⊒ LLVM.Int.fshl a₂ b₂ c₂ := by
  grind

private theorem int_fshr_mono {w : Nat} (a₁ b₁ c₁ a₂ b₂ c₂ : LLVM.Int w)
    (ha : a₁ ⊒ a₂) (hb : b₁ ⊒ b₂) (hc : c₁ ⊒ c₂) :
    LLVM.Int.fshr a₁ b₁ c₁ ⊒ LLVM.Int.fshr a₂ b₂ c₂ := by
  grind

private theorem int_ctlz_mono {w : Nat} (x₁ x₂ : LLVM.Int w) (isZeroPoison : Bool)
    (h : x₁ ⊒ x₂) : LLVM.Int.ctlz x₁ isZeroPoison ⊒ LLVM.Int.ctlz x₂ isZeroPoison := by
  grind

private theorem int_cttz_mono {w : Nat} (x₁ x₂ : LLVM.Int w) (isZeroPoison : Bool)
    (h : x₁ ⊒ x₂) : LLVM.Int.cttz x₁ isZeroPoison ⊒ LLVM.Int.cttz x₂ isZeroPoison := by
  grind

private theorem int_ctpop_mono {w : Nat} (x₁ x₂ : LLVM.Int w) (h : x₁ ⊒ x₂) :
    LLVM.Int.ctpop x₁ ⊒ LLVM.Int.ctpop x₂ := by
  grind

/-- `bswap` has no width-generic `getValue` equation, so we argue by cases on the source instead:
poison propagates, and a concrete source is refined only by itself. -/
private theorem int_bswap_mono {w : Nat} (x₁ x₂ : LLVM.Int w) (h : x₁ ⊒ x₂) :
    LLVM.Int.bswap x₁ ⊒ LLVM.Int.bswap x₂ := by
  cases x₁ with
  | poison => grind
  | val v => rw [int_eq_of_val_isRefinedBy h]; grind

private theorem int_bitreverse_mono {w : Nat} (x₁ x₂ : LLVM.Int w) (h : x₁ ⊒ x₂) :
    LLVM.Int.bitreverse x₁ ⊒ LLVM.Int.bitreverse x₂ := by
  grind

private theorem int_smax_mono {w : Nat} (x₁ y₁ x₂ y₂ : LLVM.Int w)
    (hx : x₁ ⊒ x₂) (hy : y₁ ⊒ y₂) : LLVM.Int.smax x₁ y₁ ⊒ LLVM.Int.smax x₂ y₂ := by
  grind

private theorem int_smin_mono {w : Nat} (x₁ y₁ x₂ y₂ : LLVM.Int w)
    (hx : x₁ ⊒ x₂) (hy : y₁ ⊒ y₂) : LLVM.Int.smin x₁ y₁ ⊒ LLVM.Int.smin x₂ y₂ := by
  grind

private theorem int_umax_mono {w : Nat} (x₁ y₁ x₂ y₂ : LLVM.Int w)
    (hx : x₁ ⊒ x₂) (hy : y₁ ⊒ y₂) : LLVM.Int.umax x₁ y₁ ⊒ LLVM.Int.umax x₂ y₂ := by
  grind

private theorem int_umin_mono {w : Nat} (x₁ y₁ x₂ y₂ : LLVM.Int w)
    (hx : x₁ ⊒ x₂) (hy : y₁ ⊒ y₂) : LLVM.Int.umin x₁ y₁ ⊒ LLVM.Int.umin x₂ y₂ := by
  grind

private theorem int_abs_mono {w : Nat} (x₁ x₂ : LLVM.Int w) (isIntMinPoison : Bool)
    (h : x₁ ⊒ x₂) : LLVM.Int.abs x₁ isIntMinPoison ⊒ LLVM.Int.abs x₂ isIntMinPoison := by
  grind

private theorem int_saddSat_mono {w : Nat} (x₁ y₁ x₂ y₂ : LLVM.Int w)
    (hx : x₁ ⊒ x₂) (hy : y₁ ⊒ y₂) : LLVM.Int.saddSat x₁ y₁ ⊒ LLVM.Int.saddSat x₂ y₂ := by
  grind

private theorem int_uaddSat_mono {w : Nat} (x₁ y₁ x₂ y₂ : LLVM.Int w)
    (hx : x₁ ⊒ x₂) (hy : y₁ ⊒ y₂) : LLVM.Int.uaddSat x₁ y₁ ⊒ LLVM.Int.uaddSat x₂ y₂ := by
  grind

private theorem int_ssubSat_mono {w : Nat} (x₁ y₁ x₂ y₂ : LLVM.Int w)
    (hx : x₁ ⊒ x₂) (hy : y₁ ⊒ y₂) : LLVM.Int.ssubSat x₁ y₁ ⊒ LLVM.Int.ssubSat x₂ y₂ := by
  grind

private theorem int_usubSat_mono {w : Nat} (x₁ y₁ x₂ y₂ : LLVM.Int w)
    (hx : x₁ ⊒ x₂) (hy : y₁ ⊒ y₂) : LLVM.Int.usubSat x₁ y₁ ⊒ LLVM.Int.usubSat x₂ y₂ := by
  grind

private theorem int_sshlSat_mono {w : Nat} (x₁ y₁ x₂ y₂ : LLVM.Int w)
    (hx : x₁ ⊒ x₂) (hy : y₁ ⊒ y₂) : LLVM.Int.sshlSat x₁ y₁ ⊒ LLVM.Int.sshlSat x₂ y₂ := by
  grind

private theorem int_ushlSat_mono {w : Nat} (x₁ y₁ x₂ y₂ : LLVM.Int w)
    (hx : x₁ ⊒ x₂) (hy : y₁ ⊒ y₂) : LLVM.Int.ushlSat x₁ y₁ ⊒ LLVM.Int.ushlSat x₂ y₂ := by
  grind

/-! ### Data-level monotonicity of the `LLVM.Byte` operations

`llvm.shl`, `llvm.lshr` and `llvm.trunc` also accept a *byte* operand, whose refinement is
bit-wise (`LLVM.Byte.isRefinedBy`). There are no monotonicity lemmas for `LLVM.Byte` yet, so we
prove the three we need here, working bit by bit.
-/

/-- Bit-wise characterisation of byte refinement: at every bit, either the source bit is poison,
or the value bits agree and the target bit is not poison. -/
private theorem byte_isRefinedBy_iff {w : Nat} (x y : LLVM.Byte w) :
    x ⊒ y ↔ ∀ i, i < w →
      (x.poison.getLsbD i = true ∨
        (x.val.getLsbD i = y.val.getLsbD i ∧ y.poison.getLsbD i = false)) := by
  simp only [LLVM.Byte.isRefinedBy, BitVec.eq_of_getLsbD_eq_iff, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, BitVec.getLsbD_allOnes]
  constructor
  · intro h i hi
    have hbit := h i hi
    revert hbit
    simp only [hi, decide_true, Bool.true_and]
    cases x.poison.getLsbD i <;> cases x.val.getLsbD i <;> cases y.val.getLsbD i <;>
      cases y.poison.getLsbD i <;> simp
  · intro h i hi
    have hbit := h i hi
    revert hbit
    simp only [hi, decide_true, Bool.true_and]
    cases x.poison.getLsbD i <;> cases x.val.getLsbD i <;> cases y.val.getLsbD i <;>
      cases y.poison.getLsbD i <;> simp

/-- The all-poison byte refines every byte. -/
private theorem byte_allPoison_isRefinedBy {w : Nat} (y : LLVM.Byte w) :
    LLVM.Byte.allPoison ⊒ y := by
  rw [byte_isRefinedBy_iff]
  intro i hi
  simp [LLVM.Byte.allPoison, hi]

/-- Shifting left and back right is the identity exactly when the bits shifted out are zero. -/
private theorem bv_shiftLeft_ushiftRight_eq_self_iff {w : Nat} (v : BitVec w) (n : Nat) :
    (v <<< n) >>> n = v ↔ ∀ i, i < w → w ≤ i + n → v.getLsbD i = false := by
  rw [BitVec.eq_of_getLsbD_eq_iff]
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, Nat.add_sub_cancel_left]
  constructor
  · intro h i hi hw
    have := h i hi
    simp only [Nat.not_lt.mpr (by omega : w ≤ n + i), decide_false, Bool.false_and] at this
    grind
  · intro h i hi
    by_cases hw : n + i < w
    · simp [hw]
    · simp only [hw, decide_false, Bool.false_and]
      exact (h i hi (by omega)).symm

/-- Shifting right and back left is the identity exactly when the bits shifted out are zero. -/
private theorem bv_ushiftRight_shiftLeft_eq_self_iff {w : Nat} (v : BitVec w) (n : Nat) :
    (v >>> n) <<< n = v ↔ ∀ i, i < n → v.getLsbD i = false := by
  rw [BitVec.eq_of_getLsbD_eq_iff]
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  constructor
  · intro h i hi
    by_cases hiw : i < w
    · have := h i hiw
      simp only [hiw, decide_true, Bool.true_and, hi, decide_true, Bool.not_true,
        Bool.false_and] at this
      exact this.symm
    · exact BitVec.getLsbD_of_ge v i (by omega)
  · intro h i hi
    by_cases hin : i < n
    · simp only [hi, decide_true, Bool.true_and, hin, decide_true, Bool.not_true, Bool.false_and]
      exact (h i hin).symm
    · simp only [hi, decide_true, Bool.true_and, hin, decide_false, Bool.not_false,
        Bool.true_and]
      congr 1
      omega

/-- Shifting both the value and the poison mask left preserves byte refinement. -/
private theorem byte_shiftLeft_isRefinedBy {w : Nat} {x y : LLVM.Byte w} (h : x ⊒ y)
    (s : BitVec w) (hx : (x.val <<< s) &&& (x.poison <<< s) = 0)
    (hy : (y.val <<< s) &&& (y.poison <<< s) = 0) :
    (⟨x.val <<< s, x.poison <<< s, hx⟩ : LLVM.Byte w) ⊒
      ⟨y.val <<< s, y.poison <<< s, hy⟩ := by
  rw [byte_isRefinedBy_iff] at h ⊢
  intro i hi
  simp only [BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  by_cases hlt : i < s.toNat
  · simp [hlt]
  · simp only [hlt, decide_false, Bool.not_false, Bool.true_and]
    exact h (i - s.toNat) (by omega)

/-- Shifting both the value and the poison mask right preserves byte refinement. -/
private theorem byte_ushiftRight_isRefinedBy {w : Nat} {x y : LLVM.Byte w} (h : x ⊒ y)
    (s : BitVec w) (hx : (x.val >>> s) &&& (x.poison >>> s) = 0)
    (hy : (y.val >>> s) &&& (y.poison >>> s) = 0) :
    (⟨x.val >>> s, x.poison >>> s, hx⟩ : LLVM.Byte w) ⊒
      ⟨y.val >>> s, y.poison >>> s, hy⟩ := by
  rw [byte_isRefinedBy_iff] at h ⊢
  intro i hi
  simp only [BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight]
  by_cases hlt : s.toNat + i < w
  · exact h (s.toNat + i) hlt
  · right
    exact ⟨by rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)],
      BitVec.getLsbD_of_ge _ _ (by omega)⟩

/-- If the source byte loses no bit when shifted left (the `nuw` check of `LLVM.Byte.shl`), then
neither does a byte refining it: the bits shifted out are concrete zeros in the source, hence also
in the target. -/
private theorem byte_shl_noWrap_of_isRefinedBy {w : Nat} {x y : LLVM.Byte w} (h : x ⊒ y)
    (s : BitVec w) (hv : (x.val <<< s) >>> s = x.val)
    (hp : (x.poison <<< s) >>> s = x.poison) :
    (y.val <<< s) >>> s = y.val ∧ (y.poison <<< s) >>> s = y.poison := by
  rw [byte_isRefinedBy_iff] at h
  rw [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq'] at hv hp
  rw [bv_shiftLeft_ushiftRight_eq_self_iff] at hv hp
  constructor <;>
    · rw [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', bv_shiftLeft_ushiftRight_eq_self_iff]
      intro i hi hw
      rcases h i hi with hpoison | ⟨hval, hypoison⟩
      · simp [hp i hi hw] at hpoison
      · first
          | (rw [← hval]; exact hv i hi hw)
          | exact hypoison

/-- If the source byte loses no bit when shifted right (the `exact` check of `LLVM.Byte.lshr`),
then neither does a byte refining it. -/
private theorem byte_lshr_exact_of_isRefinedBy {w : Nat} {x y : LLVM.Byte w} (h : x ⊒ y)
    (s : BitVec w) (hv : (x.val >>> s) <<< s = x.val)
    (hp : (x.poison >>> s) <<< s = x.poison) :
    (y.val >>> s) <<< s = y.val ∧ (y.poison >>> s) <<< s = y.poison := by
  rw [byte_isRefinedBy_iff] at h
  rw [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq'] at hv hp
  rw [bv_ushiftRight_shiftLeft_eq_self_iff] at hv hp
  constructor <;>
    · rw [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', bv_ushiftRight_shiftLeft_eq_self_iff]
      intro i hi
      by_cases hiw : i < w
      · rcases h i hiw with hpoison | ⟨hval, hypoison⟩
        · simp [hp i hi] at hpoison
        · first
            | (rw [← hval]; exact hv i hi)
            | exact hypoison
      · exact BitVec.getLsbD_of_ge _ _ (by omega)

/-- `LLVM.Byte.shl` as a conditional chain: unlike `LLVM.Byte.lshr` it is written as a `do`-block,
which is awkward to case-split on directly. -/
private theorem byte_shl_eq {w : Nat} (x : LLVM.Byte w) (y : LLVM.Int w) (nuw : Bool) :
    LLVM.Byte.shl x y nuw =
      if y.isPoison || y.getValueD ≥ w then LLVM.Byte.allPoison
      else if nuw ∧ (x.val <<< y.getValueD) >>> y.getValueD ≠ x.val then LLVM.Byte.allPoison
      else if nuw ∧ (x.poison <<< y.getValueD) >>> y.getValueD ≠ x.poison then LLVM.Byte.allPoison
      else ⟨x.val <<< y.getValueD, x.poison <<< y.getValueD, by
        simp [← BitVec.shiftLeft_and_distrib, x.h]⟩ := by
  cases y with
  | poison => simp [LLVM.Byte.shl, Id.run, LLVM.Int.isPoison_of_poison]
  | val y' =>
    simp only [LLVM.Byte.shl, Id.run, LLVM.Int.isPoison_of_val, LLVM.Int.getValueD_val,
      Bool.false_or, decide_eq_true_eq]
    repeat' split
    all_goals first | rfl | simp_all | (exfalso; bv_omega)

/-- `LLVM.Byte.shl` is monotone in both of its operands. -/
private theorem byte_shl_mono {w : Nat} (x y : LLVM.Byte w) (a b : LLVM.Int w) (nuw : Bool)
    (hxy : x ⊒ y) (hab : a ⊒ b) :
    LLVM.Byte.shl x a nuw ⊒ LLVM.Byte.shl y b nuw := by
  cases a with
  | poison =>
    rw [byte_shl_eq]
    simp only [LLVM.Int.isPoison_of_poison, Bool.true_or, if_true]
    exact byte_allPoison_isRefinedBy _
  | val s =>
    rw [int_eq_of_val_isRefinedBy hab, byte_shl_eq, byte_shl_eq]
    simp only [LLVM.Int.isPoison_of_val, LLVM.Int.getValueD_val, Bool.false_or]
    split
    · exact byte_allPoison_isRefinedBy _
    · by_cases hnuw : nuw = true
      · subst hnuw
        split
        · exact byte_allPoison_isRefinedBy _
        · next hv =>
          split
          · exact byte_allPoison_isRefinedBy _
          · next hp =>
            have hv' : (x.val <<< s) >>> s = x.val := by simpa using hv
            have hp' : (x.poison <<< s) >>> s = x.poison := by simpa using hp
            obtain ⟨hvy, hpy⟩ := byte_shl_noWrap_of_isRefinedBy hxy s hv' hp'
            rw [if_neg (by simpa using hvy), if_neg (by simpa using hpy)]
            exact byte_shiftLeft_isRefinedBy hxy s _ _
      · simp only [Bool.not_eq_true] at hnuw
        subst hnuw
        simp only [Bool.false_eq_true, false_and, if_false]
        exact byte_shiftLeft_isRefinedBy hxy s _ _

/-- `LLVM.Byte.lshr` is monotone in both of its operands. -/
private theorem byte_lshr_mono {w : Nat} (x y : LLVM.Byte w) (a b : LLVM.Int w) (exact : Bool)
    (hxy : x ⊒ y) (hab : a ⊒ b) :
    LLVM.Byte.lshr x a exact ⊒ LLVM.Byte.lshr y b exact := by
  cases a with
  | poison =>
    simp only [LLVM.Byte.lshr, LLVM.Int.isPoison_of_poison, Bool.true_or, if_true]
    exact byte_allPoison_isRefinedBy _
  | val s =>
    rw [int_eq_of_val_isRefinedBy hab]
    simp only [LLVM.Byte.lshr, LLVM.Int.isPoison_of_val, LLVM.Int.getValueD_val, Bool.false_or]
    split
    · exact byte_allPoison_isRefinedBy _
    · by_cases hexact : exact = true
      · subst hexact
        split
        · exact byte_allPoison_isRefinedBy _
        · next hv =>
          split
          · exact byte_allPoison_isRefinedBy _
          · next hp =>
            have hv' : (x.val >>> s) <<< s = x.val := by simpa using hv
            have hp' : (x.poison >>> s) <<< s = x.poison := by simpa using hp
            obtain ⟨hvy, hpy⟩ := byte_lshr_exact_of_isRefinedBy hxy s hv' hp'
            rw [if_neg (by simpa using hvy), if_neg (by simpa using hpy)]
            exact byte_ushiftRight_isRefinedBy hxy s _ _
      · simp only [Bool.not_eq_true] at hexact
        subst hexact
        simp only [Bool.false_eq_true, false_and, if_false]
        exact byte_ushiftRight_isRefinedBy hxy s _ _

/-- `LLVM.Byte.trunc` is monotone. -/
private theorem byte_trunc_mono {w w' : Nat} (x y : LLVM.Byte w) (h : x ⊒ y) :
    LLVM.Byte.trunc x w' ⊒ LLVM.Byte.trunc y w' := by
  rw [byte_isRefinedBy_iff] at h ⊢
  intro i hi
  simp only [LLVM.Byte.trunc, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  by_cases hiw : i < w
  · exact h i hiw
  · right
    exact ⟨by rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)],
      BitVec.getLsbD_of_ge _ _ (by omega)⟩

/-! ### Monotonicity of the `llvm` dialect interpreter -/

/-- Two single-integer-result interpretations refine each other as soon as the integers do. -/
private theorem interp_llvm_int_isRefinedBy {bw : Nat} {v v' : LLVM.Int bw} (mem : MemoryState) :
    v ⊒ v' →
    Interp.isRefinedBy InterpretResultIsRefinedBy
      (pure (#[RuntimeValue.int bw v], mem, none))
      (pure (#[RuntimeValue.int bw v'], mem, none)) := by
  intro hv
  refine ⟨?_, rfl, trivial⟩
  simp only [RuntimeValue.arrayIsRefinedBy_singleton]
  exact ⟨rfl, by simpa using hv⟩

/-- Two single-byte-result interpretations refine each other as soon as the bytes do. -/
private theorem interp_llvm_byte_isRefinedBy {bw : Nat} {v v' : LLVM.Byte bw} (mem : MemoryState) :
    v ⊒ v' →
    Interp.isRefinedBy InterpretResultIsRefinedBy
      (pure (#[RuntimeValue.byte bw v], mem, none))
      (pure (#[RuntimeValue.byte bw v'], mem, none)) := by
  intro hv
  refine ⟨?_, rfl, trivial⟩
  simp only [RuntimeValue.arrayIsRefinedBy_singleton]
  exact ⟨rfl, by simpa using hv⟩

/--
`Llvm.interpretOp'` is monotone in its operands, except for three opcodes that *materialise poison
into a representation that cannot hold it*, and so are genuinely **not** monotone for this
relation:

* `llvm.store` writes poison to memory as an empoisoned byte range (`MemoryState.empoison`), while
  storing the concrete value that refines the poison writes those bytes and *clears* their poison
  mask (`MemoryState.store`). Both stores succeed, but the resulting memories differ, and the
  relation demands that they be equal.
* `llvm.freeze` turns poison into a fixed concrete value: `LLVM.Int.freeze poison = 0`, while
  freezing the concrete value `1` that refines poison yields `1`, and `0 ⊒ 1` is false (a concrete
  integer is refined only by itself). The same happens for byte operands, whose poison mask
  `freeze` clears while keeping the value bits.
* `llvm.bitcast` of a *byte* to a *pointer* goes through `LLVM.Byte.toUInt64`, which maps a byte
  with any poison bit to the address `0`, while the concrete byte `1` that refines it maps to the
  address `1`; addresses carry no poison, so refinement on them is equality.

Every other opcode is monotone: the arithmetic, bitwise, comparison, selection and intrinsic
opcodes are pure functions of their operands computed with monotone data-level operations; the
division and remainder opcodes are UB in the source exactly when the target could misbehave; and
the memory and control-flow opcodes either read only poison-free operands (addresses, concrete
integers) or raise UB on a poison operand (`llvm.cond_br`, `llvm.getelementptr`).
-/
theorem Llvm.interpretOp'_monotone {operands operands' : Array RuntimeValue}
    (notStore : opType ≠ Llvm.store) (notFreeze : opType ≠ Llvm.freeze)
    (notBitcast : opType ≠ Llvm.bitcast) :
    operands ⊒ operands' →
    Interp.isRefinedBy InterpretResultIsRefinedBy
      (Llvm.interpretOp' opType properties resultTypes operands blockOperands mem)
      (Llvm.interpretOp' opType properties resultTypes operands' blockOperands mem) := by
  intro h
  cases opType
  /- The three genuinely non-monotone opcodes are excluded by hypothesis. -/
  case store => exact absurd rfl notStore
  case freeze => exact absurd rfl notFreeze
  case bitcast => exact absurd rfl notBitcast
  /- `llvm.mlir.constant` and `llvm.mlir.poison` do not read their operands. -/
  case mlir__constant | mlir__poison =>
    all_goals
      simp only [Llvm.interpretOp']
      exact interpretResult_isRefinedBy_refl _
  /- `llvm.unreachable` is UB, which is refined by anything. -/
  case unreachable => exact Interp.isRefinedBy_ub_target
  /- The binary integer opcodes: their data-level operation is monotone. -/
  case add | sub | mul | ashr | and | or | xor =>
    all_goals
      simp only [Llvm.interpretOp']
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
          exact interp_llvm_int_isRefinedBy mem (by grind)
      · exact Interp.isRefinedBy_none_target
  /- The binary integer intrinsics, closed with the data-level lemmas proved above. -/
  case intr__smax | intr__smin | intr__umax | intr__umin | intr__sadd__sat | intr__uadd__sat
      | intr__ssub__sat | intr__usub__sat | intr__sshl__sat | intr__ushl__sat =>
    all_goals
      simp only [Llvm.interpretOp']
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
          refine interp_llvm_int_isRefinedBy mem ?_
          first
            | exact int_smax_mono _ _ _ _ hl hr
            | exact int_smin_mono _ _ _ _ hl hr
            | exact int_umax_mono _ _ _ _ hl hr
            | exact int_umin_mono _ _ _ _ hl hr
            | exact int_saddSat_mono _ _ _ _ hl hr
            | exact int_uaddSat_mono _ _ _ _ hl hr
            | exact int_ssubSat_mono _ _ _ _ hl hr
            | exact int_usubSat_mono _ _ _ _ hl hr
            | exact int_sshlSat_mono _ _ _ _ hl hr
            | exact int_ushlSat_mono _ _ _ _ hl hr
      · exact Interp.isRefinedBy_none_target
  /- `llvm.icmp`: two integer operands and a one-bit result. -/
  case icmp =>
    simp only [Llvm.interpretOp']
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
        exact interp_llvm_int_isRefinedBy mem (by grind)
    · exact Interp.isRefinedBy_none_target
  /- The unary integer intrinsics. -/
  case intr__ctlz | intr__cttz | intr__ctpop | intr__bswap | intr__bitreverse | intr__abs =>
    all_goals
      simp only [Llvm.interpretOp']
      split
      · next bw x heq =>
        obtain ⟨_, heq', hx⟩ := arrayIsRefinedBy_toList_one h heq
        obtain ⟨x', rfl, hxx⟩ := RuntimeValue.int_of_isRefinedBy hx
        rw [heq']
        dsimp only
        refine interp_llvm_int_isRefinedBy mem ?_
        first
          | exact int_ctlz_mono _ _ _ hxx
          | exact int_cttz_mono _ _ _ hxx
          | exact int_ctpop_mono _ _ hxx
          | exact int_bswap_mono _ _ hxx
          | exact int_bitreverse_mono _ _ hxx
          | exact int_abs_mono _ _ _ hxx
      · exact Interp.isRefinedBy_none_target
  /- The unsigned division/remainder opcodes: a poison or zero divisor is UB in the source. -/
  case udiv | urem =>
    all_goals
      simp only [Llvm.interpretOp']
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
            · exact interp_llvm_int_isRefinedBy mem (by grind)
      · exact Interp.isRefinedBy_none_target
  /- The signed division/remainder opcodes: additionally, the overflowing `intMin / -1` is UB. -/
  case sdiv | srem =>
    all_goals
      simp only [Llvm.interpretOp']
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
                  · exact interp_llvm_int_isRefinedBy mem (by grind)
              · exact interp_llvm_int_isRefinedBy mem (by grind)
      · exact Interp.isRefinedBy_none_target
  /- The funnel shifts: three integer operands. -/
  case intr__fshl | intr__fshr =>
    all_goals
      simp only [Llvm.interpretOp']
      split
      · next bw a bw' b bw'' c heq =>
        obtain ⟨_, _, _, heq', ha, hb, hc⟩ := arrayIsRefinedBy_toList_three h heq
        obtain ⟨a', rfl, haa⟩ := RuntimeValue.int_of_isRefinedBy ha
        obtain ⟨b', rfl, hbb⟩ := RuntimeValue.int_of_isRefinedBy hb
        obtain ⟨c', rfl, hcc⟩ := RuntimeValue.int_of_isRefinedBy hc
        rw [heq']
        dsimp only
        split
        · exact Interp.isRefinedBy_none_target
        · next hbw =>
          have hbw' : bw' = bw := by omega
          subst hbw'
          split
          · exact Interp.isRefinedBy_none_target
          · next hbw2 =>
            have hbw2' : bw'' = bw' := by omega
            subst hbw2'
            simp only [LLVM.Int.cast_self]
            refine interp_llvm_int_isRefinedBy mem ?_
            first
              | exact int_fshl_mono _ _ _ _ _ _ haa hbb hcc
              | exact int_fshr_mono _ _ _ _ _ _ haa hbb hcc
      · exact Interp.isRefinedBy_none_target
  /- `llvm.select`: three integer operands, and `LLVM.Int.select` is monotone. -/
  case select =>
    simp only [Llvm.interpretOp']
    split
    · next cond bw lhs bw' rhs heq =>
      obtain ⟨_, _, _, heq', hc, hx, hy⟩ := arrayIsRefinedBy_toList_three h heq
      obtain ⟨cond', rfl, hcond⟩ := RuntimeValue.int_of_isRefinedBy hc
      obtain ⟨lhs', rfl, hl⟩ := RuntimeValue.int_of_isRefinedBy hx
      obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy hy
      simp only [heq']
      split
      · exact Interp.isRefinedBy_none_target
      · next hbw =>
        have hbw' : bw' = bw := by omega
        subst hbw'
        simp only [LLVM.Int.cast_self]
        exact interp_llvm_int_isRefinedBy mem
          (LLVM.Int.select_mono lhs rhs lhs' rhs' cond cond' hl hr hcond)
    · exact Interp.isRefinedBy_none_target
  /- The integer widening casts. -/
  case zext | sext =>
    all_goals
      simp only [Llvm.interpretOp']
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
            · exact interp_llvm_int_isRefinedBy mem (by grind)
          · exact Interp.isRefinedBy_none_target
        · exact Interp.isRefinedBy_none_target
      · exact Interp.isRefinedBy_none_target
  /- `llvm.trunc` accepts an integer or a byte operand. -/
  case trunc =>
    simp only [Llvm.interpretOp']
    split
    · next val heq =>
      obtain ⟨val', heq', hv⟩ := arrayIsRefinedBy_toList_one h heq
      cases val with
      | int w v =>
        obtain ⟨v', rfl, hvv⟩ := RuntimeValue.int_of_isRefinedBy hv
        simp only [heq']
        repeat' split
        all_goals first
          | exact Interp.isRefinedBy_none_target
          | exact interp_llvm_int_isRefinedBy mem (by grind)
      | byte w b =>
        obtain ⟨b', rfl, hbb⟩ := RuntimeValue.byte_of_isRefinedBy hv
        simp only [heq']
        repeat' split
        all_goals first
          | exact Interp.isRefinedBy_none_target
          | exact interp_llvm_byte_isRefinedBy mem (byte_trunc_mono _ _ hbb)
      | addr a =>
        rw [RuntimeValue.addr_of_isRefinedBy hv] at heq'
        simp only [heq']
        repeat' split
        all_goals exact Interp.isRefinedBy_none_target
      | reg r =>
        rw [RuntimeValue.reg_of_isRefinedBy hv] at heq'
        simp only [heq']
        repeat' split
        all_goals exact Interp.isRefinedBy_none_target
      | float bw f =>
        rw [RuntimeValue.float_of_isRefinedBy hv] at heq'
        simp only [heq']
        repeat' split
        all_goals exact Interp.isRefinedBy_none_target
    · exact Interp.isRefinedBy_none_target
  /- `llvm.shl` accepts an integer or a byte left-hand side. -/
  case shl =>
    simp only [Llvm.interpretOp']
    split
    · next lhs bw' rhs heq =>
      obtain ⟨_, _, heq', hx, hy⟩ := arrayIsRefinedBy_toList_two h heq
      obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy hy
      rw [heq']
      dsimp only
      cases lhs with
      | int bw v =>
        obtain ⟨v', rfl, hvv⟩ := RuntimeValue.int_of_isRefinedBy hx
        dsimp only
        split
        · exact Interp.isRefinedBy_none_target
        · next hbw =>
          have hbw' : bw' = bw := by omega
          subst hbw'
          simp only [LLVM.Int.cast_self]
          exact interp_llvm_int_isRefinedBy mem (by grind)
      | byte bw b =>
        obtain ⟨b', rfl, hbb⟩ := RuntimeValue.byte_of_isRefinedBy hx
        dsimp only
        split
        · exact Interp.isRefinedBy_none_target
        · next hbw =>
          have hbw' : bw' = bw := by omega
          subst hbw'
          split
          · exact Interp.isRefinedBy_none_target
          · simp only [LLVM.Int.cast_self]
            exact interp_llvm_byte_isRefinedBy mem (byte_shl_mono _ _ _ _ _ hbb hr)
      | addr a =>
        rw [RuntimeValue.addr_of_isRefinedBy hx]
        exact Interp.isRefinedBy_none_target
      | reg r =>
        rw [RuntimeValue.reg_of_isRefinedBy hx]
        exact Interp.isRefinedBy_none_target
      | float bw f =>
        rw [RuntimeValue.float_of_isRefinedBy hx]
        exact Interp.isRefinedBy_none_target
    · exact Interp.isRefinedBy_none_target
  /- `llvm.lshr` accepts an integer or a byte left-hand side. -/
  case lshr =>
    simp only [Llvm.interpretOp']
    split
    · next lhs bw' rhs heq =>
      obtain ⟨_, _, heq', hx, hy⟩ := arrayIsRefinedBy_toList_two h heq
      obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy hy
      rw [heq']
      dsimp only
      cases lhs with
      | int bw v =>
        obtain ⟨v', rfl, hvv⟩ := RuntimeValue.int_of_isRefinedBy hx
        dsimp only
        split
        · exact Interp.isRefinedBy_none_target
        · next hbw =>
          have hbw' : bw' = bw := by omega
          subst hbw'
          simp only [LLVM.Int.cast_self]
          exact interp_llvm_int_isRefinedBy mem (by grind)
      | byte bw b =>
        obtain ⟨b', rfl, hbb⟩ := RuntimeValue.byte_of_isRefinedBy hx
        dsimp only
        split
        · exact Interp.isRefinedBy_none_target
        · next hbw =>
          have hbw' : bw' = bw := by omega
          subst hbw'
          simp only [LLVM.Int.cast_self]
          exact interp_llvm_byte_isRefinedBy mem (byte_lshr_mono _ _ _ _ _ hbb hr)
      | addr a =>
        rw [RuntimeValue.addr_of_isRefinedBy hx]
        exact Interp.isRefinedBy_none_target
      | reg r =>
        rw [RuntimeValue.reg_of_isRefinedBy hx]
        exact Interp.isRefinedBy_none_target
      | float bw f =>
        rw [RuntimeValue.float_of_isRefinedBy hx]
        exact Interp.isRefinedBy_none_target
    · exact Interp.isRefinedBy_none_target
  /- `llvm.return` and `llvm.br` hand their operands to the control-flow action, which refines
  pointwise. -/
  case «return» =>
    simp only [Llvm.interpretOp']
    exact ⟨RuntimeValue.arrayIsRefinedBy_refl _, rfl, h⟩
  case br =>
    simp only [Llvm.interpretOp']
    split
    · exact ⟨RuntimeValue.arrayIsRefinedBy_refl _, rfl, rfl, h⟩
    · exact Interp.isRefinedBy_none_target
  /- `llvm.cond_br`: a poison condition is UB in the source, a concrete condition is refined only
  by itself, and the branch arguments refine because `Array.extract` preserves refinement. -/
  case cond_br =>
    simp only [Llvm.interpretOp']
    split
    · split
      · next condVal hcond =>
        obtain ⟨condVal', hcond', hcc⟩ := RuntimeValue.arrayIsRefinedBy_getElem? h hcond
        rw [hcond']
        split
        · match condVal, hcc with
          | .int 1 (.val cond), hcc =>
            obtain ⟨c', rfl, hc⟩ := RuntimeValue.int_of_isRefinedBy hcc
            rw [int_eq_of_val_isRefinedBy hc]
            have hsizes : operands.size = operands'.size := h.1
            by_cases hcond1 : cond = 1#1
            · simp only [if_pos hcond1]
              exact ⟨RuntimeValue.arrayIsRefinedBy_refl _, rfl, rfl,
                RuntimeValue.arrayIsRefinedBy_extract h _ _⟩
            · simp only [if_neg hcond1, ← hsizes]
              exact ⟨RuntimeValue.arrayIsRefinedBy_refl _, rfl, rfl,
                RuntimeValue.arrayIsRefinedBy_extract h _ _⟩
          | .int 1 .poison, _ => exact Interp.isRefinedBy_ub_target
          | .int 0 v, _ => exact Interp.isRefinedBy_none_target
          | .int (n + 2) v, _ => exact Interp.isRefinedBy_none_target
          | .byte bw v, _ => exact Interp.isRefinedBy_none_target
          | .addr a, _ => exact Interp.isRefinedBy_none_target
          | .reg r, _ => exact Interp.isRefinedBy_none_target
          | .float bw f, _ => exact Interp.isRefinedBy_none_target
        · exact Interp.isRefinedBy_none_target
      · exact Interp.isRefinedBy_none_target
    · exact Interp.isRefinedBy_none_target
  /- `llvm.alloca` and `llvm.load` read only poison-free operands (a concrete count, an address),
  which are refined only by themselves, so both sides compute the very same result. -/
  case alloca =>
    simp only [Llvm.interpretOp']
    split
    · next bw count heq =>
      obtain ⟨_, heq', hx⟩ := arrayIsRefinedBy_toList_one h heq
      obtain ⟨count', rfl, hc⟩ := RuntimeValue.int_of_isRefinedBy hx
      rw [int_eq_of_val_isRefinedBy hc] at heq'
      rw [heq']
      exact interpretResult_isRefinedBy_refl _
    · exact Interp.isRefinedBy_none_target
  case load =>
    simp only [Llvm.interpretOp']
    split
    · next addr heq =>
      obtain ⟨_, heq', hx⟩ := arrayIsRefinedBy_toList_one h heq
      rw [RuntimeValue.addr_of_isRefinedBy hx] at heq'
      rw [heq']
      exact interpretResult_isRefinedBy_refl _
    · exact Interp.isRefinedBy_none_target
  /- `llvm.getelementptr`: a poison index is UB in the source, a concrete one is refined only by
  itself. -/
  case getelementptr =>
    simp only [Llvm.interpretOp']
    split
    · next ptr bw idx heq =>
      obtain ⟨_, _, heq', hp, hi⟩ := arrayIsRefinedBy_toList_two h heq
      obtain ⟨idx', rfl, hidx⟩ := RuntimeValue.int_of_isRefinedBy hi
      rw [RuntimeValue.addr_of_isRefinedBy hp] at heq'
      rw [heq']
      cases idx with
      | poison =>
        simp only [bind, pure, liftM, monadLift, MonadLift.monadLift]
        repeat' split
        all_goals first
          | exact Interp.isRefinedBy_none_target
          | exact Interp.isRefinedBy_ub_target
      | val v =>
        rw [int_eq_of_val_isRefinedBy hidx]
        exact interpretResult_isRefinedBy_refl _
    · exact Interp.isRefinedBy_none_target
  /- The remaining `llvm` opcodes are not interpreted, so the source interpretation fails. -/
  all_goals exact Interp.isRefinedBy_none_target

end LlvmMonotone

/--
`interpretOp'` is monotone in its operands, except for the opcodes that materialise poison into a
representation that cannot hold it, and so are genuinely *not* monotone for this relation:

* `llvm.store` writes poison into memory as an empoisoned byte range, while storing the concrete
  value that refines it clears that poison mask, and the relation requires the resulting memories
  to be *equal* (see `Llvm.interpretOp'_monotone`).
* `llvm.freeze` maps poison to a fixed concrete value, which is *not* refined by the freeze of the
  concrete value that refines the poison (see `Llvm.interpretOp'_monotone`).
* `llvm.bitcast` of a byte to a pointer maps a poisoned byte to the address `0`, which is not
  refined by the address the refining concrete byte casts to (see `Llvm.interpretOp'_monotone`).
* `builtin.unrealized_conversion_cast` from an integer to a register maps poison to the register
  `0` (`LLVM.Int.toReg`), while the concrete value that refines it maps to a different register,
  and refinement on registers is equality (registers cannot be poison).
-/
theorem interpretOp'_monotone
    (opType : OpCode) (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands operands' : Array RuntimeValue) (blockOperands : Array BlockPtr) (mem : MemoryState)
    (notStore : opType ≠ .llvm .store)
    (notFreeze : opType ≠ .llvm .freeze)
    (notBitcast : opType ≠ .llvm .bitcast)
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
    exact Llvm.interpretOp'_monotone (by grind) (by grind) (by grind) h
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
  /- `arith`, `cf`, `riscv_cf` and `comb` do not touch memory: lift their own monotonicity through
  the memory threading. -/
  case arith op =>
    simp only [interpretOp']
    exact interpretResult_isRefinedBy_of_memFree mem
      (Arith.interpretOp'_monotone op properties resultTypes operands operands' blockOperands h)
  case cf op =>
    simp only [interpretOp']
    exact interpretResult_isRefinedBy_of_memFree mem
      (Cf.interpretOp'_monotone op properties resultTypes operands operands' blockOperands h)
  case riscv_cf op =>
    simp only [interpretOp']
    exact interpretResult_isRefinedBy_of_memFree mem
      (Riscv_Cf.interpretOp'_monotone op properties resultTypes operands operands' blockOperands h)
  case comb op =>
    simp only [interpretOp']
    exact interpretResult_isRefinedBy_of_memFree mem
      (Comb.interpretOp'_monotone op properties operands operands' blockOperands h)
  /- The remaining dialects are not interpreted, so the source interpretation fails. -/
  all_goals simp [interpretOp', Interp.isRefinedBy]

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
