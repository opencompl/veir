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

set_option warn.sorry false in
theorem interpretOp'_monotone
    (opType : OpCode) (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands operands' : Array RuntimeValue) (blockOperands : Array BlockPtr) (mem : MemoryState) :
    operands ⊒ operands' →
    Interp.isRefinedBy (α := Array RuntimeValue × MemoryState × Option ControlFlowAction)
      (fun r₁ r₂ => r₁.1 ⊒ r₂.1 ∧ r₁.2.1 = r₂.2.1 ∧
        ControlFlowAction.optionIsRefinedBy r₁.2.2 r₂.2.2)
      (interpretOp' opType properties resultTypes operands blockOperands mem)
      (interpretOp' opType properties resultTypes operands' blockOperands mem) := by
  sorry

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

/-- `VariableState.getOperandValues` is monotone with respect to the state refinement relation:
refined variable states produce refined operand arrays. -/
theorem VariableState.getOperandValues_isRefinedBy
    {srcVars : VariableState ctx} {tgtVars : VariableState ctx'} {mapping : ValueMapping ctx ctx'}
    (hRef : srcVars.isRefinedBy tgtVars mapping) (opIn : op.InBounds ctx.raw)
    (hOperands : op'.getOperands! ctx'.raw = mapping.applyToArray (op.getOperands! ctx.raw))
    (hSrc : srcVars.getOperandValues op = some srcVal) :
    ∃ tgtVal, tgtVars.getOperandValues op' = some tgtVal ∧ srcVal ⊒ tgtVal := by
  simp only [VariableState.isRefinedBy] at hRef
  have ⟨hsize, hSrc⟩ := VariableState.getOperandValues_eq_some_iff.mp hSrc
  have hSrc₂ := Array.mapM_option_isSome (f := tgtVars.getVar?) (l := op'.getOperands! ctx'.raw)
  have ⟨r, hr⟩ := hSrc₂ (by grind [ValueMapping.applyToArray])
  simp only [getOperandValues, hr, Option.some.injEq, exists_eq_left']
  simp only [RuntimeValue.arrayIsRefinedBy]
  constructor
  · grind
  · intro i hi
    grind [Array.mapM_option_eq_some_implies hr i (by grind), ValueMapping.applyToArray]

/-- `setResultValues?` preserves the state refinement. If the source/target variable states are
related by `mapping`, the freshly-computed result values refine (`resValues ⊒ resValues'`), `op`
and `op'` have the same results related by `mapping` (`hResults` and `hReflect`), then the target
`setResultValues?` also succeeds and the states after binding the results are again related by
`mapping`. -/
theorem VariableState.setResultValues?_isRefinedBy
    {srcVars : VariableState ctx} {tgtVars : VariableState ctx'}
    (hRef : srcVars.isRefinedBy tgtVars mapping) {newSrcVars : VariableState ctx}
    {srcVals tgtVals : Array RuntimeValue} (hVals : srcVals ⊒ tgtVals)
    (hResults : op'.getResults! ctx'.raw = mapping.applyToArray (op.getResults! ctx.raw))
    (hReflect : mapping.ReflectsResults op op')
    (hSrc : srcVars.setResultValues? op srcVals opIn = some newSrcVars)
    (tgtValsConforms : RuntimeValue.ArrayConforms tgtVals (op'.getResultTypes! ctx'.raw))
    (opIn' : op'.InBounds ctx'.raw) :
    ∃ newTgtVars, tgtVars.setResultValues? op' tgtVals opIn' = some newTgtVars ∧
                  newSrcVars.isRefinedBy newTgtVars mapping := by
  /- Conformance of the (refined) target values implies target success. -/
  have ⟨newTgtVars, hTgt⟩ :=
    (VariableState.setResultValues?_isSome_iff_conforms
      (varState := tgtVars) (inBounds := opIn')).mp tgtValsConforms
  simp only [hTgt, Option.some.injEq, exists_eq_left']
  /- Reason per element in the source and result value arrays. -/
  intro val valIn sv hsv
  /- Do a case analysis on wether or not the value is one of `op` results.
  If it is not, the value is not a result of `op'`, and the refinement follows from the
  original `VariableState` refinement.
  If it is, then because of `hReflect`, the value is mapped to a result of `op'`, and the
  refinement follows the `RuntimeValue` array refinement. -/
  cases OperationPtr.getResults!_not_mem_or_eq_getResult ctx.raw val op
  next hNotMem => grind [VariableState.isRefinedBy]
  next hMem =>
    have hfix := ValueMapping.applyToArray_getResults!_ext opIn hResults.symm
    grind [RuntimeValue.arrayIsRefinedBy]

/--
`interpretOp` is monotone under a *cross-context* interpreter-state refinement.

Lift `interpretOp'_monotone` through `getOperandValues` and `setResultValues?`. The source state
lives in `ctx`, the target in `ctx'`, related by `InterpreterState.isRefinedBy` through the value
renaming `mapping` (for the unchanged majority, `mapping` is the identity-on-`ValuePtr` `InBounds`-embedding).
The *frame hypotheses* say that `op` carries identical intrinsic data in both contexts
(`getOpType!`/`getProperties!`/`getResultTypes!`/`getSuccessors!` agree, and `mapping` carries `op`'s
operands in `ctx` to its operands in `ctx'`), so both sides run the same dialect step.

The conclusion relates the two `interpretOp` results: their interpreter states are again related by
`InterpreterState.isRefinedBy mapping`, and their control flow actions by `ControlFlowAction`-refinement.
Because the state relation constrains only values defined in *both* states, `op`'s freshly-set
results are added on both sides and re-established by `interpretOp'_monotone`, while pre-existing
values stay defined and refined.
-/
theorem interpretOp_monotone
    {ctx ctx' : WfIRContext OpCode}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    {mapping : ValueMapping ctx ctx'}
    (opIn : op.InBounds ctx.raw) (opIn' : op'.InBounds ctx'.raw)
    (hState : state.isRefinedBy state' mapping)
    -- Frame: `op` carries identical intrinsic data in both contexts, so both sides take the
    -- same dialect step.
    (hOpType : op'.getOpType! ctx'.raw = op.getOpType! ctx.raw)
    (hProps : op'.getProperties! ctx'.raw (op'.getOpType! ctx'.raw) =
      hOpType ▸ op.getProperties! ctx.raw (op.getOpType! ctx.raw))
    (hResultTypes : op'.getResultTypes! ctx'.raw = op.getResultTypes! ctx.raw)
    (hSuccessors : op'.getSuccessors! ctx'.raw = op.getSuccessors! ctx.raw)
    (hOperands : op'.getOperands! ctx'.raw = mapping.applyToArray (op.getOperands! ctx.raw))
    (hResults : op'.getResults! ctx'.raw = mapping.applyToArray (op.getResults! ctx.raw) (by grind))
    (hReflect : mapping.ReflectsResults op op')
    (opVerif' : op'.Verified ctx' opIn') :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState ctx' × Option ControlFlowAction) =>
        r₁.1.isRefinedBy r₂.1 mapping ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (interpretOp op state opIn)
      (interpretOp op' state' opIn') := by
  -- If the source interpretation fails, then the refinement is trivial
  by_cases hsource : interpretOp op state opIn = none; simp [hsource, Interp.isRefinedBy]
  -- Source/target operands are defined, and memory is equal.
  have ⟨operands, hSrcOps⟩ : ∃ operands, state.variables.getOperandValues op = some operands := by
    grind [interpretOp]
  obtain ⟨operands', hTgtOps, hOpsRef⟩ :=
    VariableState.getOperandValues_isRefinedBy hState.2 opIn hOperands hSrcOps
  have hMem : state.memory = state'.memory := hState.1
  -- Add the refinement of `interpretOp'` on `op` with `operands` and `operands'`
  have hPR1 := interpretOp'_monotone (op.getOpType! ctx.raw)
    (op.getProperties! ctx.raw (op.getOpType! ctx.raw)) (op.getResultTypes! ctx.raw)
    operands operands' (op.getSuccessors! ctx.raw) state.memory hOpsRef
  -- Add the equality between `interpretOp'` on `operands'`
  have hInterp'Eq : op'.interpret ctx'.raw operands' state'.memory =
                    op.interpret ctx.raw operands' state.memory := by
     grind [interpretOp'_opType_cast]
  /- Do a case analysis on the source interpretation -/
  rcases hsrc : interpretOp op state opIn with _ | (⟨state₂, act⟩ | _)
  · -- If the source interpretation fails, then the refinement is trivial
    simp [Interp.isRefinedBy]
  · /- If the source interpretation returns a new state, we need to prove that (1) the target
       interpretation also returns a new state, and (2) the new states are in the refinement relation. -/
    simp only [Interp.isRefinedBy_ok_target_iff, Prod.exists]
    have ⟨resValues, hinterp', hResValues⟩ :=
      (interpretOp_ok_iff_of_getOperandValues_eq_some hSrcOps).mp hsrc
    simp only [hinterp', Interp.isRefinedBy_ok_target_iff, Prod.exists] at hPR1
    have ⟨resValues', memory'₂, act', hinterp'Tgt, resValuesRef, memoryEq, actRef⟩ := hPR1
    subst memory'₂
    simp only [← hInterp'Eq] at hinterp'Tgt
    simp only [interpretOp, hTgtOps, bind, hinterp'Tgt, liftM, monadLift, MonadLift.monadLift]
    have := interpretOp'_results_conform (opInBounds := opIn') opVerif' (VariableState.getOperandValues_conforms hTgtOps) hinterp'Tgt
    have ⟨v, hv⟩ := (VariableState.setResultValues?_isSome_iff_conforms state'.variables opIn').mp this
    simp only [Interp, hv, pure, Option.some.injEq, UBOr.ok.injEq, Prod.mk.injEq]
    have stateVarRef : state.variables.isRefinedBy state'.variables mapping := by grind [InterpreterState.isRefinedBy]
    grind [InterpreterState.isRefinedBy, VariableState.setResultValues?_isRefinedBy stateVarRef resValuesRef]
  · /- If the source interpretation returns UB, then we need to prove that the target
       interpretation does not fail. -/
    simp only [Interp.isRefinedBy_ub_target_iff]
    rcases htgt : interpretOp op' state' opIn' with _ | (⟨state₂', act'⟩ | _)
    /- If the target is either ub or a result, then the refinement is trivial. -/
    rotate_left; grind; grind
    have hinterp' := (interpretOp_ub_iff_op_interpret_of_getOperandValues_eq_some hSrcOps).mp hsrc
    simp only [interpretOp, OperationPtr.interpret, hTgtOps, hResultTypes, hSuccessors, ← hMem, liftM, monadLift,
      MonadLift.monadLift] at htgt
    simp only [Interp.isRefinedBy, hinterp'] at hPR1
    split at hPR1; grind; rotate_left; grind; grind
    rename_i _ _ interpTgtRes _ hInterpTgtRes
    simp [interpretOp'_opType_cast hOpType hProps, hInterpTgtRes, bind] at htgt
    cases interpTgtRes
    · simp only [pure] at htgt
      simp only [← hInterp'Eq] at hInterpTgtRes
      have := interpretOp'_results_conform (opInBounds := opIn') opVerif' (VariableState.getOperandValues_conforms hTgtOps) hInterpTgtRes
      split at htgt
      · grind [VariableState.setResultValues?_isSome_iff_conforms (varState := state'.variables)]
      · grind
      · grind
    · grind
