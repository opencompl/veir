module

public import Veir.Passes.InstructionSelection.Branches.Spec
public import Veir.Passes.InstructionSelection.Branches.Casts

import Veir.Interpreter.Lemmas
import Veir.Dialects.GMIR.Lemmas
import Veir.Dialects.RISCV_Cf.Lemmas
import Veir.Dialects.RV64.Lemmas
import Veir.Interpreter.Refinement.Lemmas
import Veir.Interpreter.Refinement.Monotonicity
import all Veir.Interpreter.Basic
import all Veir.Interpreter.VariableState
import all Veir.Interpreter.Refinement.Basic
import all Veir.IR.Basic
import all Veir.Interfaces.FunctionInterfaces
import all Veir.GlobalOpInfo
import all Veir.Dialects.Func.OpInfo

public section

/-!
# The branch lowering refines the module

A module is refined by any module that is its `BranchLowering`. The states of
the two runs are related through the map that sends an argument of a converted
block to its cast, and they are related after the casts at the start of a block,
where every value of the source has its counterpart again. Values are compared
in the memory of the source, which the casts and the branches leave alone.

A compare-and-branch reads the values that the `g_icmp` in front of it
compared. Right after a `g_icmp` runs, its result is what it computes from the
values of its operands, which `CompareFact` records for the branch that follows.
A `g_constant` always holds its value, which `ConstantsHold` records for the
whole run.
-/

namespace Veir

/-! ## Facts about the interpreter that do not depend on the lowering -/

/-- A register is a value of the register type. -/
theorem RuntimeValue.reg_conforms {reg : Data.RISCV.Reg} :
    (RuntimeValue.reg reg).Conforms (RegisterType.mk : TypeAttr) := by
  simp

/-- A refinement of an array of values conforms to the types the array conforms to. -/
theorem RuntimeValue.ArrayConforms.of_isRefinedBy
    {source target : Array RuntimeValue} {types : Array TypeAttr}
    (hConforms : RuntimeValue.ArrayConforms source types)
    (hRefined : source ⊒ target) : RuntimeValue.ArrayConforms target types := by
  refine ⟨by grind [RuntimeValue.arrayIsRefinedBy, RuntimeValue.ArrayConforms], fun i hi => ?_⟩
  have hi' : i < source.size := by grind [RuntimeValue.arrayIsRefinedBy]
  exact (hConforms.2 i hi').of_isRefinedBy (hRefined.2 i hi')

/-- A `FunctionOp` view of `op` is the one that `FunctionOp.of?` finds. -/
theorem FunctionOp.of?_eq_some {op : OperationPtr} {ctx : IRContext OpCode}
    (funcOp : FunctionOp ctx op) : FunctionOp.of? op ctx = some funcOp := by
  obtain ⟨⟨symbolInterface, hSymbol, hName⟩, functionInterface, hFunction⟩ := funcOp
  simp only [FunctionOp.of?]
  split
  next functionInterface' h =>
    obtain rfl : functionInterface' = functionInterface := by
      rw [hFunction] at h; exact (Option.some.inj h).symm
    simp only [Option.some.injEq, FunctionOp.mk.injEq, SymbolOp.mk.injEq, and_true]
    simp [hSymbol]
  next h => simp [hFunction] at h

theorem OperationPtr.getProperties!_cast {op : OperationPtr} {ctx : IRContext OpCode}
    {opType opType' : OpCode} (h : opType = opType') :
    op.getProperties! ctx opType = h ▸ op.getProperties! ctx opType' := by
  subst h; rfl

variable {ctx ctx' : WfIRContext OpCode}

/-- A block sets its arguments and then runs its operations up to the terminator. -/
theorem interpretBlock_eq {block : BlockPtr} {values : Array RuntimeValue}
    {state : InterpreterState ctx} (blockIn : block.InBounds ctx.raw) :
    interpretBlock block values state blockIn =
    match state.variables.setArgumentValues? block values blockIn with
    | none => .fail none
    | some variables =>
      interpretTerminatedOpList (block.operationList ctx.raw ctx.wellFormed blockIn).toList
        ⟨variables, state.memory⟩
        (by grind [BlockPtr.operationListWF, BlockPtr.OpChain]) := by
  have hChain := BlockPtr.operationListWF ctx.raw block blockIn ctx.wellFormed
  simp only [interpretBlock, bind, liftM, monadLift, MonadLift.monadLift]
  rcases state.variables.setArgumentValues? block values blockIn with _ | variables
  · rfl
  · simp only
    split
    next hFirst =>
      have : (block.operationList ctx.raw ctx.wellFormed blockIn) = #[] := by
        have := hChain.first
        grind
      simp [this]
    next firstOp hFirst =>
      rw [interpretOpChain_eq_interpretTerminatedOpList_of_firstOp blockIn (by grind)]

/-- The meaning of an operation whose meaning does not depend on its properties. -/
theorem interpretOp'_eq_of_opType {opType opType' : OpCode} {properties : propertiesOf opType}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {successors : Array BlockPtr}
    {mem : MemoryState} {result : Interp (Array RuntimeValue × MemoryState × Option ControlFlowAction)}
    (hType : opType = opType')
    (hAll : ∀ properties', interpretOp' opType' properties' resultTypes operands successors mem =
      result) :
    interpretOp' opType properties resultTypes operands successors mem = result := by
  subst hType; exact hAll _

/--
  A cast with one operand and one result, whose meaning on the value of the
  operand is known, binds its result to the outcome and changes nothing else.
-/
theorem interpretOp_cast {op : OperationPtr} {state : InterpreterState ctx}
    {type : TypeAttr} {operand : ValuePtr} {input output : RuntimeValue}
    (opIn : op.InBounds ctx.raw)
    (hType : op.getOpType! ctx.raw = .builtin .unrealized_conversion_cast)
    (hResultTypes : op.getResultTypes! ctx.raw = #[type])
    (hOperands : op.getOperands! ctx.raw = #[operand])
    (hInput : state.variables.getVar? operand = some input)
    (hInterp : ∀ properties successors,
      interpretOp' (.builtin .unrealized_conversion_cast) properties #[type] #[input]
        successors state.memory = .ok (#[output], state.memory, none))
    (hConforms : output.Conforms type) :
    ∃ state', interpretOp op state opIn = .ok (state', none) ∧
      state'.memory = state.memory ∧
      ∀ value, state'.variables.getVar? value =
        if value = op.getResult 0 then some output else state.variables.getVar? value := by
  have hVals : state.variables.getOperandValues op = some #[input] := by
    simp [VariableState.getOperandValues, hOperands, hInput]
  have hRun : op.interpret ctx.raw #[input] state.memory = .ok (#[output], state.memory, none) := by
    simp only [OperationPtr.interpret, hResultTypes]
    exact interpretOp'_eq_of_opType hType fun _ => hInterp _ _
  have hConf : RuntimeValue.ArrayConforms #[output] (op.getResultTypes! ctx.raw) := by
    simp [RuntimeValue.ArrayConforms, hResultTypes, hConforms]
  obtain ⟨state', hOk, hMem, hSet⟩ := interpretOp_forward (inBounds := opIn) hVals hRun hConf
  refine ⟨state', hOk, hMem, fun value => ?_⟩
  have hNum : op.getNumResults! ctx.raw = 1 := by
    rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, hResultTypes]; rfl
  rw [VariableState.getVar?_setResultValues? hSet]
  rcases value with ⟨op', index⟩ | arg
  · simp only [OperationPtr.getResult_def, ValuePtr.opResult.injEq, OpResultPtr.mk.injEq, hNum]
    by_cases h : op' = op ∧ index = 0
    · obtain ⟨rfl, rfl⟩ := h; simp
    · simp [h]
  · simp [OperationPtr.getResult_def]

/-- `rv64.get_register` of `x0` binds its result to the register that holds zero. -/
theorem interpretOp_getRegister {op : OperationPtr} {state : InterpreterState ctx}
    (opIn : op.InBounds ctx.raw) (hType : op.getOpType! ctx.raw = .rv64 .get_register)
    (hResultTypes : op.getResultTypes! ctx.raw = #[(RegisterType.mk (some 0) : TypeAttr)])
    (hOperands : op.getOperands! ctx.raw = #[]) :
    ∃ state', interpretOp op state opIn = .ok (state', none) ∧
      state'.memory = state.memory ∧
      ∀ value, state'.variables.getVar? value =
        if value = op.getResult 0 then some (.reg ⟨0⟩) else state.variables.getVar? value := by
  have hVals : state.variables.getOperandValues op = some #[] := by
    simp [VariableState.getOperandValues, hOperands]
  have hRun : op.interpret ctx.raw #[] state.memory = .ok (#[.reg ⟨0⟩], state.memory, none) := by
    simp only [OperationPtr.interpret, hResultTypes]
    exact interpretOp'_eq_of_opType hType fun _ => interpretOp'_rv64_get_register_x0
  have hConf : RuntimeValue.ArrayConforms #[.reg ⟨0⟩] (op.getResultTypes! ctx.raw) := by
    simp [RuntimeValue.ArrayConforms, hResultTypes]
  obtain ⟨state', hOk, hMem, hSet⟩ := interpretOp_forward (inBounds := opIn) hVals hRun hConf
  refine ⟨state', hOk, hMem, fun value => ?_⟩
  have hNum : op.getNumResults! ctx.raw = 1 := by
    rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, hResultTypes]; rfl
  rw [VariableState.getVar?_setResultValues? hSet]
  rcases value with ⟨op', index⟩ | arg
  · simp only [OperationPtr.getResult_def, ValuePtr.opResult.injEq, OpResultPtr.mk.injEq, hNum]
    by_cases h : op' = op ∧ index = 0
    · obtain ⟨rfl, rfl⟩ := h; simp
    · simp [h]
  · simp [OperationPtr.getResult_def]

theorem interpretOpList_congr {ops ops' : List OperationPtr} (h : ops = ops')
    {state : InterpreterState ctx} {opsIn : ∀ op ∈ ops, op.InBounds ctx.raw} :
    interpretOpList ops state opsIn = interpretOpList ops' state (h ▸ opsIn) := by
  subst h; rfl

theorem interpretTerminatedOpList_congr {ops ops' : List OperationPtr} (h : ops = ops')
    {state : InterpreterState ctx} {opsIn : ∀ op ∈ ops, op.InBounds ctx.raw} :
    interpretTerminatedOpList ops state opsIn =
      interpretTerminatedOpList ops' state (h ▸ opsIn) := by
  subst h; rfl

/-- An operation without results leaves the variables as they are. -/
theorem VariableState.setResultValues?_empty {variables : VariableState ctx} {op : OperationPtr}
    {opIn : op.InBounds ctx.raw} (hNum : op.getNumResults! ctx.raw = 0) :
    variables.setResultValues? op #[] opIn = some variables := by
  have hConforms : RuntimeValue.ArrayConforms #[] (op.getResultTypes! ctx.raw) := by
    refine ⟨?_, by simp⟩
    rw [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNum]; rfl
  obtain ⟨variables', hSet⟩ :=
    (VariableState.setResultValues?_isSome_iff_conforms variables opIn).mp hConforms
  rw [hSet]
  congr 1
  ext value
  rw [VariableState.getVar?_setResultValues? hSet]
  rcases value with ⟨op', index⟩ | arg <;> simp [hNum]

/--
  `interpretOp` is monotone for an operation that a value mapping preserves.
  Unlike `interpretOp_monotone` this does not ask the target to verify: the
  results of the target conform to their types because those of the source do.
-/
theorem interpretOp_monotone_of_preservesOperation
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    {mapping : ValueMapping ctx ctx'} {op op' : OperationPtr}
    (opIn : op.InBounds ctx.raw) (opIn' : op'.InBounds ctx'.raw)
    [InterpretOp'Monotone (op.getOpType! ctx.raw)]
    (hState : state.isRefinedBy state' mapping)
    (hPreserves : mapping.PreservesOperation op op') :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState ctx' × Option ControlFlowAction) =>
        r₁.1.isRefinedBy r₂.1 mapping ∧
          ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (interpretOp op state opIn)
      (interpretOp op' state' opIn') := by
  rcases hsrc : interpretOp op state opIn with _ | _ | ⟨state₂, act⟩
  · simp [Interp.isRefinedBy]
  · simp [Interp.isRefinedBy]
  have ⟨operands, hSrcOps⟩ : ∃ operands, state.variables.getOperandValues op = some operands := by
    grind [interpretOp]
  obtain ⟨operands', hTgtOps, hOpsRef⟩ :=
    VariableState.getOperandValues_isRefinedBy hState.2 opIn hPreserves.operands hSrcOps
  have hMem : state.memory = state'.memory := hState.1
  have hPR1 := interpretOp'_monotone (op.getOpType! ctx.raw)
    (op.getProperties! ctx.raw (op.getOpType! ctx.raw)) (op.getResultTypes! ctx.raw)
    operands operands' (op.getSuccessors! ctx.raw) state.memory hOpsRef
  have hInterp'Eq : op'.interpret ctx'.raw operands' state'.memory =
                    op.interpret ctx.raw operands' state.memory := by
     grind [interpretOp'_opType_cast, cases ValueMapping.PreservesOperation]
  simp only [Interp.isRefinedBy_ok_target_iff, Prod.exists]
  have ⟨resValues, hinterp', hResValues⟩ :=
    (interpretOp_ok_iff_of_getOperandValues_eq_some hSrcOps).mp hsrc
  simp only [hinterp', Interp.isRefinedBy_ok_target_iff, OperationResult.isRefinedBy,
    Prod.exists] at hPR1
  have ⟨resValues', memory'₂, act', hinterp'Tgt, resValuesRef, memoryEq, actRef⟩ :=
    hPR1
  subst memory'₂
  simp only [← hInterp'Eq] at hinterp'Tgt
  simp only [interpretOp, hTgtOps, bind, hinterp'Tgt, liftM, monadLift, MonadLift.monadLift]
  have hConforms : RuntimeValue.ArrayConforms resValues' (op'.getResultTypes! ctx'.raw) := by
    rw [hPreserves.resultTypes]
    exact (RuntimeValue.ArrayConforms_of_setResultValues?_eq_some hResValues).of_isRefinedBy
      resValuesRef
  have ⟨v, hv⟩ :=
    (VariableState.setResultValues?_isSome_iff_conforms state'.variables opIn').mp hConforms
  simp only [hv, Interp.pure_eq, Interp.withBlame_ok, Interp.ok.injEq, Prod.mk.injEq]
  have stateVarRef := hState.2
  grind [InterpreterState.isRefinedBy,
    VariableState.setResultValues?_isRefinedBy stateVarRef resValuesRef,
    cases ValueMapping.PreservesOperation]

/-! ## The map between the values of the two modules -/

/--
  Every operation of `ctx` is monotone in its operands. This is what the proof
  needs of the operations that the lowering leaves alone.
-/
@[expose]
def MonotoneOps (ctx : WfIRContext OpCode) : Prop :=
  ∀ op : OperationPtr, op.InBounds ctx.raw → InterpretOp'Monotone (op.getOpType! ctx.raw)

namespace BranchLowering

variable (L : BranchLowering ctx ctx')

/-- The value of `ctx'` that stands for a value of `ctx`. -/
abbrev mapValue (value : ValuePtr) : ValuePtr :=
  lowerValue L.converted L.argCast value

theorem argCast_numResults {arg : BlockArgumentPtr} (argIn : arg.InBounds ctx.raw)
    (hConverted : L.converted arg.block) : (L.argCast arg).getNumResults! ctx'.raw = 1 := by
  have := (L.argCastSpec argIn hConverted).2.2.2.1
  rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, this]; rfl

/-- The source of a register in front of the new branch of a branch. -/
theorem regOperands_getElem? {op : OperationPtr} {i : Nat}
    (hi : i < (regOperands ctx.raw op (L.compare op)).length) :
    ∃ source, (regOperands ctx.raw op (L.compare op))[i]? = some source :=
  ⟨_, List.getElem?_eq_getElem hi⟩

include L in
theorem numResults {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : ¬ op.IsGmirBranch ctx.raw) :
    op.getNumResults! ctx'.raw = op.getNumResults! ctx.raw := by
  have := (L.opSpec opIn hBranch).2.2.2.1
  rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, this, OperationPtr.getResultTypes!.size_eq_getNumResults!]

theorem mapValue_inBounds {value : ValuePtr} (valueIn : value.InBounds ctx.raw) :
    (L.mapValue value).InBounds ctx'.raw := by
  rcases value with result | arg
  · simp only [mapValue, lowerValue, ValuePtr.inBounds_opResult] at valueIn ⊢
    obtain ⟨opIn, hIndex⟩ := OpResultPtr.inBounds_def.mp valueIn
    have hBranch : ¬ result.op.IsGmirBranch ctx.raw := fun h => by
      have := L.branchNumResults opIn h
      grind
    have opIn' := (L.opSpec opIn hBranch).1
    have := L.numResults opIn hBranch
    exact OpResultPtr.inBounds_def.mpr ⟨opIn', by grind⟩
  · simp only [ValuePtr.inBounds_blockArg] at valueIn
    obtain ⟨blockIn, hIndex⟩ := BlockArgumentPtr.inBounds_def.mp valueIn
    simp only [mapValue, lowerValue]
    split
    next hConverted =>
      have hSpec := L.argCastSpec valueIn hConverted
      have := L.argCast_numResults valueIn hConverted
      simp only [ValuePtr.inBounds_opResult, OperationPtr.getResult_def]
      exact OpResultPtr.inBounds_def.mpr ⟨hSpec.1, by grind⟩
    next =>
      simp only [ValuePtr.inBounds_blockArg]
      have := L.numArguments blockIn
      exact BlockArgumentPtr.inBounds_def.mpr ⟨L.blockIn blockIn, by grind⟩

/-- The map between the values of the two modules. -/
@[expose]
def mapping : ValueMapping ctx ctx' :=
  fun ⟨value, valueIn⟩ => ⟨L.mapValue value, L.mapValue_inBounds valueIn⟩

@[simp] theorem mapping_val {value : ValuePtr} {valueIn : value.InBounds ctx.raw} :
    (L.mapping ⟨value, valueIn⟩).val = L.mapValue value := rfl

theorem applyToArray_mapping {values : Array ValuePtr}
    (valuesIn : ∀ v ∈ values, v.InBounds ctx.raw) :
    L.mapping.applyToArray values valuesIn = values.map L.mapValue := by
  simp [ValueMapping.applyToArray]

/-- Only a result stands for itself as a result of an operation of the source. -/
theorem eq_of_mapValue_eq_getResult {value : ValuePtr} {op : OperationPtr} {i : Nat}
    (valueIn : value.InBounds ctx.raw) (opIn : op.InBounds ctx.raw)
    (hBranch : ¬ op.IsGmirBranch ctx.raw)
    (h : L.mapValue value = op.getResult i) : value = op.getResult i := by
  rcases value with result | arg
  · simpa [mapValue, lowerValue] using h
  · simp only [mapValue, lowerValue] at h
    split at h
    next hConverted =>
      have argIn : arg.InBounds ctx.raw := by simpa using valueIn
      simp only [OperationPtr.getResult_def, ValuePtr.opResult.injEq, OpResultPtr.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      /- The cast has a result in the lowering, so it has one in the source, which is not fresh. -/
      have hNum := L.argCast_numResults argIn hConverted
      rw [L.numResults opIn hBranch] at hNum
      exact absurd rfl ((L.argCastSpec argIn hConverted).2.1 ⟨L.argCast arg, 0⟩
        (OpResultPtr.inBounds_def.mpr ⟨opIn, by grind⟩))
    next => simp at h

/-- Only the argument of a converted block stands for its cast. -/
theorem eq_of_mapValue_eq_argCast {value : ValuePtr} {arg : BlockArgumentPtr}
    (valueIn : value.InBounds ctx.raw) (argIn : arg.InBounds ctx.raw)
    (hConverted : L.converted arg.block)
    (h : L.mapValue value = (L.argCast arg).getResult 0) : value = .blockArgument arg := by
  rcases value with result | arg'
  · simp only [mapValue, lowerValue, OperationPtr.getResult_def, ValuePtr.opResult.injEq] at h
    have := (L.argCastSpec argIn hConverted).2.1
    obtain ⟨opIn, _⟩ := OpResultPtr.inBounds_def.mp (by simpa using valueIn)
    grind
  · simp only [mapValue, lowerValue] at h
    split at h
    next hConverted' =>
      simp only [OperationPtr.getResult_def, ValuePtr.opResult.injEq, OpResultPtr.mk.injEq,
        and_true] at h
      rw [L.argCastInj (by simpa using valueIn) argIn hConverted' hConverted h]
    next => simp [OperationPtr.getResult_def] at h

/-- No value stands for an operation in front of the new branch of a branch. -/
theorem mapValue_ne_regOp {value : ValuePtr} {op : OperationPtr} {i : Nat}
    (valueIn : value.InBounds ctx.raw) (opIn : op.InBounds ctx.raw)
    (hBranch : op.IsGmirBranch ctx.raw) (hi : i < (regOperands ctx.raw op (L.compare op)).length) :
    L.mapValue value ≠ (L.regOp op i).getResult 0 := by
  intro h
  have hSpec := L.regOpSpec opIn hBranch hi
  rcases value with result | arg
  · simp only [mapValue, lowerValue, OperationPtr.getResult_def, ValuePtr.opResult.injEq] at h
    obtain ⟨opIn', _⟩ := OpResultPtr.inBounds_def.mp (by simpa using valueIn)
    grind
  · simp only [mapValue, lowerValue] at h
    split at h
    next hConverted =>
      simp only [OperationPtr.getResult_def, ValuePtr.opResult.injEq, OpResultPtr.mk.injEq,
        and_true] at h
      exact hSpec.2.2 arg (by simpa using valueIn) hConverted h
    next => simp [OperationPtr.getResult_def] at h

/-- An operation other than the two branches is the same operation in the lowering. -/
theorem preservesOperation {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : ¬ op.IsGmirBranch ctx.raw) :
    L.mapping.PreservesOperation op op opIn (L.opSpec opIn hBranch).1 := by
  have hSpec := L.opSpec opIn hBranch
  have hSucc := L.opSuccessors opIn hBranch
  have hNum := L.numResults opIn hBranch
  refine ⟨hSpec.2.1, ?_, hSpec.2.2.2.1, by rw [hSucc.1, hSucc.2], ?_, ?_, ?_⟩
  · rw [hSpec.2.2.1]
    exact OperationPtr.getProperties!_cast hSpec.2.1
  · rw [L.applyToArray_mapping]; exact hSpec.2.2.2.2.1
  · rw [L.applyToArray_mapping]
    simp [OperationPtr.getResults!, hNum, mapValue, lowerValue, OperationPtr.getResult_def]
  · intro value valueIn i h
    exact L.eq_of_mapValue_eq_getResult valueIn opIn hBranch h

/-! ## The casts at the start of a converted block -/

/--
  The states while the casts at the start of `block` run: the arguments hold
  registers, and every value of the source has its counterpart, except for
  the arguments whose cast is still `pending`.
-/
structure EntryInv (block : BlockPtr) (source : InterpreterState ctx)
    (target : InterpreterState ctx') (pending : List Nat) : Prop where
  memory : source.memory = target.memory
  arguments : ∀ i, i < block.getNumArguments! ctx.raw → ∃ sourceValue value reg,
    source.variables.getVar? (block.getArgument i) = some sourceValue ∧
    sourceValue ⊒ value ∧ value.toReg? = some reg ∧
    target.variables.getVar? (block.getArgument i) = some (.reg reg)
  values : ∀ value, value.InBounds ctx.raw → ∀ sourceValue,
    source.variables.getVar? value = some sourceValue →
    (∃ i ∈ pending, value = block.getArgument i) ∨
    ∃ targetValue, target.variables.getVar? (L.mapValue value) = some targetValue ∧
      sourceValue ⊒ targetValue

theorem entryCasts_inBounds {block : BlockPtr} (blockIn : block.InBounds ctx.raw)
    (hConverted : L.converted block) {pending : List Nat}
    (hPending : ∀ i ∈ pending, i < block.getNumArguments! ctx.raw) :
    ∀ op ∈ pending.map (fun i => L.argCast (block.getArgument i)), op.InBounds ctx'.raw := by
  intro op hOp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hOp
  refine (L.argCastSpec (arg := block.getArgument i) ?_ hConverted).1
  exact BlockArgumentPtr.inBounds_def.mpr ⟨blockIn, by grind [BlockPtr.getArgument_def]⟩

/-- Running the pending casts gives every value of the source its counterpart. -/
theorem interpretOpList_entryCasts {block : BlockPtr} (blockIn : block.InBounds ctx.raw)
    (hConverted : L.converted block) {source : InterpreterState ctx} {pending : List Nat}
    (hPending : ∀ i ∈ pending, i < block.getNumArguments! ctx.raw)
    {target : InterpreterState ctx'} (hInv : L.EntryInv block source target pending) :
    ∃ target', interpretOpList (pending.map (fun i => L.argCast (block.getArgument i))) target
        (L.entryCasts_inBounds blockIn hConverted hPending) = .ok (target', none) ∧
      L.EntryInv block source target' [] := by
  induction pending generalizing target with
  | nil => exact ⟨target, by simp [interpretOpList_nil], hInv⟩
  | cons i pending ih =>
    have hi : i < block.getNumArguments! ctx.raw := hPending i (by simp)
    have argIn : (block.getArgument i).InBounds ctx.raw :=
      BlockArgumentPtr.inBounds_def.mpr ⟨blockIn, by grind [BlockPtr.getArgument_def]⟩
    have hSpec := L.argCastSpec argIn hConverted
    obtain ⟨sourceValue, value, reg, hSource, hRefined, hReg, hTarget⟩ := hInv.arguments i hi
    have hFits := (L.argTypeConverted blockIn hConverted hi).2
    have hConforms := VariableState.getVar?_conforms hSource
    obtain ⟨result, hResult, hRefinedResult, hConformsResult⟩ :=
      RuntimeValue.isRefinedBy_ofReg?_of_toReg? hFits (hConforms.of_isRefinedBy hRefined) hReg
    have hRefinedResult := RuntimeValue.isRefinedBy_trans hRefined hRefinedResult
    obtain ⟨target', hOk, hMem, hGet⟩ := interpretOp_cast (state := target) hSpec.1 hSpec.2.2.1
      hSpec.2.2.2.1 hSpec.2.2.2.2 hTarget (interpretOp'_cast_ofReg hResult) hConformsResult
    have hInv' : L.EntryInv block source target' pending := by
      refine ⟨hInv.memory.trans hMem.symm, fun j hj => ?_, fun v vIn sv hv => ?_⟩
      · obtain ⟨sv, tv, r, h₁, h₂, h₃, h₄⟩ := hInv.arguments j hj
        exact ⟨sv, tv, r, h₁, h₂, h₃, by rw [hGet]; simpa [OperationPtr.getResult_def] using h₄⟩
      · have hMapArg : L.mapValue (block.getArgument i) =
            (L.argCast (block.getArgument i)).getResult 0 := by
          simp [mapValue, lowerValue, BlockPtr.getArgument_def, hConverted]
        rcases hInv.values v vIn sv hv with ⟨j, hj, rfl⟩ | ⟨tv, hTv, hRef⟩
        · rcases List.mem_cons.mp hj with rfl | hj
          · refine .inr ⟨result, by rw [hGet, hMapArg]; simp, ?_⟩
            obtain rfl : sv = sourceValue := by simpa [hSource] using hv.symm
            exact hRefinedResult
          · exact .inl ⟨j, hj, rfl⟩
        · by_cases hEq : L.mapValue v = (L.argCast (block.getArgument i)).getResult 0
          · have := L.eq_of_mapValue_eq_argCast vIn argIn hConverted hEq
            subst this
            obtain rfl : sv = sourceValue := by simpa [hSource] using hv.symm
            exact .inr ⟨result, by rw [hGet, hEq]; simp, hRefinedResult⟩
          · exact .inr ⟨tv, by rw [hGet]; simpa [hEq] using hTv, hRef⟩
    obtain ⟨target'', hOk', hInv''⟩ := ih (fun j hj => hPending j (by simp [hj])) hInv'
    refine ⟨target'', ?_, hInv''⟩
    simp only [List.map_cons, interpretOpList_cons, hOk]
    exact hOk'

/--
  Entering a converted block: the target sets its arguments to the registers
  it was passed, and after the casts the states are related again.
-/
theorem setArgumentValues?_converted {block : BlockPtr} (blockIn : block.InBounds ctx.raw)
    (hConverted : L.converted block) {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} (hState : state.isRefinedBy state' L.mapping)
    {values values' : Array RuntimeValue} (hValues : RegistersOf values values')
    {variables : VariableState ctx}
    (hSet : state.variables.setArgumentValues? block values blockIn = some variables) :
    ∃ variables' target,
      state'.variables.setArgumentValues? block values' (L.blockIn blockIn) = some variables' ∧
      interpretOpList ((List.range (block.getNumArguments! ctx.raw)).map
          (fun i => L.argCast (block.getArgument i))) ⟨variables', state'.memory⟩
        (L.entryCasts_inBounds blockIn hConverted (by simp)) = .ok (target, none) ∧
      InterpreterState.isRefinedBy ⟨variables, state.memory⟩ target L.mapping := by
  have hNum := L.numArguments blockIn
  have hSizeEq : values.size = block.getNumArguments! ctx.raw := by
    grind [VariableState.setArgumentValues?]
  have hSize : ∀ i, i < block.getNumArguments! ctx.raw → i < values.size := by
    intro i hi; omega
  /- The target is passed registers, which is what its arguments are. -/
  obtain ⟨variables', hSet'⟩ := (VariableState.setArgumentValues?_isSome_iff_conforms
      state'.variables (blockInBounds := L.blockIn blockIn) (values := values')
      (by rw [hNum, ← hValues.size_eq, hSizeEq])).mp (by
    intro j hj
    rw [hNum] at hj
    obtain ⟨_, reg, _, _, hReg⟩ := hValues.2 j (hSize j hj)
    rw [(L.argTypeConverted blockIn hConverted hj).1, hReg]
    exact RuntimeValue.reg_conforms)
  have hInv : L.EntryInv block ⟨variables, state.memory⟩ ⟨variables', state'.memory⟩
      (List.range (block.getNumArguments! ctx.raw)) := by
    refine ⟨hState.1, fun i hi => ?_, fun v vIn sv hv => ?_⟩
    · obtain ⟨value, reg, hRefined, hReg, hTarget⟩ := hValues.2 i (hSize i hi)
      refine ⟨values[i]!, value, reg, ?_, hRefined, hReg, ?_⟩
      · exact VariableState.getVar?_getArgument_of_setArgumentValues? hi hSet
      · rw [← hTarget]
        exact VariableState.getVar?_getArgument_of_setArgumentValues? (by rw [hNum]; exact hi) hSet'
    · by_cases hMem : v ∈ block.getArguments! ctx.raw
      · obtain ⟨i, hi, rfl⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp hMem
        exact .inl ⟨i, by simpa using hi, rfl⟩
      · rw [VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! hMem hSet] at hv
        obtain ⟨tv, hTv, hRef⟩ := hState.2 v vIn sv hv
        refine .inr ⟨tv, ?_, hRef⟩
        rw [VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! ?_ hSet']
        · exact hTv
        · intro hMem'
          obtain ⟨j, hj, hEq⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp hMem'
          rcases v with result | arg
          · simp [mapValue, lowerValue] at hEq
          · simp only [mapValue, lowerValue] at hEq
            split at hEq
            · simp [OperationPtr.getResult_def] at hEq
            · exact hMem (BlockPtr.getArguments!.mem_iff_exists_index.mpr
                ⟨j, by rw [← hNum]; exact hj, hEq⟩)
  obtain ⟨target, hOk, hInv'⟩ := L.interpretOpList_entryCasts blockIn hConverted (by simp) hInv
  refine ⟨variables', target, hSet', hOk, hInv'.memory, fun v vIn sv hv => ?_⟩
  rcases hInv'.values v vIn sv hv with ⟨_, h, _⟩ | h
  · simp at h
  · exact h

/-- A value stands for an argument of a block only if it is that argument. -/
theorem eq_of_mapValue_eq_getArgument {value : ValuePtr} {block : BlockPtr} {i : Nat}
    (h : L.mapValue value = block.getArgument i) :
    value = block.getArgument i ∧ L.converted block = false := by
  rcases value with result | arg
  · simp [mapValue, lowerValue] at h
  · simp only [mapValue, lowerValue] at h
    split at h
    · simp [OperationPtr.getResult_def] at h
    · next hConverted =>
      refine ⟨h, ?_⟩
      simp only [ValuePtr.blockArgument.injEq] at h
      subst h
      simpa [BlockPtr.getArgument_def] using hConverted

/-- Entering a block whose arguments are unchanged keeps the states related. -/
theorem setArgumentValues?_other {block : BlockPtr} (blockIn : block.InBounds ctx.raw)
    (hConverted : L.converted block = false) {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} (hState : state.isRefinedBy state' L.mapping)
    {values values' : Array RuntimeValue} (hValues : values ⊒ values')
    {variables : VariableState ctx}
    (hSet : state.variables.setArgumentValues? block values blockIn = some variables) :
    ∃ variables',
      state'.variables.setArgumentValues? block values' (L.blockIn blockIn) = some variables' ∧
      InterpreterState.isRefinedBy ⟨variables, state.memory⟩ ⟨variables', state'.memory⟩
        L.mapping := by
  have hNum := L.numArguments blockIn
  have hSizeEq : values.size = block.getNumArguments! ctx.raw := by
    grind [VariableState.setArgumentValues?]
  have hSourceConforms := (VariableState.setArgumentValues?_isSome_iff_conforms
    state.variables (blockInBounds := blockIn) hSizeEq).mpr ⟨variables, hSet⟩
  have hRefined : ∀ i : Nat, values[i]! ⊒ values'[i]! := by
    intro i
    by_cases hi : i < values.size
    · exact hValues.2 i hi
    · rw [getElem!_neg values i hi, getElem!_neg values' i (by rw [← hValues.1]; exact hi)]
      exact RuntimeValue.isRefinedBy_refl _
  obtain ⟨variables', hSet'⟩ := (VariableState.setArgumentValues?_isSome_iff_conforms
      state'.variables (blockInBounds := L.blockIn blockIn) (values := values')
      (by rw [hNum, ← hValues.1, hSizeEq])).mp (by
    intro j hj
    rw [hNum] at hj
    rw [L.argTypeOther blockIn hConverted hj]
    exact (hSourceConforms j hj).of_isRefinedBy (hRefined j))
  refine ⟨variables', hSet', hState.1, fun v vIn sv hv => ?_⟩
  simp only [mapping_val]
  by_cases hMem : v ∈ block.getArguments! ctx.raw
  · obtain ⟨i, hi, rfl⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp hMem
    have hMap : L.mapValue (block.getArgument i) = block.getArgument i := by
      simp [mapValue, lowerValue, BlockPtr.getArgument_def, hConverted]
    rw [VariableState.getVar?_getArgument_of_setArgumentValues? hi hSet] at hv
    rw [hMap, VariableState.getVar?_getArgument_of_setArgumentValues? (by rw [hNum]; exact hi) hSet']
    exact ⟨_, rfl, by simpa using (Option.some.inj hv) ▸ hRefined i⟩
  · rw [VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! hMem hSet] at hv
    obtain ⟨tv, hTv, hRef⟩ := hState.2 v vIn sv hv
    refine ⟨tv, ?_, hRef⟩
    rw [VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! ?_ hSet']
    · exact hTv
    · intro hMem'
      obtain ⟨j, hj, hEq⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp hMem'
      have := (L.eq_of_mapValue_eq_getArgument hEq.symm).1
      exact hMem (BlockPtr.getArguments!.mem_iff_exists_index.mpr
        ⟨j, by rw [← hNum]; exact hj, this.symm⟩)

end BranchLowering

/-! ## Constants -/

/-- Every `g_constant` of `ctx` holds its value in `state`, once it has run. -/
@[expose]
def ConstantsHold (state : InterpreterState ctx) : Prop :=
  ∀ constant : OperationPtr, constant.InBounds ctx.raw →
    constant.getOpType! ctx.raw = .gmir .g_constant →
    ∀ (value : RuntimeValue) (type : TypeAttr) (t : IntegerType),
      state.variables.getVar? (constant.getResult 0) = some value →
      (constant.getResultTypes! ctx.raw)[0]? = some type → type.val = .integerType t →
      value = .int t.bitwidth (.val (BitVec.ofInt t.bitwidth
        (constant.getProperties! ctx.raw (OpCode.gmir .g_constant)).value.value))

/-- No `g_constant` has run in a function that has just been entered. -/
theorem ConstantsHold.empty {memory : MemoryState} :
    ConstantsHold (⟨VariableState.empty ctx, memory⟩ : InterpreterState ctx) := by
  intro _ _ _ _ _ _ h
  simp [VariableState.empty, VariableState.getVar?] at h

/-- Entering a block sets its arguments, which are no results of a `g_constant`. -/
theorem ConstantsHold.setArgumentValues? {state : InterpreterState ctx} {block : BlockPtr}
    {values : Array RuntimeValue} {blockIn : block.InBounds ctx.raw} {variables : VariableState ctx}
    (hSet : state.variables.setArgumentValues? block values blockIn = some variables)
    (h : ConstantsHold state) : ConstantsHold (⟨variables, state.memory⟩ : InterpreterState ctx) := by
  intro constant constantIn hType value type t hValue
  rw [VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! (by
    simp [BlockPtr.getArguments!.mem_iff_exists_index, OperationPtr.getResult_def]) hSet] at hValue
  exact h constant constantIn hType value type t hValue

/-- Running an operation keeps every `g_constant` holding its value. -/
theorem ConstantsHold.interpretOp {op : OperationPtr} {opIn : op.InBounds ctx.raw}
    {state state' : InterpreterState ctx} {action : Option ControlFlowAction}
    (hRun : interpretOp op state opIn = .ok (state', action)) (h : ConstantsHold state) :
    ConstantsHold state' := by
  obtain ⟨operands, results, mem, variables, -, hInterp, hSet, rfl⟩ := interpretOp_some_iff.mp hRun
  intro constant constantIn hType value type t hValue hResultType hVal
  by_cases hEq : constant = op
  · subst hEq
    simp only [OperationPtr.interpret] at hInterp
    rw [interpretOp'_opType_cast hType (OperationPtr.getProperties!_cast hType)] at hInterp
    obtain ⟨type', t', hType', hVal', rfl, -, -⟩ := interpretOp'_gmir_g_constant_eq_ok hInterp
    rw [hResultType] at hType'
    obtain rfl := Option.some.inj hType'
    obtain rfl : t = t' := Attribute.integerType.inj (hVal.symm.trans hVal')
    rw [VariableState.getVar?_setResultValues? hSet] at hValue
    have hNum : 0 < constant.getNumResults! ctx.raw := by
      rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!]
      exact (Array.getElem?_eq_some_iff.mp hResultType).1
    simp [OperationPtr.getResult_def, hNum] at hValue
    exact hValue.symm
  · rw [VariableState.getVar?_setResultValues?_of_notMem_getResults! (by
      intro hMem
      obtain ⟨i, _, hi⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp hMem
      grind [OperationPtr.getResult_def]) hSet] at hValue
    exact h constant constantIn hType value type t hValue hResultType hVal

namespace BranchLowering

variable (L : BranchLowering ctx ctx')

/-! ## The compares -/

/--
  The `g_icmp` of the compare-and-branch that replaces `op` has just run: its
  result is what it computes from the values its operands hold.
-/
@[expose]
def CompareFact (op : OperationPtr) (state : InterpreterState ctx) : Prop :=
  ∃ a b cond, state.variables.getVar? ((L.icmpOf op).getOperand! ctx.raw 0) = some a ∧
    state.variables.getVar? ((L.icmpOf op).getOperand! ctx.raw 1) = some b ∧
    state.variables.getVar? ((L.icmpOf op).getResult 0) = some cond ∧
    ∃ successors mem mem' action,
      interpretOp' (.gmir .g_icmp) ((L.icmpOf op).getProperties! ctx.raw (OpCode.gmir .g_icmp))
        ((L.icmpOf op).getResultTypes! ctx.raw) #[a, b] successors mem =
        .ok (#[cond], mem', action)

/-- Running the `g_icmp` of a compare-and-branch establishes its `CompareFact`. -/
theorem compareFact_of_interpretOp {op : OperationPtr} {c : Compare} (opIn : op.InBounds ctx.raw)
    (hCompare : L.compare op = some c) {state state' : InterpreterState ctx}
    {action : Option ControlFlowAction} {icmpIn : (L.icmpOf op).InBounds ctx.raw}
    (hRun : interpretOp (L.icmpOf op) state icmpIn = .ok (state', action)) :
    L.CompareFact op state' := by
  obtain ⟨-, -, hType, hNum, -, hNumOps, hLhs, hRhs, -⟩ := L.compareSpec opIn hCompare
  obtain ⟨operands, results, mem, variables, hOperands, hInterp, hSet, rfl⟩ :=
    interpretOp_some_iff.mp hRun
  obtain ⟨hSize, hVals⟩ := VariableState.getOperandValues_eq_some_iff.mp hOperands
  simp only [OperationPtr.interpret] at hInterp
  rw [interpretOp'_opType_cast hType (OperationPtr.getProperties!_cast hType)] at hInterp
  obtain ⟨bw, x, y, w, cond, rfl, rfl, -, -, -⟩ := interpretOp'_gmir_g_icmp_eq_ok hInterp
  have hGet : ∀ value : ValuePtr, value ≠ (L.icmpOf op).getResult 0 →
      variables.getVar? value = state.variables.getVar? value := by
    intro value hNe
    apply VariableState.getVar?_setResultValues?_of_notMem_getResults! _ hSet
    intro hMem
    obtain ⟨i, hi, hEq⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp hMem
    obtain rfl : i = 0 := by omega
    exact hNe hEq.symm
  refine ⟨.int bw x, .int bw y, .int w cond, ?_, ?_, ?_, _, _, _, _, hInterp⟩
  · rw [hGet _ hLhs, hVals 0 (by omega)]; rfl
  · rw [hGet _ hRhs, hVals 1 (by omega)]; rfl
  · rw [VariableState.getVar?_setResultValues? hSet]
    simp [OperationPtr.getResult_def, hNum]

/-! ## The two branches -/

theorem regOps_inBounds {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : op.IsGmirBranch ctx.raw) {k : Nat}
    (hk : k ≤ (regOperands ctx.raw op (L.compare op)).length) :
    ∀ o ∈ (List.range k).map (L.regOp op), o.InBounds ctx'.raw := by
  intro o hO
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hO
  exact (L.regOpSpec opIn hBranch (by simp at hi; omega)).1

/-- The value of the register that holds `source`, read in `target`: `x0` holds zero. -/
@[expose]
def regValue (target : InterpreterState ctx') : Option ValuePtr → BitVec 64
  | none => 0
  | some value =>
    match target.variables.getVar? (L.mapValue value) with
    | some tv =>
      match tv.toReg? with
      | some reg => reg.val
      | none => 0
    | none => 0

/--
  The register that holds `source`: `x0`, or the cast of the counterpart in
  `target` of the value of `source` in `state`.
-/
@[expose]
def RegFor (state : InterpreterState ctx) (target : InterpreterState ctx')
    (source : Option ValuePtr) (register : RuntimeValue) : Prop :=
  register = .reg ⟨L.regValue target source⟩ ∧
  ∀ value, source = some value → ∃ sv tv reg, state.variables.getVar? value = some sv ∧
    target.variables.getVar? (L.mapValue value) = some tv ∧ sv ⊒ tv ∧ tv.toReg? = some reg ∧
    register = .reg reg

/--
  The operations in front of the new branch bind the registers of its operands,
  and keep the states related since no value of the source stands for one of them.
-/
theorem interpretOpList_regOps {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : op.IsGmirBranch ctx.raw) {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} (hState : state.isRefinedBy state' L.mapping)
    (hSources : ∀ (i : Nat) (value : ValuePtr),
      (regOperands ctx.raw op (L.compare op))[i]? = some (some value) →
      value.InBounds ctx.raw ∧ ∃ sv, state.variables.getVar? value = some sv ∧
        ∀ tv, sv ⊒ tv → ∃ reg, tv.toReg? = some reg)
    {k : Nat} (hk : k ≤ (regOperands ctx.raw op (L.compare op)).length) :
    ∃ (target : InterpreterState ctx') (registers : Array RuntimeValue),
      interpretOpList ((List.range k).map (L.regOp op)) state'
        (L.regOps_inBounds opIn hBranch hk) = .ok (target, none) ∧
      state.isRefinedBy target L.mapping ∧ registers.size = k ∧
      (∀ value, value.InBounds ctx.raw →
        target.variables.getVar? (L.mapValue value) = state'.variables.getVar? (L.mapValue value)) ∧
      ∀ i, i < k → (∃ source, (regOperands ctx.raw op (L.compare op))[i]? = some source ∧
          L.RegFor state state' source registers[i]!) ∧
        target.variables.getVar? ((L.regOp op i).getResult 0) = some registers[i]! := by
  induction k with
  | zero => exact ⟨state', #[], by simp [interpretOpList_nil], hState, rfl, fun _ _ => rfl,
      by simp⟩
  | succ k ih =>
    obtain ⟨target, registers, hOk, hTarget, hSize, hSame, hRegisters⟩ := ih (by omega)
    have hk' : k < (regOperands ctx.raw op (L.compare op)).length := by omega
    have hSpec := L.regOpSpec opIn hBranch hk'
    obtain ⟨source, hSource⟩ := L.regOperands_getElem? hk'
    /- The operation at `k` binds `register`, related to its source as `RegFor` says. -/
    obtain ⟨register, target', hOk', hMem, hGet, hReg⟩ : ∃ register target',
        interpretOp (L.regOp op k) target hSpec.1 = .ok (target', none) ∧
        target'.memory = target.memory ∧
        (∀ value, target'.variables.getVar? value =
          if value = (L.regOp op k).getResult 0 then some register
          else target.variables.getVar? value) ∧
        L.RegFor state state' source register := by
      rcases source with _ | value
      · obtain ⟨hType, hResultTypes, hOperands⟩ := L.regOpX0 opIn hBranch hSource
        obtain ⟨target', hOk', hMem, hGet⟩ :=
          interpretOp_getRegister (state := target) hSpec.1 hType hResultTypes hOperands
        exact ⟨_, target', hOk', hMem, hGet, rfl, fun _ h => by simp at h⟩
      · obtain ⟨hType, hResultTypes, hOperands⟩ := L.regOpCast opIn hBranch hSource
        obtain ⟨valueIn, sv, hSv, hRegs⟩ := hSources k value hSource
        obtain ⟨tv, hTv, hRefined⟩ := hState.2 value valueIn sv hSv
        simp only [mapping_val] at hTv
        obtain ⟨reg, hReg⟩ := hRegs tv hRefined
        have hTv' : target.variables.getVar? (lowerValue L.converted L.argCast value) = some tv := by
          rw [show lowerValue L.converted L.argCast value = L.mapValue value from rfl,
            hSame value valueIn, hTv]
        obtain ⟨target', hOk', hMem, hGet⟩ := interpretOp_cast (state := target) hSpec.1 hType
          hResultTypes hOperands hTv'
          (fun properties successors => interpretOp'_cast_toReg hReg properties successors)
          RuntimeValue.reg_conforms
        refine ⟨_, target', hOk', hMem, hGet, ?_, fun value' h => ?_⟩
        · simp [regValue, hTv, hReg]
        · obtain rfl := Option.some.inj h
          exact ⟨sv, tv, reg, hSv, hTv, hRefined, hReg, rfl⟩
    refine ⟨target', registers.push register, ?_, ⟨hTarget.1.trans hMem.symm, ?_⟩,
      by simp [hSize], fun value valueIn => ?_, fun i hi => ?_⟩
    · simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        interpretOpList_append, hOk, interpretOpList_cons, hOk', interpretOpList_nil]
    · intro v vIn sv hv
      obtain ⟨tv, hTv, hRef⟩ := hTarget.2 v vIn sv hv
      refine ⟨tv, ?_, hRef⟩
      simp only [mapping_val] at hTv ⊢
      rw [hGet]
      simpa [L.mapValue_ne_regOp vIn opIn hBranch hk'] using hTv
    · rw [hGet]
      simp only [L.mapValue_ne_regOp valueIn opIn hBranch hk', ↓reduceIte]
      exact hSame value valueIn
    · by_cases hEq : i = k
      · subst hEq
        have hPush : (registers.push register)[i]! = register := by simp [← hSize]
        refine ⟨⟨source, hSource, by rw [hPush]; exact hReg⟩, ?_⟩
        rw [hGet, hPush]; simp
      · obtain ⟨h₁, h₂⟩ := hRegisters i (by omega)
        have hLt : i < registers.size := by omega
        have hPush : (registers.push register)[i]! = registers[i]! := by
          rw [getElem!_pos (registers.push register) i (by simp; omega),
            getElem!_pos registers i hLt, Array.getElem_push_lt hLt]
        refine ⟨by rw [hPush]; exact h₁, ?_⟩
        have hNe : ((L.regOp op i).getResult 0 : ValuePtr) ≠ (L.regOp op k).getResult 0 := by
          intro h
          simp only [OperationPtr.getResult_def, ValuePtr.opResult.injEq, OpResultPtr.mk.injEq,
            and_true] at h
          exact hEq (L.regOpInj opIn hBranch (by omega) hk' h)
        rw [hGet, hPush]
        simpa [hNe] using h₂

theorem lowerOp_inBounds {op : OperationPtr} (opIn : op.InBounds ctx.raw) :
    ∀ op' ∈ lowerOp ctx.raw L.compare L.regOp L.newBranch op, op'.InBounds ctx'.raw := by
  intro op' hOp'
  simp only [lowerOp] at hOp'
  split at hOp'
  next hBranch =>
    rcases List.mem_append.mp hOp' with h | h
    · exact L.regOps_inBounds opIn hBranch (Nat.le_refl _) op' h
    · obtain rfl : op' = L.newBranch op := by simpa using h
      exact (L.newBranchSpec opIn hBranch).1
  next hBranch =>
    obtain rfl : op' = op := by simpa using hOp'
    exact (L.opSpec opIn hBranch).1

/-- How the outcome of a branch relates to the outcome of its lowering. -/
abbrev BranchRel (source : InterpreterState ctx × Option ControlFlowAction)
    (target : InterpreterState ctx' × Option ControlFlowAction) : Prop :=
  source.1.isRefinedBy target.1 L.mapping ∧
  ∃ values values' dest, source.2 = some (.branch values dest) ∧
    target.2 = some (.branch values' dest) ∧ L.converted dest ∧
    RegistersOf values values'

/-- The new branch reads the registers that the operations in front of it bound. -/
theorem getOperandValues_newBranch {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : op.IsGmirBranch ctx.raw) {target : InterpreterState ctx'}
    {registers : Array RuntimeValue}
    (hSize : registers.size = (regOperands ctx.raw op (L.compare op)).length)
    (hRegisters : ∀ i, i < (regOperands ctx.raw op (L.compare op)).length →
      target.variables.getVar? ((L.regOp op i).getResult 0) = some registers[i]!) :
    target.variables.getOperandValues (L.newBranch op) = some registers := by
  have hSpec := (L.newBranchSpec opIn hBranch).2.2.2
  have hNum : (L.newBranch op).getNumOperands! ctx'.raw =
      (regOperands ctx.raw op (L.compare op)).length := by
    rw [← OperationPtr.getOperands!.size_eq_getNumOperands!, hSpec]; simp
  refine VariableState.getOperandValues_eq_some_iff.mpr ⟨by rw [hNum, hSize], fun i hi => ?_⟩
  rw [hNum] at hi
  rw [← OperationPtr.getOperands!.getElem!_eq_getOperand!, hSpec]
  rw [getElem!_pos _ i (by simpa using hi)]
  simpa using hRegisters i hi

/-- An operand of an operation that has run holds the value the operation read. -/
theorem getVar?_getOperand {op : OperationPtr} {state : InterpreterState ctx}
    {operands : Array RuntimeValue} (hOperands : state.variables.getOperandValues op = some operands)
    {i : Nat} (hi : i < op.getNumOperands! ctx.raw) :
    state.variables.getVar? (op.getOperand! ctx.raw i) = some operands[i]! :=
  (VariableState.getOperandValues_eq_some_iff.mp hOperands).2 i hi

include L in
/--
  The registers of the operands of a branch from `start` on are those that hold
  them, from `offset` on.
-/
theorem registersOf_of_regFor {op : OperationPtr} {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} {operands registers : Array RuntimeValue} {start offset : Nat}
    (hOperands : state.variables.getOperandValues op = some operands)
    (hStart : start ≤ operands.size)
    (hSize : registers.size + start = operands.size + offset)
    (hRegisters : ∀ i, offset ≤ i → i < registers.size →
      L.RegFor state state' (some (op.getOperand! ctx.raw (i - offset + start))) registers[i]!) :
    RegistersOf (operands.extract start) (registers.extract offset) := by
  have hNum := (VariableState.getOperandValues_eq_some_iff.mp hOperands).1
  refine ⟨by simp; omega, fun i hi => ?_⟩
  simp only [Array.size_extract] at hi
  obtain ⟨sv, tv, reg, hSv, -, hRefined, hReg, hRegister⟩ :=
    (hRegisters (i + offset) (by omega) (by omega)).2 _ rfl
  rw [Nat.add_sub_cancel, getVar?_getOperand hOperands (by omega)] at hSv
  obtain rfl := Option.some.inj hSv
  refine ⟨tv, reg, ?_, hReg, ?_⟩
  · rw [getElem!_pos _ i (by simp; omega), Array.getElem_extract,
      ← getElem!_pos operands _ (by omega), Nat.add_comm]
    exact hRefined
  · rw [getElem!_pos _ i (by simp; omega), Array.getElem_extract, ← hRegister,
      getElem!_pos registers _ (by omega)]
    simp [Nat.add_comm]

/--
  A branch is refined by the operations that put its registers in front of the
  RISC-V branch. A compare-and-branch needs the `CompareFact` of its `g_icmp`,
  and the constant it may compare with to hold its value.
-/
theorem interpretOp_gmirBranch {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : op.IsGmirBranch ctx.raw) {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} (hState : state.isRefinedBy state' L.mapping)
    (hConstants : ConstantsHold state)
    (hFact : ∀ c, L.compare op = some c → L.CompareFact op state) :
    Interp.isRefinedBy L.BranchRel (interpretOp op state opIn)
      (interpretOpList (lowerOp ctx.raw L.compare L.regOp L.newBranch op) state'
        (L.lowerOp_inBounds opIn)) := by
  rcases hsrc : interpretOp op state opIn with _ | _ | ⟨source₁, action⟩
  · simp [Interp.isRefinedBy]
  · simp [Interp.isRefinedBy]
  obtain ⟨operands, results, mem₁, variables₁, hOperands, hInterp, hSetResults, rfl⟩ :=
    interpretOp_some_iff.mp hsrc
  have hNumOperands := (VariableState.getOperandValues_eq_some_iff.mp hOperands).1
  have operandIn : ∀ i, i < op.getNumOperands! ctx.raw →
      (op.getOperand! ctx.raw i).InBounds ctx.raw := fun i hi =>
    OperationPtr.getOperands!_inBounds ctx.wellFormed.inBounds opIn
      (OperationPtr.getOperands!.mem_getOperand hi)
  /- An operand of the branch fits a register, and so does every refinement of its value. -/
  have hOperandRegs : ∀ i, i < op.getNumOperands! ctx.raw → ∀ tv, operands[i]! ⊒ tv →
      ∃ reg, tv.toReg? = some reg := by
    intro i hi tv hRefined
    have hConforms :=
      (VariableState.getVar?_conforms (getVar?_getOperand hOperands hi)).of_isRefinedBy hRefined
    exact RuntimeValue.toReg?_eq_some_of_roundTrips (L.operandRoundTrips opIn hBranch hi) hConforms
  /- So do the values that a compare-and-branch compares, as the `g_icmp` compared integers. -/
  have hSources : ∀ (i : Nat) (value : ValuePtr),
      (regOperands ctx.raw op (L.compare op))[i]? = some (some value) →
      value.InBounds ctx.raw ∧ ∃ sv, state.variables.getVar? value = some sv ∧
        ∀ tv, sv ⊒ tv → ∃ reg, tv.toReg? = some reg := by
    intro i value hValue
    rcases hc : L.compare op with _ | ⟨branch, l, r⟩
    · rw [hc, regOperands_none] at hValue
      obtain ⟨hi, rfl⟩ : i < op.getNumOperands! ctx.raw ∧ op.getOperand! ctx.raw i = value := by
        grind [List.getElem?_range]
      exact ⟨operandIn i hi, _, getVar?_getOperand hOperands hi, hOperandRegs i hi⟩
    · obtain ⟨-, icmpIn, -, -, -, hIcmpNumOps, -, -, -, hCompareEq⟩ := L.compareSpec opIn hc
      obtain ⟨a, b, cond, hA, hB, _, _, _, _, _, hIcmp⟩ := hFact _ hc
      obtain ⟨bw, x, y, -, -, hOps, -⟩ := interpretOp'_gmir_g_icmp_eq_ok hIcmp
      obtain ⟨rfl, rfl⟩ : a = .int bw x ∧ b = .int bw y := by simpa using hOps
      have hInt : ∀ v : Data.LLVM.Int bw, ∀ tv, RuntimeValue.int bw v ⊒ tv →
          ∃ reg, tv.toReg? = some reg := by
        intro v tv hRefined
        obtain ⟨t, rfl, -⟩ := RuntimeValue.int_of_isRefinedBy hRefined
        exact ⟨_, RuntimeValue.toReg?_int⟩
      have icmpOperandIn : ∀ j, j < 2 → ((L.icmpOf op).getOperand! ctx.raw j).InBounds ctx.raw :=
        fun j hj => OperationPtr.getOperands!_inBounds ctx.wellFormed.inBounds icmpIn
          (OperationPtr.getOperands!.mem_getOperand (by omega))
      /- A compared value is one of the two operands of the `g_icmp`. -/
      have hCompared : some value = l ∨ some value = r →
          value.InBounds ctx.raw ∧ ∃ sv, state.variables.getVar? value = some sv ∧
            ∀ tv, sv ⊒ tv → ∃ reg, tv.toReg? = some reg := by
        intro hMem
        have := compareBranch_operands (value := some value) (by rw [hCompareEq]; exact hMem)
        rcases this with h | h | h
        · simp at h
        · obtain rfl := Option.some.inj h
          exact ⟨icmpOperandIn 0 (by omega), _, hA, hInt x⟩
        · obtain rfl := Option.some.inj h
          exact ⟨icmpOperandIn 1 (by omega), _, hB, hInt y⟩
      rw [hc, regOperands_some] at hValue
      rcases i with _ | _ | i
      · exact hCompared (.inl (by simpa using hValue.symm))
      · exact hCompared (.inr (by simpa using hValue.symm))
      · obtain ⟨hi, rfl⟩ : i + 1 < op.getNumOperands! ctx.raw ∧
            op.getOperand! ctx.raw (i + 1) = value := by
          simp only [List.getElem?_cons_succ] at hValue
          grind [List.getElem?_range]
        exact ⟨operandIn _ hi, _, getVar?_getOperand hOperands hi, hOperandRegs _ hi⟩
  obtain ⟨target, registers, hOk, hTarget, hSize, hSame, hRegisters⟩ :=
    L.interpretOpList_regOps opIn hBranch hState hSources (Nat.le_refl _)
  have hNewOperands := L.getOperandValues_newBranch opIn hBranch hSize
    (fun i hi => (hRegisters i hi).2)
  have hSpec := L.newBranchSpec opIn hBranch
  /- Both branches compute the same successor, from the operands and from their registers. -/
  have hData : ∃ values values' dest, results = #[] ∧ mem₁ = state.memory ∧
      action = some (.branch values dest) ∧
      (L.newBranch op).interpret ctx'.raw registers target.memory =
        .ok (#[], target.memory, some (.branch values' dest)) ∧
      RegistersOf values values' := by
    /- Without a compare, the registers are those of the operands. -/
    have hPlain : L.compare op = none → RegistersOf operands registers := by
      intro hc
      have hLen : (regOperands ctx.raw op (L.compare op)).length = operands.size := by
        rw [hc, regOperands_none]; simp [hNumOperands]
      have := L.registersOf_of_regFor (registers := registers) (state' := state')
        (start := 0) (offset := 0) hOperands (by omega)
        (by omega) (fun i _ hi => by
          obtain ⟨⟨source, hSource, hFor⟩, -⟩ := hRegisters i (by omega)
          rw [hc, regOperands_none] at hSource
          obtain rfl : source = some (op.getOperand! ctx.raw i) := by
            grind [List.getElem?_range]
          simpa using hFor)
      simpa using this
    rw [← hTarget.1]
    simp only [OperationPtr.interpret, hSpec.2.2.1] at hInterp ⊢
    rcases hBranch with hType | hType
    · obtain ⟨hc, hNewType⟩ := L.newBranchBr opIn hType
      rw [interpretOp'_opType_cast hType (OperationPtr.getProperties!_cast hType)] at hInterp
      rw [interpretOp'_opType_cast hNewType (OperationPtr.getProperties!_cast hNewType)]
      exact interpretOp'_br_registers hInterp (hPlain hc) _ _
    rw [interpretOp'_opType_cast hType (OperationPtr.getProperties!_cast hType)] at hInterp
    rcases hc : L.compare op with _ | ⟨branch, l, r⟩
    · obtain ⟨hNewType, hSizes⟩ := L.newBranchBnez opIn hType hc
      rw [interpretOp'_opType_cast hNewType (OperationPtr.getProperties!_cast hNewType)]
      refine interpretOp'_brcond_registers hInterp (fun w x h0 => ?_) (hPlain hc) _ _ hSizes
      have hLt : 0 < op.getNumOperands! ctx.raw := by
        have := (Array.getElem?_eq_some_iff.mp h0).1; omega
      have hValue := getVar?_getOperand hOperands hLt
      rw [getElem!_pos operands 0 (by omega), (Array.getElem?_eq_some_iff.mp h0).2] at hValue
      exact RuntimeValue.width_le_of_roundTrips (L.operandRoundTrips opIn (.inr hType) hLt)
        (VariableState.getVar?_conforms hValue)
    · obtain ⟨-, icmpIn, -, -, hCondOperand, hIcmpNumOps, -, -, hFills, hCompareEq⟩ :=
        L.compareSpec opIn hc
      obtain ⟨a, b, cond, hA, hB, hCond, _, _, _, _, hIcmp⟩ := hFact _ hc
      obtain ⟨hNewType, segments, hProps, hSegments⟩ := L.newBranchCompare opIn hc
      have icmpOperandIn : ∀ j, j < 2 → ((L.icmpOf op).getOperand! ctx.raw j).InBounds ctx.raw :=
        fun j hj => OperationPtr.getOperands!_inBounds ctx.wellFormed.inBounds icmpIn
          (OperationPtr.getOperands!.mem_getOperand (by omega))
      /- The compared values are integers of 64 bits, as the first fills a register. -/
      have hWidth : ∀ w x, a = .int w x → w = 64 := by
        intro w x rfl
        have hConf := VariableState.getVar?_conforms hA
        rcases fillsRegister_iff.mp hFills with ⟨t, ht, h64⟩ | ⟨t, ht⟩ <;> rw [ht] at hConf <;>
          simp at hConf
        omega
      /- The register of a compared value holds the value. -/
      have hValue : ∀ (v : ValuePtr) (x : BitVec 64), v.InBounds ctx.raw →
          state.variables.getVar? v = some (.int 64 (.val x)) → L.regValue state' (some v) = x := by
        intro v x vIn hv
        obtain ⟨tv, hTv, hRef⟩ := hState.2 v vIn _ hv
        simp only [mapping_val] at hTv
        rw [RuntimeValue.int_val_isRefinedBy_iff] at hRef
        subst hRef
        simp [regValue, hTv, val_toReg]
      /- A constant that the `g_icmp` compares with holds its value. -/
      have hConstant : ∀ k, L.constantOf op = some k → b = .int 64 (.val (BitVec.ofInt 64 k)) := by
        intro k hk
        obtain ⟨constant, type, ⟨n⟩, hRhs, constantIn, constantType, hResultType, hTypeVal, rfl⟩ :=
          L.constantSpec opIn hc hk
        have hHolds := hConstants constant constantIn constantType b type _ (hRhs ▸ hB) hResultType
          hTypeVal
        obtain ⟨bw, x, y, -, -, hOps, -⟩ := interpretOp'_gmir_g_icmp_eq_ok hIcmp
        obtain ⟨rfl, rfl⟩ : a = .int bw x ∧ b = .int bw y := by simpa using hOps
        obtain rfl := hWidth bw x rfl
        simp only [RuntimeValue.int.injEq] at hHolds
        obtain ⟨rfl, hy⟩ := hHolds
        obtain rfl := eq_of_heq hy
        rw [BitVec.ofInt_toInt]
      have h0 : 0 < operands.size := by
        obtain ⟨_, _, _, _, _, _, hC, _⟩ := interpretOp'_gmir_g_brcond_eq_ok_iff.mp hInterp
        exact (Array.getElem?_eq_some_iff.mp hC).1
      have hCond' : operands[0]? = some cond := by
        have := getVar?_getOperand hOperands (i := 0) (by omega)
        rw [hCondOperand, hCond] at this
        rw [Array.getElem?_eq_some_getElem! operands 0 h0, ← Option.some.inj this]
      have hLen : (regOperands ctx.raw op (L.compare op)).length = operands.size + 1 := by
        rw [hc, regOperands_some]; simp; omega
      have hReg : ∀ j source, j < 2 → (regOperands ctx.raw op (L.compare op))[j]? = some source →
          registers[j]? = some (.reg ⟨L.regValue state' source⟩) := by
        intro j source hj hSource
        obtain ⟨⟨source', hSource', hFor⟩, -⟩ := hRegisters j (by omega)
        rw [hSource] at hSource'
        obtain rfl := Option.some.inj hSource'
        rw [← hFor.1]
        exact Array.getElem?_eq_some_getElem! registers j (by omega)
      have hTail : RegistersOf (operands.extract 1) (registers.extract 2) :=
        L.registersOf_of_regFor (registers := registers) (state' := state') hOperands (by omega)
          (by omega) (fun i hi hi' => by
            obtain ⟨⟨source, hSource, hFor⟩, -⟩ := hRegisters i (by omega)
            rw [hc, regOperands_some] at hSource
            obtain rfl : source = some (op.getOperand! ctx.raw (i - 2 + 1)) := by
              obtain ⟨i, rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
              simp only [List.getElem?_cons_succ] at hSource
              grind [List.getElem?_range]
            exact hFor)
      have hResult := interpretOp'_brcond_compare_registers hInterp hIcmp hCond' hWidth
        hCompareEq (value := L.regValue state') rfl
        (fun x hx => hValue _ x (icmpOperandIn 0 (by omega)) (hx ▸ hA))
        (fun y hy => hValue _ y (icmpOperandIn 1 (by omega)) (hy ▸ hB)) hConstant
        (hReg 0 l (by omega) (by rw [hc, regOperands_some]; rfl))
        (hReg 1 r (by omega) (by rw [hc, regOperands_some]; rfl)) hTail hSegments
        ((L.newBranch op).getResultTypes! ctx'.raw)
      rw [interpretOp'_opType_cast hNewType (OperationPtr.getProperties!_cast hNewType), hProps]
      exact hResult
  obtain ⟨values, values', dest, rfl, rfl, rfl, hNewInterp, hValues⟩ := hData
  have hDest : dest ∈ op.getSuccessors! ctx.raw := interpretOp'_branch_dest_mem hInterp
  have hVariables : variables₁ = state.variables := by
    rw [VariableState.setResultValues?_empty (L.branchNumResults opIn hBranch)] at hSetResults
    exact (Option.some.inj hSetResults).symm
  subst hVariables
  have hNewOk : interpretOp (L.newBranch op) target hSpec.1 =
      .ok (target, some (.branch values' dest)) :=
    (interpretOp_ok_iff_of_getOperandValues_eq_some hNewOperands).mpr
      ⟨#[], hNewInterp, VariableState.setResultValues?_empty hSpec.2.1⟩
  have hList : interpretOpList (lowerOp ctx.raw L.compare L.regOp L.newBranch op) state'
      (L.lowerOp_inBounds opIn) = .ok (target, some (.branch values' dest)) := by
    simp only [lowerOp, hBranch, ↓reduceIte, interpretOpList_append, hOk, interpretOpList_cons,
      hNewOk]
  rw [hList]
  exact ⟨hTarget, values, values', dest, rfl, rfl,
    L.branchSuccessorConverted opIn hBranch hDest, hValues⟩

/-! ## Blocks -/

/-- How the control flow of the source relates to that of the lowering. -/
@[expose]
def ActionRel : Option ControlFlowAction → Option ControlFlowAction → Prop
  | none, none => True
  | some (.return values), some (.return values') => values ⊒ values'
  | some (.branch values dest), some (.branch values' dest') =>
    dest = dest' ∧ L.converted dest ∧ RegistersOf values values'
  | _, _ => False

theorem flatMap_lowerOp_inBounds {ops : List OperationPtr}
    (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw) :
    ∀ op' ∈ ops.flatMap (lowerOp ctx.raw L.compare L.regOp L.newBranch), op'.InBounds ctx'.raw := by
  intro op' hOp'
  obtain ⟨op, hOp, hMem⟩ := List.mem_flatMap.mp hOp'
  exact L.lowerOp_inBounds (opsIn op hOp) op' hMem

/--
  The `g_icmp` of every compare-and-branch in `ops` comes right before it, unless
  the compare-and-branch comes first.
-/
@[expose]
def ComparesAdjacent (ops : List OperationPtr) : Prop :=
  ∀ pre op post c, ops = pre ++ op :: post → pre ≠ [] → L.compare op = some c →
    pre.getLast? = some (L.icmpOf op)

/-- The first operation of `ops`, if a compare-and-branch, has its `CompareFact`. -/
@[expose]
def HeadFact (ops : List OperationPtr) (state : InterpreterState ctx) : Prop :=
  ∀ op post c, ops = op :: post → L.compare op = some c → L.CompareFact op state

/-- How the source state after a list of operations relates to the target state. -/
abbrev ListRel (source : InterpreterState ctx × Option ControlFlowAction)
    (target : InterpreterState ctx' × Option ControlFlowAction) : Prop :=
  source.1.isRefinedBy target.1 L.mapping ∧ L.ActionRel source.2 target.2 ∧
    ConstantsHold source.1

/-- A list of operations is refined by its lowering. -/
theorem interpretOpList_lowered (hMono : MonotoneOps ctx) {ops : List OperationPtr}
    (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw) {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} (hState : state.isRefinedBy state' L.mapping)
    (hConstants : ConstantsHold state) (hAdjacent : L.ComparesAdjacent ops)
    (hHead : L.HeadFact ops state) :
    Interp.isRefinedBy L.ListRel
      (interpretOpList ops state opsIn)
      (interpretOpList (ops.flatMap (lowerOp ctx.raw L.compare L.regOp L.newBranch)) state'
        (L.flatMap_lowerOp_inBounds opsIn)) := by
  induction ops generalizing state state' with
  | nil =>
    simp only [interpretOpList_nil, List.flatMap_nil, Interp.isRefinedBy]
    exact ⟨hState, trivial, hConstants⟩
  | cons op ops ih =>
    have opIn := opsIn op (by simp)
    simp only [List.flatMap_cons, interpretOpList_cons, interpretOpList_append]
    by_cases hBranch : op.IsGmirBranch ctx.raw
    · have hOp := L.interpretOp_gmirBranch opIn hBranch hState hConstants
        (fun c hc => hHead op ops c rfl hc)
      rcases hsrc : interpretOp op state opIn with _ | _ | ⟨source₁, action⟩
      · simp [Interp.isRefinedBy]
      · simp [Interp.isRefinedBy]
      · simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at hOp
        obtain ⟨⟨target₁, action'⟩, hTarget, hRel, values, values', dest, rfl, rfl, hDest, hValues⟩ :=
          hOp
        simp only [hTarget, Interp.isRefinedBy]
        exact ⟨hRel, ⟨rfl, hDest, hValues⟩, hConstants.interpretOp hsrc⟩
    · have := hMono op opIn
      have hOp := interpretOp_monotone_of_preservesOperation opIn (L.opSpec opIn hBranch).1
        hState (L.preservesOperation opIn hBranch)
      have hLower : lowerOp ctx.raw L.compare L.regOp L.newBranch op = [op] := by
        simp [lowerOp, hBranch]
      rcases hsrc : interpretOp op state opIn with _ | _ | ⟨source₁, action⟩
      · simp [Interp.isRefinedBy]
      · simp [Interp.isRefinedBy]
      · simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at hOp
        obtain ⟨⟨target₁, action'⟩, hTarget, hRel, hAction⟩ := hOp
        have hConstants₁ := hConstants.interpretOp hsrc
        rw [interpretOpList_congr hLower]
        simp only [interpretOpList_cons, interpretOpList_nil, hTarget]
        rcases action with _ | cf
        · obtain rfl : action' = none := by
            cases action' <;> simp_all [ControlFlowAction.optionIsRefinedBy]
          refine ih (fun op' hOp' => opsIn op' (by simp [hOp'])) hRel hConstants₁
            (fun pre op' post c hOps hPre hc => ?_) (fun op' post c hOps hc => ?_)
          · have := hAdjacent (op :: pre) op' post c (by simp [hOps]) (by simp) hc
            cases pre with
            | nil => contradiction
            | cons p pre => simpa [List.getLast?_cons_cons] using this
          · /- The operation that just ran is the `g_icmp` of the compare-and-branch after it. -/
            have hIcmp := hAdjacent [op] op' post c (by simp [hOps]) (by simp) hc
            obtain rfl : op = L.icmpOf op' := by simpa using hIcmp
            exact L.compareFact_of_interpretOp (opsIn op' (by simp [hOps])) hc hsrc
        · obtain ⟨cf', rfl, hCf⟩ : ∃ cf', action' = some cf' ∧
              cf.isRefinedBy cf' := by
            cases action' <;> simp_all [ControlFlowAction.optionIsRefinedBy]
          rcases cf with values | ⟨values, dest⟩
          · rcases cf' with values' | _
            · exact ⟨hRel, hCf, hConstants₁⟩
            · simp [ControlFlowAction.isRefinedBy] at hCf
          · have := interpretOp_branch_dest_mem_getSuccessors! hsrc
            simp [(L.opSuccessors opIn hBranch).1] at this

/-- A list of operations that ends in a terminator is refined by its lowering. -/
theorem interpretTerminatedOpList_lowered (hMono : MonotoneOps ctx) {ops : List OperationPtr}
    (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw) {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} (hState : state.isRefinedBy state' L.mapping)
    (hConstants : ConstantsHold state) (hAdjacent : L.ComparesAdjacent ops)
    (hHead : L.HeadFact ops state) :
    Interp.isRefinedBy
      (fun source target => source.1.isRefinedBy target.1 L.mapping ∧
        L.ActionRel (some source.2) (some target.2) ∧ ConstantsHold source.1)
      (interpretTerminatedOpList ops state opsIn)
      (interpretTerminatedOpList (ops.flatMap (lowerOp ctx.raw L.compare L.regOp L.newBranch)) state'
        (L.flatMap_lowerOp_inBounds opsIn)) := by
  have hList := L.interpretOpList_lowered hMono opsIn hState hConstants hAdjacent hHead
  simp only [interpretTerminatedOpList, bind]
  rcases hsrc : interpretOpList ops state opsIn with _ | _ | ⟨source₁, action⟩
  · simp [Interp.isRefinedBy]
  · simp [Interp.isRefinedBy]
  · simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at hList
    obtain ⟨⟨target₁, action'⟩, hTarget, hRel, hAction, hConstants₁⟩ := hList
    simp only [hTarget]
    rcases action with _ | cf
    · simp [Interp.isRefinedBy]
    · rcases action' with _ | cf'
      · simp [ActionRel] at hAction
      · exact ⟨hRel, hAction, hConstants₁⟩

/-- The calls of `interpretBlockCFG` in the two modules that correspond to each other. -/
@[expose]
def CallRel : BlockCallRel ctx ctx' :=
  fun block values state block' values' state' =>
    block' = block ∧ state.isRefinedBy state' L.mapping ∧ ConstantsHold state ∧
    if L.converted block then RegistersOf values values'
    else values ⊒ values'

/-- The results of the two modules that correspond to each other. -/
abbrev ResultRel (source : InterpreterState ctx × Array RuntimeValue)
    (target : InterpreterState ctx' × Array RuntimeValue) : Prop :=
  source.1.memory = target.1.memory ∧ source.2 ⊒ target.2

/-- A block is refined by its lowering, and the blocks they branch to correspond again. -/
theorem interpretBlock_lowered (hMono : MonotoneOps ctx) {block block' : BlockPtr}
    {values values' : Array RuntimeValue}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    (blockIn : block.InBounds ctx.raw) (blockIn' : block'.InBounds ctx'.raw)
    (hRel : L.CallRel block values state block' values' state') :
    Interp.isRefinedBy (L.CallRel.Step ResultRel)
      (interpretBlock block values state blockIn)
      (interpretBlock block' values' state' blockIn') := by
  obtain ⟨rfl, hState, hConstants, hValues⟩ := hRel
  rw [interpretBlock_eq blockIn, interpretBlock_eq blockIn']
  rcases hSet : state.variables.setArgumentValues? block' values blockIn with _ | variables
  · simp [Interp.isRefinedBy]
  simp only
  have opsIn : ∀ op ∈ (block'.operationList ctx.raw ctx.wellFormed blockIn).toList,
      op.InBounds ctx.raw := by
    grind [BlockPtr.operationListWF, BlockPtr.OpChain]
  /- In the block, the `g_icmp` of a compare-and-branch comes right before it, so not first. -/
  have hAdjacent : L.ComparesAdjacent (block'.operationList ctx.raw ctx.wellFormed blockIn).toList :=
    fun pre op post c hOps _ hc =>
      L.compareAdjacent blockIn (opsIn op (by simp [hOps])) hc hOps
  have hHead : L.HeadFact (block'.operationList ctx.raw ctx.wellFormed blockIn).toList
      ⟨variables, state.memory⟩ := fun op post c hOps hc => by
    have := L.compareAdjacent blockIn (opsIn op (by simp [hOps])) hc (pre := [])
      (by simpa using hOps)
    simp at this
  /- After the arguments are set, and the casts ran in a converted block, the states are related. -/
  have hBody : ∀ (target : InterpreterState ctx'),
      InterpreterState.isRefinedBy ⟨variables, state.memory⟩ target L.mapping →
      Interp.isRefinedBy (L.CallRel.Step ResultRel)
        (interpretTerminatedOpList (block'.operationList ctx.raw ctx.wellFormed blockIn).toList
          ⟨variables, state.memory⟩ (by grind [BlockPtr.operationListWF, BlockPtr.OpChain]))
        (interpretTerminatedOpList ((block'.operationList ctx.raw ctx.wellFormed blockIn).toList.flatMap
          (lowerOp ctx.raw L.compare L.regOp L.newBranch)) target
          (L.flatMap_lowerOp_inBounds (by grind [BlockPtr.operationListWF, BlockPtr.OpChain]))) := by
    intro target hTarget
    have hOps := L.interpretTerminatedOpList_lowered hMono
      (ops := (block'.operationList ctx.raw ctx.wellFormed blockIn).toList)
      opsIn hTarget (hConstants.setArgumentValues? hSet) hAdjacent hHead
    rcases hsrc : interpretTerminatedOpList _ _ _ with _ | _ | ⟨source₁, cf⟩
    · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]
    · simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at hOps
      obtain ⟨⟨target₁, cf'⟩, hTarget₁, hRel₁, hAction, hConstants₁⟩ := hOps
      simp only [hTarget₁, Interp.isRefinedBy, BlockCallRel.Step]
      rcases cf with res | ⟨res, dest⟩ <;> rcases cf' with res' | ⟨res', dest'⟩ <;>
        simp only [ActionRel] at hAction ⊢
      · exact ⟨hRel₁.1, hAction⟩
      · obtain ⟨rfl, hDest, hRegisters⟩ := hAction
        intro destIn
        exact ⟨L.blockIn destIn, rfl, hRel₁, hConstants₁, by simp [hDest, hRegisters]⟩
  by_cases hConverted : L.converted block'
  · simp only [hConverted, ↓reduceIte] at hValues
    obtain ⟨variables', target, hSet', hCasts, hTarget⟩ :=
      L.setArgumentValues?_converted blockIn hConverted hState hValues hSet
    simp only [hSet']
    rw [interpretTerminatedOpList_congr (L.operationList blockIn)]
    simp only [hConverted, ↓reduceIte, interpretTerminatedOpList_append, hCasts]
    exact hBody target hTarget
  · have hConverted' : L.converted block' = false := by simpa using hConverted
    simp only [hConverted', Bool.false_eq_true, ↓reduceIte] at hValues
    obtain ⟨variables', hSet', hTarget⟩ :=
      L.setArgumentValues?_other blockIn hConverted' hState hValues hSet
    simp only [hSet']
    rw [interpretTerminatedOpList_congr (L.operationList blockIn)]
    simp only [hConverted', Bool.false_eq_true, ↓reduceIte, List.nil_append]
    exact hBody _ hTarget

/-! ## Functions and modules -/

/-- A control-flow graph is refined by its lowering. -/
theorem interpretBlockCFG_lowered (hMono : MonotoneOps ctx) {block : BlockPtr}
    {values values' : Array RuntimeValue}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    (blockIn : block.InBounds ctx.raw)
    (hRel : L.CallRel block values state block values' state') :
    Interp.isRefinedBy ResultRel
      (interpretBlockCFG block values state blockIn)
      (interpretBlockCFG block values' state' (L.blockIn blockIn)) :=
  interpretBlockCFG_isRefinedBy
    (fun _ _ _ _ _ _ blockIn blockIn' hRel => L.interpretBlock_lowered hMono blockIn blockIn' hRel)
    blockIn (L.blockIn blockIn) hRel

/-- A function is refined by its lowering. -/
theorem isRefinedByAsFunction (hMono : MonotoneOps ctx) {func : OperationPtr}
    (funcIn : func.InBounds ctx.raw)
    (hBranch : ¬ func.IsGmirBranch ctx.raw) (hFunc : func.getOpType! ctx.raw = .func .func) :
    func.isRefinedByAsFunction ctx func ctx' funcIn (L.opSpec funcIn hBranch).1 := by
  have hSpec := L.opSpec funcIn hBranch
  have funcIn' := hSpec.1
  have hFunc' : func.getOpType! ctx'.raw = .func .func := by rw [hSpec.2.1, hFunc]
  have f : FunctionOp ctx.raw func := .of func ctx.raw
    (by unfold OperationPtr.isFunctionLike; rw [hFunc]; rfl)
  have f' : FunctionOp ctx'.raw func := .of func ctx'.raw
    (by unfold OperationPtr.isFunctionLike; rw [hFunc']; rfl)
  rw [OperationPtr.isRefinedByAsFunction, FunctionOp.of?_eq_some f,
    FunctionOp.of?_eq_some f']
  intro values values' mem hValues
  have hNum : func.getNumRegions ctx'.raw funcIn' = func.getNumRegions ctx.raw funcIn := by
    have := hSpec.2.2.2.2.2.1
    grind
  simp only [interpretFunction, hNum]
  split
  · simp [Interp.isRefinedBy]
  next hRegions =>
  simp only [interpretRegion]
  have hRegions' : 0 < func.getNumRegions ctx.raw funcIn := by omega
  have regionIn : (f.getFunctionBody funcIn hRegions').InBounds ctx.raw := by
    have := ctx.wellFormed.inBounds
    simp only [FunctionOp.getFunctionBody]
    grind
  have hBody : f'.getFunctionBody funcIn' (by omega) = f.getFunctionBody funcIn hRegions' := by
    have := hSpec.2.2.2.2.2.2.1
    simp only [FunctionOp.getFunctionBody]
    grind
  have hFirst := L.firstBlock regionIn
  split
  next hNone => simp [Interp.isRefinedBy]
  next block hBlock =>
    have blockIn : block.InBounds ctx.raw := by grind
    have hNotConverted := L.entryNotConverted regionIn (block := block) (by grind)
    split
    next hNone' => grind
    next block' hBlock' =>
      obtain rfl : block' = block := by grind
      have hCfg := L.interpretBlockCFG_lowered hMono (values := values) (values' := values')
        (state := ⟨VariableState.empty ctx, mem⟩) (state' := ⟨VariableState.empty ctx', mem⟩)
        blockIn ⟨rfl, ⟨rfl, fun v vIn sv hv => by simp [VariableState.empty,
          VariableState.getVar?] at hv⟩, ConstantsHold.empty,
          by simpa [hNotConverted] using hValues⟩
      rcases hsrc : interpretBlockCFG block' values ⟨VariableState.empty ctx, mem⟩ blockIn
        with _ | _ | ⟨source, results⟩
      · simp [Interp.isRefinedBy, bind]
      · simp [Interp.isRefinedBy, bind]
      · simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at hCfg
        obtain ⟨⟨target, results'⟩, hTarget, hMem, hResults⟩ := hCfg
        simp only [bind, hTarget, pure, Interp.isRefinedBy]
        exact ⟨hMem, hResults⟩

include L in
/-- A module is refined by its branch lowering. -/
theorem isModuleRefinedBy (hMono : MonotoneOps ctx) (module : OperationPtr) :
    module.isModuleRefinedBy ctx module ctx' := by
  intro func funcIn name hTop
  have hBranch : ¬ func.IsGmirBranch ctx.raw := by
    simp [OperationPtr.IsGmirBranch, hTop.isFunc]
  have hSpec := L.opSpec funcIn hBranch
  refine ⟨func, hSpec.1, ⟨?_, ?_, ?_⟩, L.isRefinedByAsFunction hMono funcIn hBranch hTop.isFunc⟩
  · rw [hSpec.2.1, hTop.isFunc]
  · rw [hSpec.2.2.1]; exact hTop.hasName
  · rw [hSpec.2.2.2.2.2.2.2]; exact hTop.isTopLevel

end BranchLowering

end Veir
