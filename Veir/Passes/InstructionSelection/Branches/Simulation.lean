module

public import Veir.Passes.InstructionSelection.Branches.Spec
public import Veir.Passes.InstructionSelection.Branches.Casts

import Veir.Interpreter.Lemmas
import Veir.Interpreter.Refinement.Lemmas
import Veir.Interpreter.Refinement.Monotonicity
import Veir.Dialects.Monotonicity
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

A module is refined by any module that is its `BranchLowering`, in assembly
mode. The states of the two runs are related through the map that sends an
argument of a converted block to its cast, and they are related after the casts
at the start of a block, where every value of the source has its counterpart
again. Values are compared in the memory of the source, which the casts and the
branches leave alone.
-/

namespace Veir

/-! ## Facts about the interpreter that do not depend on the lowering -/

/-- A refinement of a value conforms to the types the value conforms to. -/
theorem RuntimeValue.Conforms.of_isRefinedBy {m : RefinementMode} {source target : RuntimeValue}
    {type : TypeAttr} (hConforms : source.Conforms type) (hRefined : source ⊒[m] target) :
    target.Conforms type := by
  obtain ⟨attr, hattr⟩ := type
  cases source <;> cases target <;> simp only [RuntimeValue.isRefinedBy] at hRefined
  all_goals cases attr <;> simp_all [RuntimeValue.Conforms]
  all_goals grind

/-- A register is a value of the register type. -/
theorem RuntimeValue.reg_conforms {reg : Data.RISCV.Reg} :
    (RuntimeValue.reg reg).Conforms (RegisterType.mk : TypeAttr) := by
  generalize hType : (RegisterType.mk : TypeAttr) = type
  have hVal : type.val = .registerType (.mk none) := by
    rw [← hType]
    simp only [TypeAttr.of_def, Attribute.of_registerType]
  obtain ⟨attr, hattr⟩ := type
  cases attr <;> simp_all only [RuntimeValue.Conforms, reduceCtorEq]

/-- The value that stands for a missing one does not have a type that fits a register. -/
theorem RuntimeValue.not_conforms_default_of_fitsRegister {type : TypeAttr}
    (hFits : fitsRegister type) : ¬ (default : RuntimeValue).Conforms type := by
  obtain ⟨attr, hattr⟩ := type
  change ¬ (RuntimeValue.int 0 default).Conforms _
  cases attr <;> simp_all [fitsRegister, RuntimeValue.Conforms]
  omega

/-- A refinement of an array of values conforms to the types the array conforms to. -/
theorem RuntimeValue.ArrayConforms.of_isRefinedBy {m : RefinementMode}
    {source target : Array RuntimeValue} {types : Array TypeAttr}
    (hConforms : RuntimeValue.ArrayConforms source types)
    (hRefined : source ⊒[m] target) : RuntimeValue.ArrayConforms target types := by
  refine ⟨by grind [RuntimeValue.arrayIsRefinedBy, RuntimeValue.ArrayConforms], fun i hi => ?_⟩
  have hi' : i < source.size := by grind [RuntimeValue.arrayIsRefinedBy]
  exact (hConforms.2 i hi').of_isRefinedBy (hRefined.2 i hi')

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
theorem interpretOp_monotone_of_preservesOperation {asm : Bool}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    {mapping : ValueMapping ctx ctx'} {op op' : OperationPtr}
    (opIn : op.InBounds ctx.raw) (opIn' : op'.InBounds ctx'.raw)
    (hState : state.isRefinedBy state' mapping asm)
    (hPreserves : mapping.PreservesOperation op op') :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState ctx' × Option ControlFlowAction) =>
        r₁.1.isRefinedBy r₂.1 mapping asm ∧
          ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2 (.of asm r₁.1.memory))
      (interpretOp op state opIn)
      (interpretOp op' state' opIn') := by
  rcases hsrc : interpretOp op state opIn with _ | _ | ⟨state₂, act⟩
  · simp [Interp.isRefinedBy]
  · simp [Interp.isRefinedBy]
  have ⟨operands, hSrcOps⟩ : ∃ operands, state.variables.getOperandValues op = some operands := by
    grind [interpretOp]
  obtain ⟨operands', hTgtOps, hOpsRef⟩ :=
    VariableState.getOperandValues_isRefinedBy hState.2.1 opIn hPreserves.operands hSrcOps
  have hMem : state.memory = state'.memory := hState.1
  have hPR1 := interpretOp'_monotone asm (op.getOpType! ctx.raw)
    (op.getProperties! ctx.raw (op.getOpType! ctx.raw)) (op.getResultTypes! ctx.raw)
    operands operands' (op.getSuccessors! ctx.raw) state.memory hState.2.2 hOpsRef
  have hInterp'Eq : op'.interpret ctx'.raw operands' state'.memory =
                    op.interpret ctx.raw operands' state.memory := by
     grind [interpretOp'_opType_cast, cases ValueMapping.PreservesOperation]
  simp only [Interp.isRefinedBy_ok_target_iff, Prod.exists]
  have ⟨resValues, hinterp', hResValues⟩ :=
    (interpretOp_ok_iff_of_getOperandValues_eq_some hSrcOps).mp hsrc
  simp only [hinterp', Interp.isRefinedBy_ok_target_iff, OperationResult.isRefinedByFrom,
    OperationResult.isRefinedBy, Prod.exists] at hPR1
  have ⟨resValues', memory'₂, act', hinterp'Tgt, ⟨resValuesRef, memoryEq, actRef, hwf⟩, hExt⟩ :=
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
  have stateVarRef := VariableState.isRefinedBy_extends hExt hState.2.1
  grind [InterpreterState.isRefinedBy,
    VariableState.setResultValues?_isRefinedBy stateVarRef resValuesRef,
    cases ValueMapping.PreservesOperation]

/-! ## The map between the values of the two modules -/

namespace BranchLowering

variable (L : BranchLowering ctx ctx')

/-- The value of `ctx'` that stands for a value of `ctx`. -/
abbrev mapValue (value : ValuePtr) : ValuePtr :=
  lowerValue L.converted L.argCast value

theorem argCast_numResults {arg : BlockArgumentPtr} (argIn : arg.InBounds ctx.raw)
    (hConverted : L.converted arg.block) : (L.argCast arg).getNumResults! ctx'.raw = 1 := by
  have := (L.argCastSpec argIn hConverted).2.2.2.1
  rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, this]; rfl

theorem operandCast_numResults {op : OperationPtr} {i : Nat} (opIn : op.InBounds ctx.raw)
    (hBranch : op.IsLlvmBranch ctx.raw) (hi : i < op.getNumOperands! ctx.raw) :
    (L.operandCast op i).getNumResults! ctx'.raw = 1 := by
  have := (L.operandCastSpec opIn hBranch hi).2.2.2.1
  rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, this]; rfl

include L in
theorem numResults {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : ¬ op.IsLlvmBranch ctx.raw) :
    op.getNumResults! ctx'.raw = op.getNumResults! ctx.raw := by
  have := (L.opSpec opIn hBranch).2.2.2.1
  rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, this, OperationPtr.getResultTypes!.size_eq_getNumResults!]

theorem mapValue_inBounds {value : ValuePtr} (valueIn : value.InBounds ctx.raw) :
    (L.mapValue value).InBounds ctx'.raw := by
  rcases value with result | arg
  · simp only [mapValue, lowerValue, ValuePtr.inBounds_opResult] at valueIn ⊢
    obtain ⟨opIn, hIndex⟩ := OpResultPtr.inBounds_def.mp valueIn
    have hBranch : ¬ result.op.IsLlvmBranch ctx.raw := fun h => by
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
    (hBranch : ¬ op.IsLlvmBranch ctx.raw)
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

/-- No value stands for the cast of an operand of a branch. -/
theorem mapValue_ne_operandCast {value : ValuePtr} {op : OperationPtr} {i : Nat}
    (valueIn : value.InBounds ctx.raw) (opIn : op.InBounds ctx.raw)
    (hBranch : op.IsLlvmBranch ctx.raw) (hi : i < op.getNumOperands! ctx.raw) :
    L.mapValue value ≠ (L.operandCast op i).getResult 0 := by
  intro h
  have hSpec := L.operandCastSpec opIn hBranch hi
  rcases value with result | arg
  · simp only [mapValue, lowerValue, OperationPtr.getResult_def, ValuePtr.opResult.injEq] at h
    obtain ⟨opIn', _⟩ := OpResultPtr.inBounds_def.mp (by simpa using valueIn)
    grind
  · simp only [mapValue, lowerValue] at h
    split at h
    next hConverted =>
      simp only [OperationPtr.getResult_def, ValuePtr.opResult.injEq, OpResultPtr.mk.injEq,
        and_true] at h
      exact hSpec.2.2.2.2.2.2 arg (by simpa using valueIn) hConverted h
    next => simp [OperationPtr.getResult_def] at h

/-- An operation other than the two branches is the same operation in the lowering. -/
theorem preservesOperation {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : ¬ op.IsLlvmBranch ctx.raw) :
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
  wf : source.memory.LayoutWf
  arguments : ∀ i, i < block.getNumArguments! ctx.raw → ∃ sourceValue value reg,
    source.variables.getVar? (block.getArgument i) = some sourceValue ∧
    sourceValue ⊒[.asm source.memory] value ∧ value.toReg? source.memory = some reg ∧
    target.variables.getVar? (block.getArgument i) = some (.reg reg)
  values : ∀ value, value.InBounds ctx.raw → ∀ sourceValue,
    source.variables.getVar? value = some sourceValue →
    (∃ i ∈ pending, value = block.getArgument i) ∨
    ∃ targetValue, target.variables.getVar? (L.mapValue value) = some targetValue ∧
      sourceValue ⊒[.asm source.memory] targetValue

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
    obtain ⟨reg', result, hReg', hResult, hRefinedResult, hConformsResult⟩ :=
      RuntimeValue.isRefinedBy_ofReg?_toReg? hInv.wf hFits hConforms hRefined
    obtain rfl : reg' = reg := by simpa [hReg] using hReg'.symm
    obtain ⟨target', hOk, hMem, hGet⟩ := interpretOp_cast (state := target) hSpec.1 hSpec.2.2.1
      hSpec.2.2.2.1 hSpec.2.2.2.2 hTarget
      (fun properties successors => interpretOp'_cast_ofReg hResult properties successors _)
      hConformsResult
    have hInv' : L.EntryInv block source target' pending := by
      refine ⟨hInv.memory.trans hMem.symm, hInv.wf, fun j hj => ?_, fun v vIn sv hv => ?_⟩
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
    {state' : InterpreterState ctx'} (hState : state.isRefinedBy state' L.mapping true)
    {values values' : Array RuntimeValue} (hValues : RegistersOf state.memory values values')
    {variables : VariableState ctx}
    (hSet : state.variables.setArgumentValues? block values blockIn = some variables) :
    ∃ variables' target,
      state'.variables.setArgumentValues? block values' (L.blockIn blockIn) = some variables' ∧
      interpretOpList ((List.range (block.getNumArguments! ctx.raw)).reverse.map
          (fun i => L.argCast (block.getArgument i))) ⟨variables', state'.memory⟩
        (L.entryCasts_inBounds blockIn hConverted (by simp)) = .ok (target, none) ∧
      InterpreterState.isRefinedBy ⟨variables, state.memory⟩ target L.mapping true := by
  have hNum := L.numArguments blockIn
  /- The source values conform to types that fit a register, so none of them is missing. -/
  have hSourceConforms := (VariableState.setArgumentValues?_isSome_iff_conforms
    state.variables (blockInBounds := blockIn)).mpr ⟨variables, hSet⟩
  have hSize : ∀ i, i < block.getNumArguments! ctx.raw → i < values.size := by
    intro i hi
    apply Classical.byContradiction
    intro hNot
    have hFits := (L.argTypeConverted blockIn hConverted hi).2
    have hConforms := hSourceConforms i hi
    rw [getElem!_neg values i hNot] at hConforms
    exact RuntimeValue.not_conforms_default_of_fitsRegister hFits hConforms
  /- The target is passed registers, which is what its arguments are. -/
  obtain ⟨variables', hSet'⟩ := (VariableState.setArgumentValues?_isSome_iff_conforms
      state'.variables (blockInBounds := L.blockIn blockIn) (values := values')).mp (by
    intro j hj
    rw [hNum] at hj
    obtain ⟨_, reg, _, _, hReg⟩ := hValues.2 j (hSize j hj)
    rw [(L.argTypeConverted blockIn hConverted hj).1, hReg]
    exact RuntimeValue.reg_conforms)
  have hInv : L.EntryInv block ⟨variables, state.memory⟩ ⟨variables', state'.memory⟩
      (List.range (block.getNumArguments! ctx.raw)).reverse := by
    refine ⟨hState.1, by simpa using hState.2.2, fun i hi => ?_, fun v vIn sv hv => ?_⟩
    · obtain ⟨value, reg, hRefined, hReg, hTarget⟩ := hValues.2 i (hSize i hi)
      refine ⟨values[i]!, value, reg, ?_, hRefined, hReg, ?_⟩
      · exact VariableState.getVar?_getArgument_of_setArgumentValues? hi hSet
      · rw [← hTarget]
        exact VariableState.getVar?_getArgument_of_setArgumentValues? (by rw [hNum]; exact hi) hSet'
    · by_cases hMem : v ∈ block.getArguments! ctx.raw
      · obtain ⟨i, hi, rfl⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp hMem
        exact .inl ⟨i, by simpa using hi, rfl⟩
      · rw [VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! hMem hSet] at hv
        obtain ⟨tv, hTv, hRef⟩ := hState.2.1 v vIn sv hv
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
  refine ⟨variables', target, hSet', hOk, hInv'.memory, fun v vIn sv hv => ?_, hState.2.2⟩
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
    {state' : InterpreterState ctx'} (hState : state.isRefinedBy state' L.mapping true)
    {values values' : Array RuntimeValue} (hValues : values ⊒[.asm state.memory] values')
    {variables : VariableState ctx}
    (hSet : state.variables.setArgumentValues? block values blockIn = some variables) :
    ∃ variables',
      state'.variables.setArgumentValues? block values' (L.blockIn blockIn) = some variables' ∧
      InterpreterState.isRefinedBy ⟨variables, state.memory⟩ ⟨variables', state'.memory⟩
        L.mapping true := by
  have hNum := L.numArguments blockIn
  have hSourceConforms := (VariableState.setArgumentValues?_isSome_iff_conforms
    state.variables (blockInBounds := blockIn)).mpr ⟨variables, hSet⟩
  have hRefined : ∀ i : Nat, values[i]! ⊒[.asm state.memory] values'[i]! := by
    intro i
    by_cases hi : i < values.size
    · exact hValues.2 i hi
    · rw [getElem!_neg values i hi, getElem!_neg values' i (by rw [← hValues.1]; exact hi)]
      exact RuntimeValue.isRefinedBy_refl_asm
        (show (RuntimeValue.int 0 default).ValidIn state.memory from trivial)
  obtain ⟨variables', hSet'⟩ := (VariableState.setArgumentValues?_isSome_iff_conforms
      state'.variables (blockInBounds := L.blockIn blockIn) (values := values')).mp (by
    intro j hj
    rw [hNum] at hj
    rw [L.argTypeOther blockIn hConverted hj]
    exact (hSourceConforms j hj).of_isRefinedBy (hRefined j))
  refine ⟨variables', hSet', hState.1, fun v vIn sv hv => ?_, hState.2.2⟩
  simp only [mapping_val]
  by_cases hMem : v ∈ block.getArguments! ctx.raw
  · obtain ⟨i, hi, rfl⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp hMem
    have hMap : L.mapValue (block.getArgument i) = block.getArgument i := by
      simp [mapValue, lowerValue, BlockPtr.getArgument_def, hConverted]
    rw [VariableState.getVar?_getArgument_of_setArgumentValues? hi hSet] at hv
    rw [hMap, VariableState.getVar?_getArgument_of_setArgumentValues? (by rw [hNum]; exact hi) hSet']
    exact ⟨_, rfl, by simpa using (Option.some.inj hv) ▸ hRefined i⟩
  · rw [VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! hMem hSet] at hv
    obtain ⟨tv, hTv, hRef⟩ := hState.2.1 v vIn sv hv
    refine ⟨tv, ?_, hRef⟩
    rw [VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! ?_ hSet']
    · exact hTv
    · intro hMem'
      obtain ⟨j, hj, hEq⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp hMem'
      have := (L.eq_of_mapValue_eq_getArgument hEq.symm).1
      exact hMem (BlockPtr.getArguments!.mem_iff_exists_index.mpr
        ⟨j, by rw [← hNum]; exact hj, this.symm⟩)

/-! ## The two branches -/

theorem operandCasts_inBounds {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : op.IsLlvmBranch ctx.raw) {k : Nat} (hk : k ≤ op.getNumOperands! ctx.raw) :
    ∀ cast ∈ (List.range k).map (L.operandCast op), cast.InBounds ctx'.raw := by
  intro cast hCast
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hCast
  exact (L.operandCastSpec opIn hBranch (by simp at hi; omega)).1

/--
  The casts in front of the new branch bind the registers of the operands, and
  keep the states related since no value of the source stands for a cast.
-/
theorem interpretOpList_operandCasts {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : op.IsLlvmBranch ctx.raw) {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} (hState : state.isRefinedBy state' L.mapping true)
    {operands : Array RuntimeValue}
    (hOperands : state.variables.getOperandValues op = some operands)
    {k : Nat} (hk : k ≤ op.getNumOperands! ctx.raw) :
    ∃ (target : InterpreterState ctx') (registers : Array RuntimeValue),
      interpretOpList ((List.range k).map (L.operandCast op)) state'
        (L.operandCasts_inBounds opIn hBranch hk) = .ok (target, none) ∧
      state.isRefinedBy target L.mapping true ∧ registers.size = k ∧
      ∀ i, i < k → ∃ value reg, operands[i]! ⊒[.asm state.memory] value ∧
        value.toReg? state.memory = some reg ∧
        registers[i]! = .reg reg ∧
        target.variables.getVar? ((L.operandCast op i).getResult 0) = some registers[i]! := by
  induction k with
  | zero => exact ⟨state', #[], by simp [interpretOpList_nil], hState, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨target, registers, hOk, hTarget, hSize, hRegisters⟩ := ih (by omega)
    have hk' : k < op.getNumOperands! ctx.raw := by omega
    have hSpec := L.operandCastSpec opIn hBranch hk'
    have ⟨_, hOperandValues⟩ := VariableState.getOperandValues_eq_some_iff.mp hOperands
    have hSource := hOperandValues k hk'
    have operandIn : (op.getOperand! ctx.raw k).InBounds ctx.raw :=
      OperationPtr.getOperands!_inBounds ctx.wellFormed.inBounds opIn
        (OperationPtr.getOperands!.mem_getOperand hk')
    obtain ⟨value, hValue, hRefined⟩ := hTarget.2.1 _ operandIn _ hSource
    simp only [mapping_val] at hValue
    have hConforms := VariableState.getVar?_conforms hSource
    obtain ⟨reg, _, hReg, _⟩ := RuntimeValue.isRefinedBy_ofReg?_toReg? (by simpa using hState.2.2)
      hSpec.2.2.2.2.2.1 hConforms hRefined
    obtain ⟨target', hOk', hMem, hGet⟩ := interpretOp_cast (state := target) hSpec.1 hSpec.2.2.1
      hSpec.2.2.2.1 hSpec.2.2.2.2.1 hValue
      (fun properties successors => interpretOp'_cast_toReg (hTarget.1 ▸ hReg) properties successors)
      RuntimeValue.reg_conforms
    refine ⟨target', registers.push (.reg reg), ?_, ⟨hTarget.1.trans hMem.symm, ?_, hState.2.2⟩,
      by simp [hSize], fun i hi => ?_⟩
    · simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        interpretOpList_append, hOk, interpretOpList_cons, hOk', interpretOpList_nil]
    · intro v vIn sv hv
      obtain ⟨tv, hTv, hRef⟩ := hTarget.2.1 v vIn sv hv
      refine ⟨tv, ?_, hRef⟩
      simp only [mapping_val] at hTv ⊢
      rw [hGet]
      simpa [L.mapValue_ne_operandCast vIn opIn hBranch hk'] using hTv
    · by_cases hEq : i = k
      · subst hEq
        refine ⟨value, reg, hRefined, hReg, by simp [← hSize], ?_⟩
        rw [hGet]; simp [← hSize]
      · obtain ⟨value', reg', h₁, h₂, h₃, h₄⟩ := hRegisters i (by omega)
        have hLt : i < registers.size := by omega
        have hPush : (registers.push (.reg reg))[i]! = registers[i]! := by
          rw [getElem!_pos (registers.push (.reg reg)) i (by simp; omega),
            getElem!_pos registers i hLt, Array.getElem_push_lt hLt]
        refine ⟨value', reg', h₁, h₂, hPush ▸ h₃, ?_⟩
        have hNe : ((L.operandCast op i).getResult 0 : ValuePtr) ≠
            (L.operandCast op k).getResult 0 := by
          intro h
          simp only [OperationPtr.getResult_def, ValuePtr.opResult.injEq, OpResultPtr.mk.injEq,
            and_true] at h
          exact hEq (L.operandCastInj opIn hBranch (by omega) hk' h)
        rw [hGet, hPush]
        simpa [hNe] using h₄

theorem lowerOp_inBounds {op : OperationPtr} (opIn : op.InBounds ctx.raw) :
    ∀ op' ∈ lowerOp ctx.raw L.operandCast L.newBranch op, op'.InBounds ctx'.raw := by
  intro op' hOp'
  simp only [lowerOp] at hOp'
  split at hOp'
  next hBranch =>
    rcases List.mem_append.mp hOp' with h | h
    · exact L.operandCasts_inBounds opIn hBranch (Nat.le_refl _) op' h
    · obtain rfl : op' = L.newBranch op := by simpa using h
      exact (L.newBranchSpec opIn hBranch).1
  next hBranch =>
    obtain rfl : op' = op := by simpa using hOp'
    exact (L.opSpec opIn hBranch).1

/-- How the outcome of a branch relates to the outcome of its lowering. -/
abbrev BranchRel (source : InterpreterState ctx × Option ControlFlowAction)
    (target : InterpreterState ctx' × Option ControlFlowAction) : Prop :=
  source.1.isRefinedBy target.1 L.mapping true ∧
  ∃ values values' dest, source.2 = some (.branch values dest) ∧
    target.2 = some (.branch values' dest) ∧ L.converted dest ∧
    RegistersOf source.1.memory values values'

/-- The new branch reads the registers that the casts in front of it bound. -/
theorem getOperandValues_newBranch {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : op.IsLlvmBranch ctx.raw) {target : InterpreterState ctx'}
    {registers : Array RuntimeValue} (hSize : registers.size = op.getNumOperands! ctx.raw)
    (hRegisters : ∀ i, i < op.getNumOperands! ctx.raw →
      target.variables.getVar? ((L.operandCast op i).getResult 0) = some registers[i]!) :
    target.variables.getOperandValues (L.newBranch op) = some registers := by
  have hSpec := (L.newBranchSpec opIn hBranch).2.2.2
  have hNum : (L.newBranch op).getNumOperands! ctx'.raw = op.getNumOperands! ctx.raw := by
    rw [← OperationPtr.getOperands!.size_eq_getNumOperands!, hSpec]; simp
  refine VariableState.getOperandValues_eq_some_iff.mpr ⟨by rw [hNum, hSize], fun i hi => ?_⟩
  rw [hNum] at hi
  rw [← OperationPtr.getOperands!.getElem!_eq_getOperand!, hSpec]
  rw [getElem!_pos _ i (by simpa using hi)]
  simpa using hRegisters i hi

/-- A branch is refined by the casts of its operands followed by the RISC-V branch. -/
theorem interpretOp_llvmBranch {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : op.IsLlvmBranch ctx.raw) {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} (hState : state.isRefinedBy state' L.mapping true) :
    Interp.isRefinedBy L.BranchRel (interpretOp op state opIn)
      (interpretOpList (lowerOp ctx.raw L.operandCast L.newBranch op) state'
        (L.lowerOp_inBounds opIn)) := by
  rcases hsrc : interpretOp op state opIn with _ | _ | ⟨source₁, action⟩
  · simp [Interp.isRefinedBy]
  · simp [Interp.isRefinedBy]
  obtain ⟨operands, results, mem₁, variables₁, hOperands, hInterp, hSetResults, rfl⟩ :=
    interpretOp_some_iff.mp hsrc
  have hNumOperands := (VariableState.getOperandValues_eq_some_iff.mp hOperands).1
  obtain ⟨target, registers, hOk, hTarget, hSize, hRegisters⟩ :=
    L.interpretOpList_operandCasts opIn hBranch hState hOperands (Nat.le_refl _)
  have hRegistersOf : RegistersOf state.memory operands registers :=
    ⟨by omega, fun i hi => by
      obtain ⟨value, reg, h₁, h₂, h₃, _⟩ := hRegisters i (by omega)
      exact ⟨value, reg, h₁, h₂, h₃⟩⟩
  have hNewOperands := L.getOperandValues_newBranch opIn hBranch hSize
    (fun i hi => (hRegisters i hi).choose_spec.choose_spec.2.2.2)
  have hSpec := L.newBranchSpec opIn hBranch
  /- Both branches compute the same successor, from the operands and from their registers. -/
  have hData : ∃ values values' dest, results = #[] ∧ mem₁ = state.memory ∧
      action = some (.branch values dest) ∧
      (L.newBranch op).interpret ctx'.raw registers target.memory =
        .ok (#[], target.memory, some (.branch values' dest)) ∧
      RegistersOf state.memory values values' := by
    rw [← hTarget.1]
    simp only [OperationPtr.interpret, hSpec.2.2.1] at hInterp ⊢
    rcases hBranch with hType | hType
    · rw [interpretOp'_opType_cast hType (OperationPtr.getProperties!_cast hType)] at hInterp
      have hType' := L.newBranchBr opIn hType
      rw [interpretOp'_opType_cast hType' (OperationPtr.getProperties!_cast hType')]
      exact interpretOp'_br_registers hInterp hRegistersOf _ _
    · rw [interpretOp'_opType_cast hType (OperationPtr.getProperties!_cast hType)] at hInterp
      have hType' := L.newBranchCondBr opIn hType
      rw [interpretOp'_opType_cast hType'.1 (OperationPtr.getProperties!_cast hType'.1)]
      exact interpretOp'_cond_br_registers hInterp hRegistersOf _ _ hType'.2
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
  have hList : interpretOpList (lowerOp ctx.raw L.operandCast L.newBranch op) state'
      (L.lowerOp_inBounds opIn) = .ok (target, some (.branch values' dest)) := by
    simp only [lowerOp, hBranch, ↓reduceIte, interpretOpList_append, hOk, interpretOpList_cons,
      hNewOk]
  rw [hList]
  exact ⟨hTarget, values, values', dest, rfl, rfl,
    L.branchSuccessorConverted opIn hBranch hDest, hValues⟩

/-! ## Blocks -/

/-- How the control flow of the source relates to that of the lowering. -/
@[expose]
def ActionRel (mem : MemoryState) : Option ControlFlowAction → Option ControlFlowAction → Prop
  | none, none => True
  | some (.return values), some (.return values') => values ⊒[.asm mem] values'
  | some (.branch values dest), some (.branch values' dest') =>
    dest = dest' ∧ L.converted dest ∧ RegistersOf mem values values'
  | _, _ => False

theorem flatMap_lowerOp_inBounds {ops : List OperationPtr}
    (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw) :
    ∀ op' ∈ ops.flatMap (lowerOp ctx.raw L.operandCast L.newBranch), op'.InBounds ctx'.raw := by
  intro op' hOp'
  obtain ⟨op, hOp, hMem⟩ := List.mem_flatMap.mp hOp'
  exact L.lowerOp_inBounds (opsIn op hOp) op' hMem

/-- A list of operations is refined by its lowering. -/
theorem interpretOpList_lowered {ops : List OperationPtr}
    (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw) {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} (hState : state.isRefinedBy state' L.mapping true) :
    Interp.isRefinedBy
      (fun source target => source.1.isRefinedBy target.1 L.mapping true ∧
        L.ActionRel source.1.memory source.2 target.2)
      (interpretOpList ops state opsIn)
      (interpretOpList (ops.flatMap (lowerOp ctx.raw L.operandCast L.newBranch)) state'
        (L.flatMap_lowerOp_inBounds opsIn)) := by
  induction ops generalizing state state' with
  | nil => simpa [interpretOpList_nil, Interp.isRefinedBy, ActionRel] using hState
  | cons op ops ih =>
    have opIn := opsIn op (by simp)
    simp only [List.flatMap_cons, interpretOpList_cons, interpretOpList_append]
    by_cases hBranch : op.IsLlvmBranch ctx.raw
    · have hOp := L.interpretOp_llvmBranch opIn hBranch hState
      rcases hsrc : interpretOp op state opIn with _ | _ | ⟨source₁, action⟩
      · simp [Interp.isRefinedBy]
      · simp [Interp.isRefinedBy]
      · simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at hOp
        obtain ⟨⟨target₁, action'⟩, hTarget, hRel, values, values', dest, rfl, rfl, hDest, hValues⟩ :=
          hOp
        simp only [hTarget, Interp.isRefinedBy]
        exact ⟨hRel, rfl, hDest, hValues⟩
    · have hOp := interpretOp_monotone_of_preservesOperation opIn (L.opSpec opIn hBranch).1
        hState (L.preservesOperation opIn hBranch)
      have hLower : lowerOp ctx.raw L.operandCast L.newBranch op = [op] := by
        simp [lowerOp, hBranch]
      rcases hsrc : interpretOp op state opIn with _ | _ | ⟨source₁, action⟩
      · simp [Interp.isRefinedBy]
      · simp [Interp.isRefinedBy]
      · simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at hOp
        obtain ⟨⟨target₁, action'⟩, hTarget, hRel, hAction⟩ := hOp
        rw [interpretOpList_congr hLower]
        simp only [interpretOpList_cons, interpretOpList_nil, hTarget]
        rcases action with _ | cf
        · obtain rfl : action' = none := by
            cases action' <;> simp_all [ControlFlowAction.optionIsRefinedBy]
          exact ih (fun op' hOp' => opsIn op' (by simp [hOp'])) hRel
        · obtain ⟨cf', rfl, hCf⟩ : ∃ cf', action' = some cf' ∧
              cf.isRefinedBy cf' (.of true source₁.memory) := by
            cases action' <;> simp_all [ControlFlowAction.optionIsRefinedBy]
          rcases cf with values | ⟨values, dest⟩
          · rcases cf' with values' | _
            · exact ⟨hRel, hCf⟩
            · simp [ControlFlowAction.isRefinedBy] at hCf
          · have := interpretOp_branch_dest_mem_getSuccessors! hsrc
            simp [(L.opSuccessors opIn hBranch).1] at this

/-- A list of operations that ends in a terminator is refined by its lowering. -/
theorem interpretTerminatedOpList_lowered {ops : List OperationPtr}
    (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw) {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} (hState : state.isRefinedBy state' L.mapping true) :
    Interp.isRefinedBy
      (fun source target => source.1.isRefinedBy target.1 L.mapping true ∧
        L.ActionRel source.1.memory (some source.2) (some target.2))
      (interpretTerminatedOpList ops state opsIn)
      (interpretTerminatedOpList (ops.flatMap (lowerOp ctx.raw L.operandCast L.newBranch)) state'
        (L.flatMap_lowerOp_inBounds opsIn)) := by
  have hList := L.interpretOpList_lowered opsIn hState
  simp only [interpretTerminatedOpList, bind]
  rcases hsrc : interpretOpList ops state opsIn with _ | _ | ⟨source₁, action⟩
  · simp [Interp.isRefinedBy]
  · simp [Interp.isRefinedBy]
  · simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at hList
    obtain ⟨⟨target₁, action'⟩, hTarget, hRel, hAction⟩ := hList
    simp only [hTarget]
    rcases action with _ | cf
    · simp [Interp.isRefinedBy]
    · rcases action' with _ | cf'
      · simp [ActionRel] at hAction
      · exact ⟨hRel, hAction⟩

/-- The calls of `interpretBlockCFG` in the two modules that correspond to each other. -/
@[expose]
def CallRel : BlockCallRel ctx ctx' :=
  fun block values state block' values' state' =>
    block' = block ∧ state.isRefinedBy state' L.mapping true ∧
    if L.converted block then RegistersOf state.memory values values'
    else values ⊒[.asm state.memory] values'

/-- The results of the two modules that correspond to each other. -/
abbrev ResultRel (source : InterpreterState ctx × Array RuntimeValue)
    (target : InterpreterState ctx' × Array RuntimeValue) : Prop :=
  source.1.memory = target.1.memory ∧ source.2 ⊒[.asm source.1.memory] target.2

/-- A block is refined by its lowering, and the blocks they branch to correspond again. -/
theorem interpretBlock_lowered {block block' : BlockPtr} {values values' : Array RuntimeValue}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    (blockIn : block.InBounds ctx.raw) (blockIn' : block'.InBounds ctx'.raw)
    (hRel : L.CallRel block values state block' values' state') :
    Interp.isRefinedBy (L.CallRel.Step ResultRel)
      (interpretBlock block values state blockIn)
      (interpretBlock block' values' state' blockIn') := by
  obtain ⟨rfl, hState, hValues⟩ := hRel
  rw [interpretBlock_eq blockIn, interpretBlock_eq blockIn']
  rcases hSet : state.variables.setArgumentValues? block' values blockIn with _ | variables
  · simp [Interp.isRefinedBy]
  simp only
  /- After the arguments are set, and the casts ran in a converted block, the states are related. -/
  have hBody : ∀ (target : InterpreterState ctx'),
      InterpreterState.isRefinedBy ⟨variables, state.memory⟩ target L.mapping true →
      Interp.isRefinedBy (L.CallRel.Step ResultRel)
        (interpretTerminatedOpList (block'.operationList ctx.raw ctx.wellFormed blockIn).toList
          ⟨variables, state.memory⟩ (by grind [BlockPtr.operationListWF, BlockPtr.OpChain]))
        (interpretTerminatedOpList ((block'.operationList ctx.raw ctx.wellFormed blockIn).toList.flatMap
          (lowerOp ctx.raw L.operandCast L.newBranch)) target
          (L.flatMap_lowerOp_inBounds (by grind [BlockPtr.operationListWF, BlockPtr.OpChain]))) := by
    intro target hTarget
    have hOps := L.interpretTerminatedOpList_lowered
      (ops := (block'.operationList ctx.raw ctx.wellFormed blockIn).toList)
      (by grind [BlockPtr.operationListWF, BlockPtr.OpChain]) hTarget
    rcases hsrc : interpretTerminatedOpList _ _ _ with _ | _ | ⟨source₁, cf⟩
    · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]
    · simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at hOps
      obtain ⟨⟨target₁, cf'⟩, hTarget₁, hRel₁, hAction⟩ := hOps
      simp only [hTarget₁, Interp.isRefinedBy, BlockCallRel.Step]
      rcases cf with res | ⟨res, dest⟩ <;> rcases cf' with res' | ⟨res', dest'⟩ <;>
        simp only [ActionRel] at hAction ⊢
      · exact ⟨hRel₁.1, hAction⟩
      · obtain ⟨rfl, hDest, hRegisters⟩ := hAction
        intro destIn
        exact ⟨L.blockIn destIn, rfl, hRel₁, by simp [hDest, hRegisters]⟩
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
theorem interpretBlockCFG_lowered {block : BlockPtr} {values values' : Array RuntimeValue}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    (blockIn : block.InBounds ctx.raw)
    (hRel : L.CallRel block values state block values' state') :
    Interp.isRefinedBy ResultRel
      (interpretBlockCFG block values state blockIn)
      (interpretBlockCFG block values' state' (L.blockIn blockIn)) :=
  interpretBlockCFG_isRefinedBy
    (fun _ _ _ _ _ _ blockIn blockIn' hRel => L.interpretBlock_lowered blockIn blockIn' hRel)
    blockIn (L.blockIn blockIn) hRel

/-- A function is refined by its lowering. -/
theorem isRefinedByAsFunction {func : OperationPtr} (funcIn : func.InBounds ctx.raw)
    (hBranch : ¬ func.IsLlvmBranch ctx.raw) (hFunc : func.getOpType! ctx.raw = .func .func) :
    func.isRefinedByAsFunction ctx func ctx' funcIn (L.opSpec funcIn hBranch).1 true := by
  have hSpec := L.opSpec funcIn hBranch
  have funcIn' := hSpec.1
  have hFunc' : func.getOpType! ctx'.raw = .func .func := by rw [hSpec.2.1, hFunc]
  have f : FunctionOp ctx.raw func := .cast func ctx.raw
    (by unfold OperationPtr.isFunctionLike; rw [hFunc]; rfl)
  have f' : FunctionOp ctx'.raw func := .cast func ctx'.raw
    (by unfold OperationPtr.isFunctionLike; rw [hFunc']; rfl)
  rw [OperationPtr.isRefinedByAsFunction, FunctionOp.cast?_eq_some f,
    FunctionOp.cast?_eq_some f']
  intro values values' mem hwf hValues
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
      have hCfg := L.interpretBlockCFG_lowered (values := values) (values' := values')
        (state := ⟨VariableState.empty ctx, mem⟩) (state' := ⟨VariableState.empty ctx', mem⟩)
        blockIn ⟨rfl, ⟨rfl, fun v vIn sv hv => by simp [VariableState.empty,
          VariableState.getVar?] at hv, hwf⟩, by simpa [hNotConverted] using hValues⟩
      rcases hsrc : interpretBlockCFG block' values ⟨VariableState.empty ctx, mem⟩ blockIn
        with _ | _ | ⟨source, results⟩
      · simp [Interp.isRefinedBy, bind]
      · simp [Interp.isRefinedBy, bind]
      · simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at hCfg
        obtain ⟨⟨target, results'⟩, hTarget, hMem, hResults⟩ := hCfg
        simp only [bind, hTarget, pure, Interp.isRefinedBy]
        exact ⟨hMem, hResults⟩

include L in
/-- A module is refined by its branch lowering, in assembly mode. -/
theorem isModuleRefinedBy (module : OperationPtr) :
    module.isModuleRefinedBy ctx module ctx' true := by
  intro func funcIn name hTop
  have hBranch : ¬ func.IsLlvmBranch ctx.raw := by
    simp [OperationPtr.IsLlvmBranch, hTop.isFunc]
  have hSpec := L.opSpec funcIn hBranch
  refine ⟨func, hSpec.1, ⟨?_, ?_, ?_⟩, L.isRefinedByAsFunction funcIn hBranch hTop.isFunc⟩
  · rw [hSpec.2.1, hTop.isFunc]
  · rw [hSpec.2.2.1]; exact hTop.hasName
  · rw [hSpec.2.2.2.2.2.2.2]; exact hTop.isTopLevel

end BranchLowering

end Veir
