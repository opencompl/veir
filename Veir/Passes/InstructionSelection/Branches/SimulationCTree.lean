module

public import Veir.Passes.InstructionSelection.Branches.Simulation
public import Veir.Interpreter.CTreeRefinement.OpList
public import Veir.Interpreter.CTreeRefinement.Normalization

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
import all Veir.Interpreter.CTreeInterpreter

public section

/-!
# The branch lowering refines the module, in CTrees

The proof follows the one for `Interp` in `Simulation`, step by step, on the closed CFG loop that
`interpretRegion` normalizes to. A step of the loop that runs a whole block runs the list of its
operations (`blockStep_entry`), so the lists of a block and of its lowering are related as for
`Interp`.

The operations that the lowering inserts are casts and a RISC-V branch. A cast to a register of a
value that is poison, in part or in full, may give any register, so the target is described by
what it may return (`CTree.Returns`) rather than by what it returns.
-/

open CTree Veir.CTree

namespace Veir

variable {ctx ctx' : WfIRContext OpCode}

/-! ## Single operations in the target -/

/--
  A cast with one operand and one result, whose meaning on the value of the
  operand returns only outputs satisfying `Q`, binds its result to such an
  output and changes nothing else.
-/
theorem returns_interpretOperationTree_cast {op : OperationPtr} {state : InterpreterState ctx}
    {type : TypeAttr} {operand : ValuePtr} {input : RuntimeValue} {Q : RuntimeValue → Prop}
    (opIn : op.InBounds ctx.raw)
    (hType : op.getOpType! ctx.raw = .builtin .unrealized_conversion_cast)
    (hResultTypes : op.getResultTypes! ctx.raw = #[type])
    (hOperands : op.getOperands! ctx.raw = #[operand])
    (hInput : state.variables.getVar? operand = some input)
    (hInterp : ∀ properties successors,
      Returns (CTree.interpretOp' (.builtin .unrealized_conversion_cast) properties #[type] #[input]
        successors state.memory)
        (fun r => ∃ output, Q output ∧ output.Conforms type ∧ r = (#[output], state.memory, none))) :
    Returns (interpretOperationTree op state opIn) (fun r => r.2 = none ∧
      r.1.memory = state.memory ∧ ∃ output, Q output ∧ ∀ value, r.1.variables.getVar? value =
        if value = op.getResult 0 then some output else state.variables.getVar? value) := by
  have hVals : state.variables.getOperandValues op = some #[input] := by
    simp [VariableState.getOperandValues, hOperands, hInput]
  have key : ∀ (t : OpCode) (h : t = .builtin .unrealized_conversion_cast) (p : propertiesOf t)
      successors, Returns (CTree.interpretOp' t p #[type] #[input] successors state.memory)
        (fun r => ∃ output, Q output ∧ output.Conforms type ∧
          r = (#[output], state.memory, none)) := by
    intro t h p successors
    subst h
    exact hInterp p successors
  rw [interpretOperationTree_eq]
  simp only [hVals, hResultTypes]
  refine ((key _ hType _ _).inflate.inflate).bind ?_
  rintro ⟨results, mem, action⟩ ⟨output, hQ, hConforms, hEq⟩
  simp only [Prod.mk.injEq] at hEq
  obtain ⟨rfl, rfl, rfl⟩ := hEq
  have hConf : RuntimeValue.ArrayConforms #[output] (op.getResultTypes! ctx.raw) := by
    simp [RuntimeValue.ArrayConforms, hResultTypes, hConforms]
  obtain ⟨variables, hSet⟩ :=
    (VariableState.setResultValues?_isSome_iff_conforms state.variables opIn).mp hConf
  simp only [hSet]
  refine returns_pure.mpr ⟨rfl, rfl, output, hQ, fun value => ?_⟩
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
theorem interpretOperationTree_getRegister {op : OperationPtr} {state : InterpreterState ctx}
    (opIn : op.InBounds ctx.raw) (hType : op.getOpType! ctx.raw = .rv64 .get_register)
    (hResultTypes : op.getResultTypes! ctx.raw = #[(RegisterType.mk (some 0) : TypeAttr)])
    (hOperands : op.getOperands! ctx.raw = #[]) :
    ∃ state', interpretOperationTree op state opIn = pure (state', none) ∧
      state'.memory = state.memory ∧
      ∀ value, state'.variables.getVar? value =
        if value = op.getResult 0 then some (.reg ⟨0⟩) else state.variables.getVar? value := by
  obtain ⟨state', hOk, hMem, hGet⟩ := interpretOp_getRegister opIn hType hResultTypes hOperands
  refine ⟨state', ?_, hMem, hGet⟩
  rw [interpretOperationTree_eq_monadLift state opIn (by rw [hType]; rfl), hOk]
  rfl

/-- Setting the results of an operation other than a `g_constant` keeps every `g_constant` holding
its value. -/
theorem ConstantsHold.setResultValues? {op : OperationPtr} {opIn : op.InBounds ctx.raw}
    {state : InterpreterState ctx} {results : Array RuntimeValue} {variables : VariableState ctx}
    {mem : MemoryState} (hType : op.getOpType! ctx.raw ≠ .gmir .g_constant)
    (hSet : state.variables.setResultValues? op results opIn = some variables)
    (h : ConstantsHold state) : ConstantsHold (⟨variables, mem⟩ : InterpreterState ctx) := by
  intro constant constantIn hConstant value type t hValue hResultType hVal
  have hNe : constant ≠ op := by rintro rfl; exact hType hConstant
  rw [VariableState.getVar?_setResultValues?_of_notMem_getResults! (by
    intro hMem
    obtain ⟨i, _, hi⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp hMem
    grind [OperationPtr.getResult_def]) hSet] at hValue
  exact h constant constantIn hConstant value type t hValue hResultType hVal

/--
  Every operation of `ctx` is monotone in CTrees, in its operands and its memory.
  This is what the proof needs of the operations that the lowering keeps.
-/
@[expose]
def TreeMonotoneOps (ctx : WfIRContext OpCode) : Prop :=
  ∀ op : OperationPtr, op.InBounds ctx.raw → op.TreeMonotone ctx

/--
  Every operation of `ctx` that runs its `Interp` semantics is monotone in
  `Interp`, in its operands and its memory, and every other one is monotone in
  CTrees. This also gives what the proof needs of the operations that the
  lowering keeps, and the proof then reasons about the first kind in `Interp`.
-/
@[expose]
def ProvedMonotoneOps (ctx : WfIRContext OpCode) : Prop :=
  ∀ op : OperationPtr, op.InBounds ctx.raw →
    ((op.getOpType! ctx.raw).isLifted → InterpretOp'ContextuallyMonotone (op.getOpType! ctx.raw)) ∧
    ((op.getOpType! ctx.raw).isLifted = false → op.TreeMonotone ctx)

/-- A RISC-V control-flow operation returns the memory it is given, whatever it is. -/
theorem interpretOp'_riscvCf_memory {opType : OpCode} (hType : ∃ c, opType = .riscv_cf c)
    {properties : propertiesOf opType}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {successors : Array BlockPtr}
    {mem mem₁ : MemoryState} {results : Array RuntimeValue} {action : Option ControlFlowAction}
    (h : interpretOp' opType properties resultTypes operands successors mem =
      .ok (results, mem₁, action)) (mem' : MemoryState) :
    interpretOp' opType properties resultTypes operands successors mem' =
      .ok (results, mem', action) := by
  obtain ⟨c, rfl⟩ := hType
  simp only [interpretOp'] at h ⊢
  rcases hc : Riscv_Cf.interpretOp' c properties resultTypes operands successors with
    _ | _ | ⟨values, action'⟩ <;> simp_all [Bind.bind]

/--
  `interpretOp` is monotone, with refined memory, for an operation that a value
  mapping preserves.
-/
theorem interpretOp_contextuallyMonotone_of_preservesOperation
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    {mapping : ValueMapping ctx ctx'} {op op' : OperationPtr}
    (opIn : op.InBounds ctx.raw) (opIn' : op'.InBounds ctx'.raw)
    [inst : InterpretOp'ContextuallyMonotone (op.getOpType! ctx.raw)]
    (hState : state.RefinedUnder (· ⊒ ·) state' mapping)
    (hPreserves : mapping.PreservesOperation op op') :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState ctx' × Option ControlFlowAction) =>
        r₁.1.RefinedUnder (· ⊒ ·) r₂.1 mapping ∧
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
  have hPR1 := inst.monotone (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
    (op.getResultTypes! ctx.raw) operands operands' (op.getSuccessors! ctx.raw) state.memory
    state'.memory hOpsRef hState.1
  have hInterp'Eq : op'.interpret ctx'.raw operands' state'.memory =
                    op.interpret ctx.raw operands' state'.memory := by
     grind [interpretOp'_opType_cast, cases ValueMapping.PreservesOperation]
  simp only [Interp.isRefinedBy_ok_target_iff, Prod.exists]
  have ⟨resValues, hinterp', hResValues⟩ :=
    (interpretOp_ok_iff_of_getOperandValues_eq_some hSrcOps).mp hsrc
  simp only [OperationPtr.interpret] at hinterp' hInterp'Eq
  rw [hinterp'] at hPR1
  simp only [Interp.isRefinedBy_ok_target_iff, Prod.exists] at hPR1
  obtain ⟨resValues', memory'₂, act', hinterp'Tgt, hRel⟩ := hPR1
  obtain ⟨resValuesRef, hMem₂, actRef⟩ := hRel
  rw [← hInterp'Eq] at hinterp'Tgt
  simp only [interpretOp, hTgtOps, Bind.bind, OperationPtr.interpret, hinterp'Tgt, liftM,
    monadLift, MonadLift.monadLift]
  have hConforms : RuntimeValue.ArrayConforms resValues' (op'.getResultTypes! ctx'.raw) := by
    rw [hPreserves.resultTypes]
    exact (RuntimeValue.ArrayConforms_of_setResultValues?_eq_some hResValues).of_isRefinedBy
      resValuesRef
  obtain ⟨variables', hSet', hRefined⟩ := VariableState.setResultValues?_isRefinedBy hState.2
    resValuesRef hPreserves.results hPreserves.reflect hResValues hConforms opIn'
  simp only [hSet', Interp.pure_eq, Interp.withBlame_ok, Interp.ok.injEq]
  exact ⟨_, _, rfl, ⟨hMem₂, hRefined⟩, actRef⟩

namespace BranchLowering

variable (L : BranchLowering ctx ctx')

/-!
## The relations of the proof

They are those of the `Interp` proof, with the memory of the target refining
that of the source instead of equal to it: a value that is poison in the source
may be concrete in the target, and the target may store it.
-/

/-- Two states whose variables refine and whose memories refine. -/
abbrev StateRel (source : InterpreterState ctx) (target : InterpreterState ctx') : Prop :=
  source.RefinedUnder (· ⊒ ·) target L.mapping

/-- How the outcome of a branch relates to the outcome of its lowering. -/
abbrev BranchRelC (source : InterpreterState ctx × Option ControlFlowAction)
    (target : InterpreterState ctx' × Option ControlFlowAction) : Prop :=
  L.StateRel source.1 target.1 ∧
  ∃ values values' dest, source.2 = some (.branch values dest) ∧
    target.2 = some (.branch values' dest) ∧ L.converted dest ∧
    RegistersOf values values'

/-- How the source state after a list of operations relates to the target state. -/
abbrev ListRelC (source : InterpreterState ctx × Option ControlFlowAction)
    (target : InterpreterState ctx' × Option ControlFlowAction) : Prop :=
  L.StateRel source.1 target.1 ∧ L.ActionRel source.2 target.2 ∧ ConstantsHold source.1

/-- The calls of the closed CFG loops of the two modules that correspond to each other. -/
@[expose]
def CallRelC : BlockCallRel ctx ctx' :=
  fun block values state block' values' state' =>
    block' = block ∧ L.StateRel state state' ∧ ConstantsHold state ∧
    if L.converted block then RegistersOf values values'
    else values ⊒ values'

/-- The results of the two modules that correspond to each other. -/
abbrev ResultRelC (source : InterpreterState ctx × Array RuntimeValue)
    (target : InterpreterState ctx' × Array RuntimeValue) : Prop :=
  source.1.memory ⊒ target.1.memory ∧ source.2 ⊒ target.2

/-! ## The casts at the start of a converted block -/

/-- Running the pending casts gives every value of the source its counterpart. -/
theorem returns_entryCasts {block : BlockPtr} (blockIn : block.InBounds ctx.raw)
    (hConverted : L.converted block) {source : InterpreterState ctx} {pending : List Nat}
    (hPending : ∀ i ∈ pending, i < block.getNumArguments! ctx.raw)
    {R : MemoryState → MemoryState → Prop}
    {target : InterpreterState ctx'} (hInv : L.EntryInv R block source target pending) :
    Returns (opListTree (pending.map (fun i => L.argCast (block.getArgument i))) target
        (L.entryCasts_inBounds blockIn hConverted hPending))
      (fun r => r.2 = none ∧ L.EntryInv R block source r.1 []) := by
  induction pending generalizing target with
  | nil =>
    simp only [List.map_nil, opListTree_nil]
    exact returns_pure.mpr ⟨rfl, hInv⟩
  | cons i pending ih =>
    have hi : i < block.getNumArguments! ctx.raw := hPending i (by simp)
    have argIn : (block.getArgument i).InBounds ctx.raw :=
      BlockArgumentPtr.inBounds_def.mpr ⟨blockIn, by grind [BlockPtr.getArgument_def]⟩
    have hSpec := L.argCastSpec argIn hConverted
    obtain ⟨sourceValue, value, reg, hSource, hRefined, hReg, hTarget⟩ := hInv.arguments i hi
    have hFits := (L.argTypeConverted blockIn hConverted hi).2
    have hConforms := VariableState.getVar?_conforms hSource
    obtain ⟨result, hResult, hRefinedResult, hConformsResult⟩ :=
      RuntimeValue.isRefinedBy_ofReg?_of_castsTo hFits (hConforms.of_isRefinedBy hRefined) hReg
    have hRefinedResult := RuntimeValue.isRefinedBy_trans hRefined hRefinedResult
    have hCast := returns_interpretOperationTree_cast (state := target) (Q := (· = result))
      hSpec.1 hSpec.2.2.1 hSpec.2.2.2.1 hSpec.2.2.2.2 hTarget (fun properties successors => by
        rw [interpretOp'_tree_cast_ofReg hResult]
        exact returns_pure.mpr ⟨result, rfl, hConformsResult, rfl⟩)
    simp only [List.map_cons, opListTree_cons, returns_tau1]
    refine hCast.bind ?_
    rintro ⟨target', action⟩ ⟨rfl, hMem, output, hOutput, hGet⟩
    rw [hOutput] at hGet
    simp only [Option.elim_none]
    refine ih (fun j hj => hPending j (by simp [hj])) ?_
    refine ⟨hMem ▸ hInv.memory, fun j hj => ?_, fun v vIn sv hv => ?_⟩
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

/-! ## The two branches -/

/--
  The operations in front of the new branch bind registers of its operands, and
  keep the states related since no value of the source stands for one of them.
-/
theorem returns_regOps {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : op.IsGmirBranch ctx.raw) {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} {R : MemoryState → MemoryState → Prop}
    (hState : state.RefinedUnder R state' L.mapping)
    (hSources : ∀ (i : Nat) (value : ValuePtr),
      (regOperands ctx.raw op (L.compare op))[i]? = some (some value) →
      value.InBounds ctx.raw ∧ ∃ sv, state.variables.getVar? value = some sv ∧
        ∀ tv, sv ⊒ tv → ∃ reg, tv.toReg? = some reg)
    {k : Nat} (hk : k ≤ (regOperands ctx.raw op (L.compare op)).length) :
    Returns (opListTree ((List.range k).map (L.regOp op)) state'
        (L.regOps_inBounds opIn hBranch hk))
      (fun r => r.2 = none ∧ ∃ registers : Array RuntimeValue,
        state.RefinedUnder R r.1 L.mapping ∧ registers.size = k ∧
        (∀ value, value.InBounds ctx.raw →
          r.1.variables.getVar? (L.mapValue value) = state'.variables.getVar? (L.mapValue value)) ∧
        ∀ i, i < k → (∃ source, (regOperands ctx.raw op (L.compare op))[i]? = some source ∧
            L.RegFor state state' source registers[i]!) ∧
          r.1.variables.getVar? ((L.regOp op i).getResult 0) = some registers[i]!) := by
  induction k with
  | zero =>
    simp only [List.range_zero, List.map_nil, opListTree_nil]
    exact returns_pure.mpr ⟨rfl, #[], hState, rfl, fun _ _ => rfl, by simp⟩
  | succ k ih =>
    have hk' : k < (regOperands ctx.raw op (L.compare op)).length := by omega
    have hSpec := L.regOpSpec opIn hBranch hk'
    obtain ⟨source, hSource⟩ := L.regOperands_getElem? hk'
    have hList : (List.range (k + 1)).map (L.regOp op) =
        (List.range k).map (L.regOp op) ++ [L.regOp op k] := by
      simp [List.range_succ]
    rw [opListTree_congr hList, opListTree_append]
    refine (ih (by omega)).bind ?_
    rintro ⟨target, action⟩ ⟨rfl, registers, hTarget, hSize, hSame, hRegisters⟩
    simp only [opListCont, Option.elim_none, opListTree_cons, returns_tau1]
    /- The operation at `k` binds `register`, related to its source as `RegFor` says. -/
    have hOp : Returns (interpretOperationTree (L.regOp op k) target hSpec.1) (fun r =>
        r.2 = none ∧ r.1.memory = target.memory ∧ ∃ register,
          (∀ value, r.1.variables.getVar? value =
            if value = (L.regOp op k).getResult 0 then some register
            else target.variables.getVar? value) ∧
          L.RegFor state state' source register) := by
      rcases source with _ | value
      · obtain ⟨hType, hResultTypes, hOperands⟩ := L.regOpX0 opIn hBranch hSource
        obtain ⟨target', hOk, hMem, hGet⟩ :=
          interpretOperationTree_getRegister (state := target) hSpec.1 hType hResultTypes hOperands
        rw [hOk]
        exact returns_pure.mpr ⟨rfl, hMem, _, hGet, fun _ => rfl, fun _ h => by simp at h⟩
      · obtain ⟨hType, hResultTypes, hOperands⟩ := L.regOpCast opIn hBranch hSource
        obtain ⟨valueIn, sv, hSv, hRegs⟩ := hSources k value hSource
        obtain ⟨tv, hTv, hRefined⟩ := hState.2 value valueIn sv hSv
        simp only [mapping_val] at hTv
        obtain ⟨reg, hReg⟩ := hRegs tv hRefined
        have hTv' : target.variables.getVar? (lowerValue L.converted L.argCast value) = some tv := by
          rw [show lowerValue L.converted L.argCast value = L.mapValue value from rfl,
            hSame value valueIn, hTv]
        refine (returns_interpretOperationTree_cast (state := target)
          (Q := fun output => ∃ reg', tv.CastsTo reg' ∧ output = .reg reg') hSpec.1 hType
          hResultTypes hOperands hTv' (fun properties successors => ?_)).mono ?_
        · exact (returns_cast_toReg hReg properties successors _).mono
            fun r ⟨reg', hCasts, hr⟩ => ⟨.reg reg', ⟨reg', hCasts, rfl⟩, RuntimeValue.reg_conforms, hr⟩
        · rintro r ⟨h₁, h₂, output, ⟨reg', hCasts, rfl⟩, hGet⟩
          refine ⟨h₁, h₂, .reg reg', hGet, fun h => by simp at h, fun value' h => ?_⟩
          obtain rfl := Option.some.inj h
          exact ⟨sv, tv, reg', hSv, hTv, hRefined, hCasts, rfl⟩
    refine hOp.bind ?_
    rintro ⟨target', action'⟩ ⟨rfl, hMem, register, hGet, hReg⟩
    simp only [Option.elim_none, opListTree_nil]
    refine returns_pure.mpr ⟨rfl, registers.push register, ⟨hMem ▸ hTarget.1, ?_⟩,
      by simp [hSize], fun value valueIn => ?_, fun i hi => ?_⟩
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

include L in
/-- The new branch of a branch is a RISC-V branch, whose CTree semantics is its `Interp` one. -/
theorem newBranch_isLifted {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : op.IsGmirBranch ctx.raw) :
    ((L.newBranch op).getOpType! ctx'.raw).isLifted := by
  rcases hBranch with hType | hType
  · rw [(L.newBranchBr opIn hType).2]; rfl
  · rcases hc : L.compare op with _ | ⟨branch, l, r⟩
    · rw [(L.newBranchBnez opIn hType hc).1]; rfl
    · rw [(L.newBranchCompare opIn hc).1]; rfl

include L in
/-- The new branch of a branch is a RISC-V control-flow operation. -/
theorem newBranch_riscvCf {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : op.IsGmirBranch ctx.raw) :
    ∃ c, (L.newBranch op).getOpType! ctx'.raw = .riscv_cf c := by
  rcases hBranch with hType | hType
  · exact ⟨_, (L.newBranchBr opIn hType).2⟩
  · rcases hc : L.compare op with _ | ⟨branch, l, r⟩
    · exact ⟨_, (L.newBranchBnez opIn hType hc).1⟩
    · exact ⟨_, (L.newBranchCompare opIn hc).1⟩

/--
  A branch is refined by the operations that put its registers in front of the
  RISC-V branch, and the source runs it as `interpretOp` does. A
  compare-and-branch needs the `CompareFact` of its `g_icmp`, and the constant it
  may compare with to hold its value.
-/
theorem sim_gmirBranch {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : op.IsGmirBranch ctx.raw) {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} (hState : L.StateRel state state')
    (hConstants : ConstantsHold state)
    (hFact : ∀ c, L.compare op = some c → L.CompareFact op state) :
    Sim (fun t s => L.BranchRelC s t ∧ interpretOp op state opIn = .ok s)
      (opListTree (lowerOp ctx.raw L.compare L.regOp L.newBranch op) state'
        (L.lowerOp_inBounds opIn))
      (interpretOperationTree op state opIn) := by
  have hLifted : (op.getOpType! ctx.raw).isLifted := by
    rcases hBranch with h | h <;> rw [h] <;> rfl
  rw [interpretOperationTree_eq_monadLift state opIn hLifted]
  refine sim_monadLift fun ⟨source₁, action⟩ hsrc => ?_
  obtain ⟨operands, results, mem₁, variables₁, hOperands, hInterp, hSetResults, rfl⟩ :=
    interpretOp_some_iff.mp hsrc
  have hSpec := L.newBranchSpec opIn hBranch
  have hLower : lowerOp ctx.raw L.compare L.regOp L.newBranch op =
      (List.range (regOperands ctx.raw op (L.compare op)).length).map (L.regOp op) ++
        [L.newBranch op] := by
    simp [lowerOp, hBranch]
  rw [opListTree_congr hLower, opListTree_append]
  refine sim_bind_of_returns (L.returns_regOps opIn hBranch hState
    (L.regSources opIn hBranch hOperands hFact) (Nat.le_refl _)) ?_
  rintro ⟨target, action'⟩ ⟨rfl, registers, hTarget, hSize, -, hRegisters⟩
  have hNewOperands := L.getOperandValues_newBranch opIn hBranch hSize
    (fun i hi => (hRegisters i hi).2)
  obtain ⟨values, values', dest, rfl, rfl, rfl, hNewInterp, hValues⟩ :=
    L.interpret_newBranch opIn hBranch hState hConstants hFact hOperands hInterp hSize
      (fun i hi => (hRegisters i hi).1)
  replace hNewInterp : (L.newBranch op).interpret ctx'.raw registers target.memory =
      .ok (#[], target.memory, some (.branch values' dest)) := by
    simp only [OperationPtr.interpret] at hNewInterp ⊢
    exact interpretOp'_riscvCf_memory (L.newBranch_riscvCf opIn hBranch) hNewInterp _
  have hDest : dest ∈ op.getSuccessors! ctx.raw := interpretOp'_branch_dest_mem hInterp
  have hVariables : variables₁ = state.variables := by
    rw [VariableState.setResultValues?_empty (L.branchNumResults opIn hBranch)] at hSetResults
    exact (Option.some.inj hSetResults).symm
  subst hVariables
  have hNewOk : interpretOp (L.newBranch op) target hSpec.1 =
      .ok (target, some (.branch values' dest)) :=
    (interpretOp_ok_iff_of_getOperandValues_eq_some hNewOperands).mpr
      ⟨#[], hNewInterp, VariableState.setResultValues?_empty hSpec.2.1⟩
  simp only [opListCont, Option.elim_none, opListTree_cons, opListTree_nil]
  apply sim_tau1_left
  rw [interpretOperationTree_eq_monadLift target hSpec.1 (L.newBranch_isLifted opIn hBranch),
    hNewOk]
  simp only [monadLift, MonadLift.monadLift, pure_bind, Option.elim_some]
  exact (Sim.pure _ _ _).mpr ⟨⟨hTarget, values, values', dest, rfl, rfl,
    L.branchSuccessorConverted opIn hBranch hDest, hValues⟩, hsrc⟩

/-! ## Blocks -/

/--
  How the outcome of an operation that the lowering keeps relates to its outcome
  in the lowering, with what the rest of the list needs of it.
-/
abbrev KeptRel (ops : List OperationPtr) (target : InterpreterState ctx' × Option ControlFlowAction)
    (source : InterpreterState ctx × Option ControlFlowAction) : Prop :=
  L.StateRel source.1 target.1 ∧
    ControlFlowAction.optionIsRefinedBy source.2 target.2 ∧ ConstantsHold source.1 ∧
    (source.2 = none → L.HeadFact ops source.1) ∧
    ∀ values dest, source.2 ≠ some (.branch values dest)

/--
  What the proof needs of the operations that the lowering keeps: each is
  refined by itself, as `KeptRel` says.
-/
@[expose]
def KeptOpsSim : Prop :=
  ∀ {op : OperationPtr} {ops : List OperationPtr} (opIn : op.InBounds ctx.raw)
    (_ : ∀ op ∈ ops, op.InBounds ctx.raw) (hBranch : ¬ op.IsGmirBranch ctx.raw)
    {state : InterpreterState ctx} {state' : InterpreterState ctx'},
    L.StateRel state state' → ConstantsHold state → L.ComparesAdjacent (op :: ops) →
    Sim (L.KeptRel ops) (interpretOperationTree op state' (L.opSpec opIn hBranch).1)
      (interpretOperationTree op state opIn)

/-- The `g_icmp` of a compare-and-branch that the lowering keeps is the operation right before it. -/
theorem eq_icmpOf_of_comparesAdjacent {op : OperationPtr} {ops : List OperationPtr}
    (hAdjacent : L.ComparesAdjacent (op :: ops)) {op' : OperationPtr} {post : List OperationPtr}
    {c : Compare} (hOps : ops = op' :: post) (hc : L.compare op' = some c) : op = L.icmpOf op' := by
  have hIcmp := hAdjacent [op] op' post c (by simp [hOps]) (by simp) hc
  simpa using hIcmp

/-- What the rest of the list needs of an operation that the lowering keeps, from its run. -/
theorem keptRel_of_interpretOp {op : OperationPtr} {ops : List OperationPtr}
    (opIn : op.InBounds ctx.raw) (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw)
    (hBranch : ¬ op.IsGmirBranch ctx.raw) {state : InterpreterState ctx}
    (hConstants : ConstantsHold state) (hAdjacent : L.ComparesAdjacent (op :: ops))
    {source : InterpreterState ctx × Option ControlFlowAction}
    (hsrc : interpretOp op state opIn = .ok source)
    {target : InterpreterState ctx' × Option ControlFlowAction}
    (hRel : L.StateRel source.1 target.1)
    (hAction : ControlFlowAction.optionIsRefinedBy source.2 target.2) :
    L.KeptRel ops target source := by
  refine ⟨hRel, hAction, hConstants.interpretOp hsrc, fun _ => ?_, fun values dest h => ?_⟩
  · intro op' post c hOps hc
    obtain rfl := L.eq_icmpOf_of_comparesAdjacent hAdjacent hOps hc
    exact L.compareFact_of_interpretOp (opsIn op' (by simp [hOps])) hc hsrc
  · rcases source with ⟨source, action⟩
    simp only at h
    subst h
    have := interpretOp_branch_dest_mem_getSuccessors! hsrc
    simp [(L.opSuccessors opIn hBranch).1] at this

/-- An operation with CTree semantics of its own that the lowering keeps is refined by itself. -/
theorem sim_keptOp_of_isLifted_eq_false {op : OperationPtr} {ops : List OperationPtr}
    (opIn : op.InBounds ctx.raw) (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw)
    (hBranch : ¬ op.IsGmirBranch ctx.raw) (hLifted : (op.getOpType! ctx.raw).isLifted = false)
    (hMono : op.TreeMonotone ctx) {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} (hState : L.StateRel state state')
    (hConstants : ConstantsHold state) (hAdjacent : L.ComparesAdjacent (op :: ops)) :
    Sim (L.KeptRel ops) (interpretOperationTree op state' (L.opSpec opIn hBranch).1)
      (interpretOperationTree op state opIn) := by
  have hSpec := L.opSpec opIn hBranch
  refine sim_mono (interpretOperationTree_sim_of_preservesOperation opIn hSpec.1 hMono
    hState (L.preservesOperation opIn hBranch)) ?_
  rintro ⟨target₁, action'⟩ ⟨source₁, action⟩ ⟨hRel, hAction, ⟨results, hSet⟩, hNone⟩
  obtain rfl := hNone hLifted
  have hNotConstant : op.getOpType! ctx.raw ≠ .gmir .g_constant := by
    intro h; rw [h] at hLifted; exact nomatch hLifted
  refine ⟨hRel, hAction, hConstants.setResultValues? hNotConstant hSet, fun _ => ?_,
    fun _ _ h => nomatch h⟩
  intro op' post c hOps hc
  obtain rfl := L.eq_icmpOf_of_comparesAdjacent hAdjacent hOps hc
  have hType := (L.compareSpec (opsIn op' (by simp [hOps])) hc).2.2.1
  rw [hType] at hLifted
  exact nomatch hLifted

/--
  An operation with lifted `Interp` semantics that the lowering keeps is refined
  by itself, if it is monotone in CTrees. Its source runs its `Interp` semantics,
  whose outcome tells what the rest of the list needs.
-/
theorem sim_keptOp_of_treeMonotone {op : OperationPtr} {ops : List OperationPtr}
    (opIn : op.InBounds ctx.raw) (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw)
    (hBranch : ¬ op.IsGmirBranch ctx.raw) (hLifted : (op.getOpType! ctx.raw).isLifted)
    (hMono : op.TreeMonotone ctx) {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} (hState : L.StateRel state state')
    (hConstants : ConstantsHold state) (hAdjacent : L.ComparesAdjacent (op :: ops)) :
    Sim (L.KeptRel ops) (interpretOperationTree op state' (L.opSpec opIn hBranch).1)
      (interpretOperationTree op state opIn) := by
  have hSpec := L.opSpec opIn hBranch
  have hOp := interpretOperationTree_sim_of_preservesOperation opIn hSpec.1 hMono
    hState (L.preservesOperation opIn hBranch)
  rw [interpretOperationTree_eq_monadLift state opIn hLifted] at hOp ⊢
  refine sim_monadLift fun source hsrc => ?_
  rw [hsrc] at hOp
  refine sim_mono (sim_pure_and hOp (P := fun s => interpretOp op state opIn = .ok s) hsrc) ?_
  rintro target source₂ ⟨⟨hRel, hAction, -⟩, hsrc₂⟩
  exact L.keptRel_of_interpretOp opIn opsIn hBranch hConstants hAdjacent hsrc₂ hRel hAction

/--
  An operation with lifted `Interp` semantics that the lowering keeps is refined
  by itself, if it is monotone in `Interp`.
-/
theorem sim_keptOp_of_contextuallyMonotone {op : OperationPtr} {ops : List OperationPtr}
    (opIn : op.InBounds ctx.raw) (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw)
    (hBranch : ¬ op.IsGmirBranch ctx.raw) (hLifted : (op.getOpType! ctx.raw).isLifted)
    [InterpretOp'ContextuallyMonotone (op.getOpType! ctx.raw)] {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} (hState : L.StateRel state state')
    (hConstants : ConstantsHold state) (hAdjacent : L.ComparesAdjacent (op :: ops)) :
    Sim (L.KeptRel ops) (interpretOperationTree op state' (L.opSpec opIn hBranch).1)
      (interpretOperationTree op state opIn) := by
  have hSpec := L.opSpec opIn hBranch
  have hLifted' : (op.getOpType! ctx'.raw).isLifted := by rw [hSpec.2.1, hLifted]
  rw [interpretOperationTree_eq_monadLift state opIn hLifted,
    interpretOperationTree_eq_monadLift state' hSpec.1 hLifted']
  refine sim_monadLift fun source hsrc => ?_
  have hOp := interpretOp_contextuallyMonotone_of_preservesOperation opIn hSpec.1 hState
    (L.preservesOperation opIn hBranch)
  simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at hOp
  obtain ⟨target, hTarget, hRel, hAction⟩ := hOp
  rw [hTarget]
  exact (Sim.pure _ _ _).mpr
    (L.keptRel_of_interpretOp opIn opsIn hBranch hConstants hAdjacent hsrc hRel hAction)

/-- The operations of a module that are monotone in CTrees are refined by themselves. -/
theorem keptOpsSim_of_treeMonotoneOps (hMono : TreeMonotoneOps ctx) : L.KeptOpsSim := by
  intro op ops opIn opsIn hBranch state state' hState hConstants hAdjacent
  cases hLifted : (op.getOpType! ctx.raw).isLifted
  · exact L.sim_keptOp_of_isLifted_eq_false opIn opsIn hBranch hLifted (hMono _ opIn) hState
      hConstants hAdjacent
  · exact L.sim_keptOp_of_treeMonotone opIn opsIn hBranch hLifted (hMono _ opIn) hState
      hConstants hAdjacent

/-- The operations of a module that are proved monotone are refined by themselves. -/
theorem keptOpsSim_of_provedMonotoneOps (hMono : ProvedMonotoneOps ctx) : L.KeptOpsSim := by
  intro op ops opIn opsIn hBranch state state' hState hConstants hAdjacent
  cases hLifted : (op.getOpType! ctx.raw).isLifted
  · exact L.sim_keptOp_of_isLifted_eq_false opIn opsIn hBranch hLifted
      ((hMono op opIn).2 hLifted) hState hConstants hAdjacent
  · have := (hMono op opIn).1 hLifted
    exact L.sim_keptOp_of_contextuallyMonotone opIn opsIn hBranch hLifted hState
      hConstants hAdjacent

theorem tau1_bind (t : Tree α) (k : α → Tree β) :
    CTree.tau1 t >>= k = CTree.tau1 (t >>= k) := by
  simp [CTree.tau1_def]

/-- A list of operations is refined by its lowering. -/
theorem sim_opList_lowered (hKept : L.KeptOpsSim)
    {ops : List OperationPtr} (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw)
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    (hState : L.StateRel state state') (hConstants : ConstantsHold state)
    (hAdjacent : L.ComparesAdjacent ops) (hHead : L.HeadFact ops state) :
    Sim (fun t s => L.ListRelC s t)
      (opListTree (ops.flatMap (lowerOp ctx.raw L.compare L.regOp L.newBranch)) state'
        (L.flatMap_lowerOp_inBounds opsIn))
      (opListTree ops state opsIn) := by
  induction ops generalizing state state' with
  | nil =>
    simp only [List.flatMap_nil, opListTree_nil]
    exact (Sim.pure _ _ _).mpr ⟨hState, trivial, hConstants⟩
  | cons op ops ih =>
    have opIn := opsIn op (by simp)
    have opsIn' : ∀ op ∈ ops, op.InBounds ctx.raw := fun op' h => opsIn op' (by simp [h])
    have hAdjacent' : L.ComparesAdjacent ops := fun pre op' post c hOps hPre hc => by
      have := hAdjacent (op :: pre) op' post c (by simp [hOps]) (by simp) hc
      cases pre with
      | nil => contradiction
      | cons p pre => simpa [List.getLast?_cons_cons] using this
    rw [opListTree_congr (List.flatMap_cons ..), opListTree_append, opListTree_cons]
    apply sim_tau1_right
    by_cases hBranch : op.IsGmirBranch ctx.raw
    · rw [tree_bind_eq, tree_bind_eq]
      refine Sim.bind _ _ _ _ (L.sim_gmirBranch opIn hBranch hState hConstants
        (fun c hc => hHead op ops c rfl hc)) ?_
      rintro ⟨target₁, action'⟩ ⟨source₁, action⟩
        ⟨⟨hRel, values, values', dest, rfl, rfl, hDest, hValues⟩, hsrc⟩
      simp only [opListCont, Option.elim_some]
      exact (Sim.pure _ _ _).mpr ⟨hRel, ⟨rfl, hDest, hValues⟩, hConstants.interpretOp hsrc⟩
    · have hLower : lowerOp ctx.raw L.compare L.regOp L.newBranch op = [op] := by
        simp [lowerOp, hBranch]
      rw [opListTree_congr hLower, opListTree_cons, tau1_bind]
      apply sim_tau1_left
      rw [CTree.bind_assoc, tree_bind_eq, tree_bind_eq]
      refine Sim.bind _ _ _ _ (hKept opIn opsIn' hBranch hState hConstants
        hAdjacent) ?_
      rintro ⟨target₁, action'⟩ ⟨source₁, action⟩ ⟨hRel, hAction, hConstants₁, hHead₁, hNoBranch⟩
      rcases action with _ | cf
      · obtain rfl : action' = none := by
          cases action' <;> simp_all [ControlFlowAction.optionIsRefinedBy]
        simp only [Option.elim_none, opListTree_nil, pure_bind, opListCont]
        exact ih opsIn' hRel hConstants₁ hAdjacent' (hHead₁ rfl)
      · obtain ⟨cf', rfl, hCf⟩ : ∃ cf', action' = some cf' ∧ cf.isRefinedBy cf' := by
          cases action' <;> simp_all [ControlFlowAction.optionIsRefinedBy]
        simp only [Option.elim_some, pure_bind, opListCont]
        rcases cf with values | ⟨values, dest⟩
        · rcases cf' with values' | _
          · exact (Sim.pure _ _ _).mpr ⟨hRel, hCf, hConstants₁⟩
          · simp [ControlFlowAction.isRefinedBy] at hCf
        · exact (hNoBranch values dest rfl).elim

/--
  The operations of a block after its arguments are set, and after the casts in
  a converted block, are refined by their lowering, and the blocks they branch
  to correspond again.
-/
theorem sim_blockBody (hKept : L.KeptOpsSim)
    {ops : List OperationPtr} (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw)
    {state : InterpreterState ctx} {target : InterpreterState ctx'}
    (hState : L.StateRel state target) (hConstants : ConstantsHold state)
    (hAdjacent : L.ComparesAdjacent ops) (hHead : L.HeadFact ops state) :
    Sim (Sum.LiftRel (EntryRel L.CallRelC) (fun t s => ResultRelC s t))
      (opListTree (ops.flatMap (lowerOp ctx.raw L.compare L.regOp L.newBranch)) target
          (L.flatMap_lowerOp_inBounds opsIn) >>=
        fun r => (r.2.elim fail fun cf => pure (r.1, cf)) >>= finishBlock)
      (opListTree ops state opsIn >>=
        fun r => (r.2.elim fail fun cf => pure (r.1, cf)) >>= finishBlock) := by
  rw [tree_bind_eq, tree_bind_eq]
  refine Sim.bind _ _ _ _ (L.sim_opList_lowered hKept opsIn hState hConstants hAdjacent
    hHead) ?_
  rintro ⟨target₁, action'⟩ ⟨source₁, action⟩ ⟨hRel₁, hAction, hConstants₁⟩
  rcases action with _ | cf
  · simp
  rcases action' with _ | cf'
  · simp [ActionRel] at hAction
  simp only [Option.elim_some, pure_bind]
  rcases cf with res | ⟨res, dest⟩ <;> rcases cf' with res' | ⟨res', dest'⟩ <;>
    simp only [ActionRel] at hAction
  · simp only [finishBlock_return]
    exact (Sim.pure _ _ _).mpr (Sum.LiftRel.inr ⟨hRel₁.1, hAction⟩)
  · obtain ⟨rfl, hDest, hRegisters⟩ := hAction
    simp only [finishBlock_branch]
    by_cases destIn : dest.InBounds ctx.raw
    · simp only [destIn, L.blockIn destIn, ↓reduceDIte]
      exact (Sim.pure _ _ _).mpr (Sum.LiftRel.inl ⟨dest, destIn, res, source₁, dest, L.blockIn destIn, res',
        target₁, rfl, rfl, rfl, hRel₁, hConstants₁, by simp [hDest, hRegisters]⟩)
    · simp only [destIn, ↓reduceDIte]
      exact sim_fail _ _

/-- A block step is refined by its lowering, and the blocks they branch to correspond again. -/
theorem sim_blockStep_lowered (hKept : L.KeptOpsSim)
    {block block' : BlockPtr} {values values' : Array RuntimeValue}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    (blockIn : block.InBounds ctx.raw) (blockIn' : block'.InBounds ctx'.raw)
    (hRel : L.CallRelC block values state block' values' state') :
    Sim (Sum.LiftRel (EntryRel L.CallRelC) (fun t s => ResultRelC s t))
      (blockStep (CFGState.entry blockIn' values' state'))
      (blockStep (CFGState.entry blockIn values state)) := by
  obtain ⟨rfl, hState, hConstants, hValues⟩ := hRel
  have hNum := L.numArguments blockIn
  rw [blockStep_entry, blockStep_entry]
  by_cases hSize : (values.size != block'.getNumArguments ctx.raw) = true
  · simp only [hSize, ↓reduceIte]
    exact sim_fail _ _
  have hSizeEq : values.size = block'.getNumArguments! ctx.raw := by
    rw [BlockPtr.getNumArguments!_eq_getNumArguments blockIn]
    simpa using hSize
  have hSizeEq' : values'.size = values.size := by
    split at hValues
    · exact hValues.size_eq.symm
    · exact hValues.1.symm
  have hSize' : (values'.size != block'.getNumArguments ctx'.raw) = false := by
    rw [← BlockPtr.getNumArguments!_eq_getNumArguments blockIn', hNum]
    simp only [bne_eq_false_iff_eq]
    omega
  simp only [hSize, hSize', Bool.false_eq_true, ↓reduceIte]
  rcases hSet : state.variables.setArgumentValues? block' values blockIn with _ | variables
  · exact sim_fail _ _
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
  have hBody := fun (target : InterpreterState ctx')
      (hTarget : L.StateRel (⟨variables, state.memory⟩ : InterpreterState ctx) target) =>
        L.sim_blockBody hKept
    opsIn hTarget (hConstants.setArgumentValues? hSet) hAdjacent hHead
  by_cases hConverted : L.converted block'
  · simp only [hConverted, ↓reduceIte] at hValues
    obtain ⟨variables', hSet', hInv⟩ :=
      L.entryInv_of_setArgumentValues? blockIn hConverted hState hValues hSet
    simp only [hSet']
    rw [terminatedOpListTree_eq, opListTree_congr (L.operationList blockIn)]
    simp only [hConverted, ↓reduceIte]
    rw [opListTree_append, CTree.bind_assoc, CTree.bind_assoc]
    refine sim_bind_of_returns (L.returns_entryCasts blockIn hConverted (by simp) hInv) ?_
    rintro ⟨target, action⟩ ⟨rfl, hInv'⟩
    simp only [opListCont, Option.elim_none]
    rw [terminatedOpListTree_eq, CTree.bind_assoc]
    exact hBody target (L.isRefinedBy_of_entryInv hInv')
  · have hConverted' : L.converted block' = false := by simpa using hConverted
    simp only [hConverted', Bool.false_eq_true, ↓reduceIte] at hValues
    obtain ⟨variables', hSet', hTarget⟩ :=
      L.setArgumentValues?_other blockIn hConverted' hState hValues hSet
    simp only [hSet']
    rw [terminatedOpListTree_eq, opListTree_congr (L.operationList blockIn)]
    simp only [hConverted', Bool.false_eq_true, ↓reduceIte, List.nil_append]
    rw [terminatedOpListTree_eq, CTree.bind_assoc, CTree.bind_assoc]
    exact hBody _ hTarget

/-! ## Functions and modules -/

/-- The closed CFG loop from a block is refined by that of its lowering. -/
theorem sim_cfg_lowered (hKept : L.KeptOpsSim)
    {block : BlockPtr} {values values' : Array RuntimeValue}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    (blockIn : block.InBounds ctx.raw)
    (hRel : L.CallRelC block values state block values' state') :
    Sim (fun t s => ResultRelC s t)
      (_root_.CTree.iter cfgStep (CFGState.entry (L.blockIn blockIn) values' state'))
      (_root_.CTree.iter cfgStep (CFGState.entry blockIn values state)) :=
  iter_cfgStep_sim
    (fun _ blockIn _ _ _ blockIn' _ _ hRel => L.sim_blockStep_lowered hKept blockIn
      blockIn' hRel)
    blockIn (L.blockIn blockIn) hRel

/-- A function is refined by its lowering. -/
theorem isRefinedByAsFunctionCTree (hKept : L.KeptOpsSim)
    {func : OperationPtr} (funcIn : func.InBounds ctx.raw)
    (hBranch : ¬ func.IsGmirBranch ctx.raw) (hFunc : func.getOpType! ctx.raw = .func .func) :
    func.isRefinedByAsFunctionCTree ctx func ctx' funcIn (L.opSpec funcIn hBranch).1 := by
  have hSpec := L.opSpec funcIn hBranch
  have funcIn' := hSpec.1
  have hFunc' : func.getOpType! ctx'.raw = .func .func := by rw [hSpec.2.1, hFunc]
  have f : FunctionOp ctx.raw func := .of func ctx.raw
    (by unfold OperationPtr.isFunctionLike; rw [hFunc]; rfl)
  have f' : FunctionOp ctx'.raw func := .of func ctx'.raw
    (by unfold OperationPtr.isFunctionLike; rw [hFunc']; rfl)
  rw [OperationPtr.isRefinedByAsFunctionCTree, FunctionOp.of?_eq_some f,
    FunctionOp.of?_eq_some f']
  intro values values' mem hValues
  have hNum : func.getNumRegions ctx'.raw funcIn' = func.getNumRegions ctx.raw funcIn := by
    have := hSpec.2.2.2.2.2.1
    grind
  simp only [CTree.interpretFunction, FunctionOp.of?_eq_some f, FunctionOp.of?_eq_some f', hNum]
  split
  · exact sim_fail _ _
  next hRegions =>
  have hRegions' : 0 < func.getNumRegions ctx.raw funcIn := by omega
  have regionIn : (f.getFunctionBody funcIn hRegions').InBounds ctx.raw := by
    have := ctx.wellFormed.inBounds
    simp only [FunctionOp.getFunctionBody]
    grind
  have hBody : f'.getFunctionBody funcIn' (by omega) = f.getFunctionBody funcIn hRegions' := by
    have := hSpec.2.2.2.2.2.2.1
    simp only [FunctionOp.getFunctionBody]
    grind
  rw [tree_bind_eq, tree_bind_eq]
  refine Sim.bind (RR := fun t s => ResultRelC s t) _ _ _ _ ?_
    (fun ⟨_, results'⟩ ⟨_, results⟩ h => (Sim.pure _ _ _).mpr h.2)
  rw [interpretRegion_eq_inflateCFGTree, interpretRegion_eq_inflateCFGTree]
  apply Sim.interp
  simp only [interpretCFGTree]
  have hFirst := L.firstBlock regionIn
  split
  · next block' hBlock' =>
    split
    · next block hBlock =>
      have blockIn : block.InBounds ctx.raw := by grind
      have hNotConverted := L.entryNotConverted regionIn (block := block) (by grind)
      obtain rfl : block' = block := by grind
      exact L.sim_cfg_lowered hKept (values := values) (values' := values')
        (state := ⟨VariableState.empty ctx, mem⟩) (state' := ⟨VariableState.empty ctx', mem⟩)
        blockIn ⟨rfl, ⟨MemoryState.isRefinedBy_refl _, fun v vIn sv hv => by
          simp [VariableState.empty, VariableState.getVar?] at hv⟩, ConstantsHold.empty,
          by simpa [hNotConverted] using hValues⟩
    · exact sim_fail _ _
  · next hNone' =>
    split
    · next block hBlock => exfalso; grind
    · exact sim_fail _ _

include L in
/-- A module is refined by its branch lowering, in CTrees. -/
theorem isModuleRefinedByCTree (hKept : L.KeptOpsSim)
    (module : OperationPtr) : module.isModuleRefinedByCTree ctx module ctx' := by
  intro func funcIn name hTop
  have hBranch : ¬ func.IsGmirBranch ctx.raw := by
    simp [OperationPtr.IsGmirBranch, hTop.isFunc]
  have hSpec := L.opSpec funcIn hBranch
  refine ⟨func, hSpec.1, ⟨?_, ?_, ?_⟩,
    L.isRefinedByAsFunctionCTree hKept funcIn hBranch hTop.isFunc⟩
  · rw [hSpec.2.1, hTop.isFunc]
  · rw [hSpec.2.2.1]; exact hTop.hasName
  · rw [hSpec.2.2.2.2.2.2.2]; exact hTop.isTopLevel

end BranchLowering

end Veir
