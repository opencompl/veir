module

public import Veir.Passes.LLVMToGMIR.BranchSpec
public import Veir.Passes.InstructionSelection.Branches.SimulationCTree

import Veir.Interpreter.Lemmas
import Veir.Interpreter.Refinement.Lemmas
import Veir.Interpreter.Refinement.Monotonicity
import Veir.Dialects.LLVM.Lemmas
import Veir.Dialects.GMIR.Lemmas
import all Veir.Interpreter.VariableState
import all Veir.Interpreter.Refinement.Basic
import all Veir.IR.Basic
import all Veir.Interfaces.FunctionInterfaces
import all Veir.GlobalOpInfo
import all Veir.Dialects.Func.OpInfo
import all Veir.Interpreter.CTreeInterpreter

public section

/-!
# The branch translation refines the module, in CTrees

The translation keeps every value and its type, so the states of the two runs
are related by refinement of the values and the memory, through the identity on
values. A function of the target is called with arguments that refine those of
the source, so the values of the target refine those of the source rather than
equal them.

An operation that the translation keeps is then refined by itself if it is
monotone (`KeptOpsSim`), and a gMIR branch branches where its LLVM branch does,
with refined operands, whenever that one is defined: a refined condition that
is not poison is the condition, and a `g_brcond` takes its first successor on a
nonzero condition, an `llvm.cond_br` on an `i1` that is one. The runs simulate
each other block by block on the closed CFG loop.
-/

open CTree Veir.CTree

namespace Veir

/-! ## The two branches -/

/--
  A `g_br` on refined operands branches where an `llvm.br` with the same successors
  does, with the refined operands, and returns the memory it is given.
-/
theorem interpretOp'_gmir_g_br_of_llvm_br {properties : propertiesOf (OpCode.llvm .br)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {successors : Array BlockPtr}
    {mem mem' : MemoryState} {results : Array RuntimeValue} {action : Option ControlFlowAction}
    (h : Veir.interpretOp' (.llvm .br) properties resultTypes operands successors mem =
      .ok (results, mem', action))
    {operands' : Array RuntimeValue} (hOperands : operands ⊒ operands')
    (properties' : propertiesOf (OpCode.gmir .g_br)) (resultTypes' : Array TypeAttr)
    (memT : MemoryState) :
    results = #[] ∧ mem' = mem ∧ ∃ action',
      Veir.interpretOp' (.gmir .g_br) properties' resultTypes' operands' successors memT =
        .ok (#[], memT, action') ∧ ControlFlowAction.optionIsRefinedBy action action' := by
  obtain ⟨dest, rfl, rfl, rfl, rfl⟩ := interpretOp'_llvm_br_eq_ok_iff.mp h
  exact ⟨rfl, rfl, _, interpretOp'_gmir_g_br_eq_ok_iff.mpr ⟨dest, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, hOperands⟩⟩

/--
  A `g_brcond` on refined operands, with the operand segments of an
  `llvm.cond_br` and the same successors, branches where it does, with the
  refined operands: a refined condition that is not poison is the condition, and
  on an `i1`, not zero is one.
-/
theorem interpretOp'_gmir_g_brcond_of_llvm_cond_br
    {properties : propertiesOf (OpCode.llvm .cond_br)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {successors : Array BlockPtr}
    {mem mem' : MemoryState} {results : Array RuntimeValue} {action : Option ControlFlowAction}
    (h : Veir.interpretOp' (.llvm .cond_br) properties resultTypes operands successors mem =
      .ok (results, mem', action))
    {operands' : Array RuntimeValue} (hOperands : operands ⊒ operands')
    (properties' : propertiesOf (OpCode.gmir .g_brcond)) (resultTypes' : Array TypeAttr)
    (hSegments : properties'.operandSegmentSizes = properties.operandSegmentSizes)
    (memT : MemoryState) :
    results = #[] ∧ mem' = mem ∧ ∃ action',
      Veir.interpretOp' (.gmir .g_brcond) properties' resultTypes' operands' successors memT =
        .ok (#[], memT, action') ∧ ControlFlowAction.optionIsRefinedBy action action' := by
  obtain ⟨destTrue, destFalse, cond, n, rfl, hCond, hN, rfl, rfl, rfl⟩ :=
    interpretOp'_llvm_cond_br_eq_ok_iff.mp h
  obtain ⟨h0, hCond⟩ := Array.getElem?_eq_some_iff.mp hCond
  have hRefined := hOperands.2 0 h0
  rw [getElem!_pos operands 0 h0, hCond, RuntimeValue.int_val_isRefinedBy_iff] at hRefined
  have h0' : 0 < operands'.size := hOperands.1 ▸ h0
  have hCond' : operands'[0]? = some (.int 1 (.val cond)) := by
    rw [Array.getElem?_eq_getElem h0', ← getElem!_pos operands' 0 h0', hRefined]
  refine ⟨rfl, rfl, _, interpretOp'_gmir_g_brcond_eq_ok_iff.mpr
    ⟨destTrue, destFalse, 1, cond, n, rfl, hCond', by rw [hSegments]; exact hN, rfl, rfl, rfl⟩,
    ?_⟩
  rcases (by bv_omega : cond = 0#1 ∨ cond = 1#1) with rfl | rfl
  · simpa [ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy] using
      RuntimeValue.arrayIsRefinedBy_extract_size hOperands _
  · simpa [ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy] using
      RuntimeValue.arrayIsRefinedBy_extract hOperands _ _

variable {ctx ctx' : WfIRContext OpCode}

/-- An LLVM branch is an operation whose CTree semantics is its `Interp` one. -/
theorem isLifted_of_isLLVMBranch {op : OperationPtr} (hBranch : op.IsLLVMBranch ctx.raw) :
    (op.getOpType! ctx.raw).isLifted := by
  rcases hBranch with h | h <;> rw [h] <;> rfl

theorem interpretOperationTree_congr {op op' : OperationPtr} (h : op = op')
    {state : InterpreterState ctx} {opIn : op.InBounds ctx.raw} {opIn' : op'.InBounds ctx.raw} :
    interpretOperationTree op state opIn = interpretOperationTree op' state opIn' := by
  subst h; rfl

namespace LLVMBranchTranslation

variable (T : LLVMBranchTranslation ctx ctx')

/-! ## The relations of the proof -/

/-- Every value of the source stands for itself in the target. -/
@[expose]
def mapping : ValueMapping ctx ctx' :=
  fun ⟨value, valueIn⟩ => ⟨value, (T.types value valueIn).1⟩

@[simp] theorem mapping_val {value : ValuePtr} {valueIn : value.InBounds ctx.raw} :
    (T.mapping ⟨value, valueIn⟩).val = value := rfl

theorem applyToArray_mapping {values : Array ValuePtr}
    (valuesIn : ∀ v ∈ values, v.InBounds ctx.raw) :
    T.mapping.applyToArray values valuesIn = values := by
  simp [ValueMapping.applyToArray]

/-- Two states whose variables and memories refine. -/
abbrev StateRel (source : InterpreterState ctx) (target : InterpreterState ctx') : Prop :=
  source.RefinedUnder (· ⊒ ·) target T.mapping

/-- How the outcomes of an operation and of its translation relate. -/
abbrev OpRel (target : InterpreterState ctx' × Option ControlFlowAction)
    (source : InterpreterState ctx × Option ControlFlowAction) : Prop :=
  T.StateRel source.1 target.1 ∧ ControlFlowAction.optionIsRefinedBy source.2 target.2

include T

/-- An operation other than the two branches is the same operation in the translation. -/
theorem preservesOperation {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : ¬ op.IsLLVMBranch ctx.raw) :
    T.mapping.PreservesOperation op op opIn (T.opSame opIn hBranch).inBounds := by
  have hSame := T.opSame opIn hBranch
  have hNum : op.getNumResults! ctx'.raw = op.getNumResults! ctx.raw := by
    rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, hSame.resultTypes,
      OperationPtr.getResultTypes!.size_eq_getNumResults!]
  refine ⟨hSame.opType, ?_, hSame.resultTypes, hSame.successors, ?_, ?_, ?_⟩
  · rw [hSame.properties]
    exact OperationPtr.getProperties!_cast hSame.opType
  · rw [T.applyToArray_mapping, hSame.operands]; simp
  · rw [T.applyToArray_mapping]; simp [OperationPtr.getResults!, hNum]
  · intro value valueIn i h
    simpa using h

/-! ## Single operations -/

/--
  What the proof needs of the operations that the translation keeps: each is
  refined by itself on refined states.
-/
@[expose]
def KeptOpsSim : Prop :=
  ∀ {op : OperationPtr} (opIn : op.InBounds ctx.raw) (hBranch : ¬ op.IsLLVMBranch ctx.raw)
    {state : InterpreterState ctx} {state' : InterpreterState ctx'},
    T.StateRel state state' →
    Sim T.OpRel (interpretOperationTree op state' (T.opSame opIn hBranch).inBounds)
      (interpretOperationTree op state opIn)

/-- The operations of a module that are monotone in CTrees are refined by themselves. -/
theorem keptOpsSim_of_treeMonotoneOps (hMono : TreeMonotoneOps ctx) : T.KeptOpsSim :=
  fun opIn hBranch _ _ hState => sim_mono
    (interpretOperationTree_sim_of_preservesOperation opIn _ (hMono _ opIn) hState
      (T.preservesOperation opIn hBranch)) fun _ _ h => ⟨h.1, h.2.1⟩

/-- The operations of a module that are proved monotone are refined by themselves. -/
theorem keptOpsSim_of_provedMonotoneOps (hMono : ProvedMonotoneOps ctx) : T.KeptOpsSim := by
  intro op opIn hBranch state state' hState
  have hSame := T.opSame opIn hBranch
  cases hLifted : (op.getOpType! ctx.raw).isLifted
  · exact sim_mono (interpretOperationTree_sim_of_preservesOperation opIn _
      ((hMono op opIn).2 hLifted) hState (T.preservesOperation opIn hBranch))
      fun _ _ h => ⟨h.1, h.2.1⟩
  · have := (hMono op opIn).1 hLifted
    have hLifted' : (op.getOpType! ctx'.raw).isLifted := by rw [hSame.opType, hLifted]
    rw [interpretOperationTree_eq_monadLift state opIn hLifted,
      interpretOperationTree_eq_monadLift state' _ hLifted']
    refine sim_monadLift fun source hsrc => ?_
    have hOp := interpretOp_contextuallyMonotone_of_preservesOperation opIn hSame.inBounds hState
      (T.preservesOperation opIn hBranch)
    simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at hOp
    obtain ⟨target, hTarget, hRel, hAction⟩ := hOp
    rw [hTarget]
    exact (Sim.pure _ _ _).mpr ⟨hRel, hAction⟩

/--
  The gMIR branch of an LLVM branch runs as the branch does, where the branch is
  defined, on refined operands.
-/
theorem interpretOp_newBranch {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : op.IsLLVMBranch ctx.raw) {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} (hState : T.StateRel state state')
    {source : InterpreterState ctx} {action : Option ControlFlowAction}
    (hsrc : Veir.interpretOp op state opIn = .ok (source, action)) :
    ∃ target action', Veir.interpretOp (T.newBranch op) state' (T.newBranchSpec opIn hBranch).1 =
      .ok (target, action') ∧ T.StateRel source target ∧
      ControlFlowAction.optionIsRefinedBy action action' := by
  obtain ⟨operands, results, mem, variables, hOperands, hInterp, hSet, rfl⟩ :=
    interpretOp_some_iff.mp hsrc
  obtain ⟨newIn, hResultTypes, hNewOperands, hSuccessors⟩ := T.newBranchSpec opIn hBranch
  obtain ⟨operands', hOperands', hRefined⟩ := VariableState.getOperandValues_isRefinedBy
    hState.2 opIn (op' := T.newBranch op) (by rw [T.applyToArray_mapping, hNewOperands])
    hOperands
  have hRun : results = #[] ∧ mem = state.memory ∧ ∃ action',
      (T.newBranch op).interpret ctx'.raw operands' state'.memory =
        .ok (#[], state'.memory, action') ∧
      ControlFlowAction.optionIsRefinedBy action action' := by
    simp only [OperationPtr.interpret] at hInterp ⊢
    rw [hResultTypes, hSuccessors]
    rcases hBranch with hType | hType
    · rw [T.newBr opIn hType]
      rw [hType] at hInterp
      exact interpretOp'_gmir_g_br_of_llvm_br hInterp hRefined _ _ _
    · obtain ⟨hNewType, hSegments⟩ := T.newBrCond opIn hType
      rw [hNewType]
      rw [hType] at hInterp
      exact interpretOp'_gmir_g_brcond_of_llvm_cond_br hInterp hRefined _ _ hSegments _
  obtain ⟨rfl, rfl, action', hRun, hAction⟩ := hRun
  have hNum : (T.newBranch op).getNumResults! ctx'.raw = 0 := by
    rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, hResultTypes]; rfl
  have hVariables : state.variables = variables := by
    have h :=
      (VariableState.setResultValues?_isSome_iff_conforms state.variables opIn).mpr ⟨_, hSet⟩
    have hNum₀ : op.getNumResults! ctx.raw = 0 := by
      rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, ← h.1]; rfl
    rw [VariableState.setResultValues?_empty hNum₀] at hSet
    exact Option.some.inj hSet
  subst hVariables
  exact ⟨⟨state'.variables, state'.memory⟩, action',
    (interpretOp_ok_iff_of_getOperandValues_eq_some hOperands').mpr
      ⟨#[], hRun, VariableState.setResultValues?_empty hNum⟩, hState, hAction⟩

/-- The gMIR branch of an LLVM branch is refined by it, in CTrees. -/
theorem sim_newBranch {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hBranch : op.IsLLVMBranch ctx.raw) {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} (hState : T.StateRel state state') :
    Sim T.OpRel (interpretOperationTree (T.newBranch op) state' (T.newBranchSpec opIn hBranch).1)
      (interpretOperationTree op state opIn) := by
  have hLifted' : ((T.newBranch op).getOpType! ctx'.raw).isLifted := by
    rcases hBranch with hType | hType
    · rw [T.newBr opIn hType]; rfl
    · rw [(T.newBrCond opIn hType).1]; rfl
  rw [interpretOperationTree_eq_monadLift state opIn (isLifted_of_isLLVMBranch hBranch),
    interpretOperationTree_eq_monadLift state' _ hLifted']
  refine sim_monadLift fun ⟨source, action⟩ hsrc => ?_
  obtain ⟨target, action', hTarget, hRel, hAction⟩ :=
    T.interpretOp_newBranch opIn hBranch hState hsrc
  rw [hTarget]
  exact (Sim.pure _ _ _).mpr ⟨hRel, hAction⟩

theorem translateOp_inBounds {op : OperationPtr} (opIn : op.InBounds ctx.raw) :
    (translateOp ctx.raw T.newBranch op).InBounds ctx'.raw := by
  by_cases hBranch : op.IsLLVMBranch ctx.raw
  · simpa [translateOp, hBranch] using (T.newBranchSpec opIn hBranch).1
  · simpa [translateOp, hBranch] using (T.opSame opIn hBranch).inBounds

/-- Every operation is refined by the one that stands for it, in CTrees. -/
theorem sim_translateOp (hKept : T.KeptOpsSim) {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    {opIn' : (translateOp ctx.raw T.newBranch op).InBounds ctx'.raw}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    (hState : T.StateRel state state') :
    Sim T.OpRel (interpretOperationTree (translateOp ctx.raw T.newBranch op) state' opIn')
      (interpretOperationTree op state opIn) := by
  by_cases hBranch : op.IsLLVMBranch ctx.raw
  · rw [interpretOperationTree_congr (op' := T.newBranch op) (by simp [translateOp, hBranch])
      (opIn' := (T.newBranchSpec opIn hBranch).1)]
    exact T.sim_newBranch opIn hBranch hState
  · rw [interpretOperationTree_congr (op' := op) (by simp [translateOp, hBranch])
      (opIn' := (T.opSame opIn hBranch).inBounds)]
    exact hKept opIn hBranch hState

/-! ## Blocks -/

/-- A list of operations is refined by its translation. -/
theorem sim_opList (hKept : T.KeptOpsSim) : ∀ {ops : List OperationPtr}
    (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw)
    (opsIn' : ∀ op ∈ ops.map (translateOp ctx.raw T.newBranch), op.InBounds ctx'.raw)
    {state : InterpreterState ctx} {state' : InterpreterState ctx'},
    T.StateRel state state' →
    Sim T.OpRel (opListTree (ops.map (translateOp ctx.raw T.newBranch)) state' opsIn')
      (opListTree ops state opsIn)
  | [], _, _, _, _, hState => by
    simp only [List.map_nil, opListTree_nil]
    exact (Sim.pure _ _ _).mpr ⟨hState, trivial⟩
  | op :: ops, opsIn, opsIn', state, state', hState => by
    rw [opListTree_congr (List.map_cons ..), opListTree_cons, opListTree_cons]
    apply sim_tau1_left
    apply sim_tau1_right
    rw [tree_bind_eq, tree_bind_eq]
    refine Sim.bind _ _ _ _ (T.sim_translateOp hKept (opsIn op (by simp)) hState) ?_
    rintro ⟨target, action'⟩ ⟨source, action⟩ ⟨hRel, hAction⟩
    rcases action with _ | cf <;> rcases action' with _ | cf' <;>
      simp only [ControlFlowAction.optionIsRefinedBy] at hAction
    · exact sim_opList hKept _ _ hRel
    · exact (Sim.pure _ _ _).mpr ⟨hRel, hAction⟩

/-- The calls of the closed CFG loops of the two modules that correspond to each other. -/
@[expose]
def CallRel : BlockCallRel ctx ctx' :=
  fun block values state block' values' state' =>
    block' = block ∧ values ⊒ values' ∧ T.StateRel state state'

/-- The results of the two modules that correspond to each other. -/
abbrev ResultRel (source : CFGResult ctx) (target : CFGResult ctx') : Prop :=
  source.1.memory ⊒ target.1.memory ∧ source.2 ⊒ target.2

/-- A block with the same arguments sets refined values on refined states. -/
theorem setArgumentValues? {block : BlockPtr} (blockIn : block.InBounds ctx.raw)
    {blockIn' : block.InBounds ctx'.raw} {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} (hState : T.StateRel state state')
    {values values' : Array RuntimeValue} (hValues : values ⊒ values')
    {variables : VariableState ctx}
    (hSet : state.variables.setArgumentValues? block values blockIn = some variables) :
    ∃ variables',
      state'.variables.setArgumentValues? block values' blockIn' = some variables' ∧
      T.StateRel ⟨variables, state.memory⟩ ⟨variables', state'.memory⟩ := by
  have hNum := T.ctxSame.numArguments blockIn
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
      state'.variables (blockInBounds := blockIn') (values := values')
      (by rw [hNum, ← hValues.1, hSizeEq])).mp (by
    intro j hj
    rw [hNum] at hj
    rw [(T.types _ (by grind)).2]
    exact (hSourceConforms j hj).of_isRefinedBy (hRefined j))
  refine ⟨variables', hSet', hState.1, fun v vIn sv hv => ?_⟩
  simp only [mapping_val]
  by_cases hMem : v ∈ block.getArguments! ctx.raw
  · obtain ⟨i, hi, rfl⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp hMem
    rw [VariableState.getVar?_getArgument_of_setArgumentValues? hi hSet] at hv
    rw [VariableState.getVar?_getArgument_of_setArgumentValues? (by rw [hNum]; exact hi) hSet']
    exact ⟨_, rfl, by simpa using (Option.some.inj hv) ▸ hRefined i⟩
  · rw [VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! hMem hSet] at hv
    obtain ⟨tv, hTv, hRef⟩ := hState.2 v vIn sv hv
    refine ⟨tv, ?_, hRef⟩
    rw [VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! ?_ hSet']
    · simpa using hTv
    · intro hMem'
      obtain ⟨j, hj, hEq⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp hMem'
      exact hMem (BlockPtr.getArguments!.mem_iff_exists_index.mpr
        ⟨j, by rw [← hNum]; exact hj, hEq⟩)

/-- A block step is refined by its translation, and the blocks they branch to correspond again. -/
theorem sim_blockStep (hKept : T.KeptOpsSim) {block : BlockPtr} (blockIn : block.InBounds ctx.raw)
    {blockIn' : block.InBounds ctx'.raw} {values values' : Array RuntimeValue}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    (hValues : values ⊒ values') (hState : T.StateRel state state') :
    Sim (Sum.LiftRel (EntryRel T.CallRel) (fun t s => ResultRel s t))
      (blockStep (CFGState.entry blockIn' values' state'))
      (blockStep (CFGState.entry blockIn values state)) := by
  have hNum := T.ctxSame.numArguments blockIn
  rw [blockStep_entry, blockStep_entry]
  by_cases hSize : (values.size != block.getNumArguments ctx.raw) = true
  · simp only [hSize, ↓reduceIte]
    exact sim_fail _ _
  have hSize' : (values'.size != block.getNumArguments ctx'.raw) = false := by
    rw [← BlockPtr.getNumArguments!_eq_getNumArguments blockIn', hNum,
      BlockPtr.getNumArguments!_eq_getNumArguments blockIn, ← hValues.1]
    simpa using hSize
  simp only [hSize, hSize', Bool.false_eq_true, ↓reduceIte]
  rcases hSet : state.variables.setArgumentValues? block values blockIn with _ | variables
  · exact sim_fail _ _
  obtain ⟨variables', hSet', hRel⟩ := T.setArgumentValues? blockIn (blockIn' := blockIn')
    hState hValues hSet
  simp only [hSet']
  have hList := T.opList blockIn
  simp only [BlockPtr.opList] at hList
  rw [terminatedOpListTree_eq, terminatedOpListTree_eq, opListTree_congr hList, tree_bind_eq,
    tree_bind_eq, tree_bind_eq, tree_bind_eq]
  refine Sim.bind (RR := fun (t : InterpreterState ctx' × ControlFlowAction)
      (s : InterpreterState ctx × ControlFlowAction) => T.StateRel s.1 t.1 ∧ s.2 ⊒ t.2) _ _ _ _
    (Sim.bind _ _ _ _ (T.sim_opList hKept _ _ (state := ⟨variables, state.memory⟩)
      (state' := ⟨variables', state'.memory⟩) hRel) ?_) ?_
  · rintro ⟨target, action'⟩ ⟨source, action⟩ ⟨hRel, hAction⟩
    rcases action with _ | cf <;> rcases action' with _ | cf' <;>
      simp only [ControlFlowAction.optionIsRefinedBy] at hAction
    · exact sim_fail _ _
    · exact (Sim.pure _ _ _).mpr ⟨hRel, hAction⟩
  · rintro ⟨target, cf'⟩ ⟨source, cf⟩ ⟨hRel, hCf⟩
    rcases cf with results | ⟨args, dest⟩ <;> rcases cf' with results' | ⟨args', dest'⟩ <;>
      simp only [ControlFlowAction.isRefinedBy] at hCf
    · simp only [finishBlock_return]
      exact (Sim.pure _ _ _).mpr (Sum.LiftRel.inr ⟨hRel.1, hCf⟩)
    · obtain ⟨rfl, hArgs⟩ := hCf
      simp only [finishBlock_branch]
      by_cases destIn : dest.InBounds ctx.raw
      · simp only [destIn, T.ctxSame.blockIn destIn, ↓reduceDIte]
        exact (Sim.pure _ _ _).mpr (Sum.LiftRel.inl ⟨dest, destIn, args, source, dest,
          T.ctxSame.blockIn destIn, args', target, rfl, rfl, rfl, hArgs, hRel⟩)
      · simp only [destIn, ↓reduceDIte]
        exact sim_fail _ _

/-- The closed CFG loop from a block is refined by that of its translation. -/
theorem sim_cfg (hKept : T.KeptOpsSim) {block : BlockPtr} (blockIn : block.InBounds ctx.raw)
    {blockIn' : block.InBounds ctx'.raw} {values values' : Array RuntimeValue}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    (hValues : values ⊒ values') (hState : T.StateRel state state') :
    Sim (fun t s => ResultRel s t)
      (_root_.CTree.iter cfgStep (CFGState.entry blockIn' values' state'))
      (_root_.CTree.iter cfgStep (CFGState.entry blockIn values state)) :=
  iter_cfgStep_sim (Rel := T.CallRel)
    (fun _ blockIn _ _ _ _ _ _ hRel => by
      obtain ⟨rfl, hValues, hState⟩ := hRel
      exact T.sim_blockStep hKept blockIn hValues hState)
    blockIn blockIn' ⟨rfl, hValues, hState⟩

/-! ## Functions and modules -/

/-- A function is refined by its translation. -/
theorem isRefinedByAsFunctionCTree (hKept : T.KeptOpsSim) {func : OperationPtr}
    (funcIn : func.InBounds ctx.raw) (hFunc : func.getOpType! ctx.raw = .func .func)
    {funcIn' : func.InBounds ctx'.raw} :
    func.isRefinedByAsFunctionCTree ctx func ctx' funcIn funcIn' := by
  have hBranch : ¬ func.IsLLVMBranch ctx.raw := by
    simp [OperationPtr.IsLLVMBranch, hFunc]
  have hSame := T.opSame funcIn hBranch
  have hFunc' : func.getOpType! ctx'.raw = .func .func := by rw [hSame.opType, hFunc]
  have f : FunctionOp ctx.raw func := .of func ctx.raw
    (by unfold OperationPtr.isFunctionLike; rw [hFunc]; rfl)
  have f' : FunctionOp ctx'.raw func := .of func ctx'.raw
    (by unfold OperationPtr.isFunctionLike; rw [hFunc']; rfl)
  rw [OperationPtr.isRefinedByAsFunctionCTree, FunctionOp.of?_eq_some f,
    FunctionOp.of?_eq_some f']
  intro values values' mem hValues
  have hNum : func.getNumRegions ctx'.raw funcIn' = func.getNumRegions ctx.raw funcIn := by
    have := hSame.numRegions
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
    have := hSame.region 0
    simp only [FunctionOp.getFunctionBody]
    grind
  rw [tree_bind_eq, tree_bind_eq]
  refine Sim.bind (RR := fun t s => ResultRel s t) _ _ _ _ ?_
    (fun ⟨_, results'⟩ ⟨_, results⟩ h => (Sim.pure _ _ _).mpr h.2)
  rw [interpretRegion_eq_inflateCFGTree, interpretRegion_eq_inflateCFGTree]
  apply Sim.interp
  simp only [interpretCFGTree]
  have hFirst := T.ctxSame.firstBlock regionIn
  split
  · next block' hBlock' =>
    split
    · next block hBlock =>
      have blockIn : block.InBounds ctx.raw := by grind
      obtain rfl : block' = block := by grind
      exact T.sim_cfg hKept blockIn (state := ⟨VariableState.empty ctx, mem⟩)
        (state' := ⟨VariableState.empty ctx', mem⟩) hValues
        ⟨MemoryState.isRefinedBy_refl _, fun v vIn sv hv => by
          simp [VariableState.empty, VariableState.getVar?] at hv⟩
    · exact sim_fail _ _
  · next hNone' =>
    split
    · next block hBlock => exfalso; grind
    · exact sim_fail _ _

/-- A top-level function of the source is one of the translation. -/
theorem isTopLevelFuncWithName {func module : OperationPtr} {name : StringAttr}
    (funcIn : func.InBounds ctx.raw) (hTop : func.IsTopLevelFuncWithName module ctx.raw name) :
    func.IsTopLevelFuncWithName module ctx'.raw name := by
  have hBranch : ¬ func.IsLLVMBranch ctx.raw := by
    simp [OperationPtr.IsLLVMBranch, hTop.isFunc]
  have hSame := T.opSame funcIn hBranch
  refine ⟨?_, ?_, ?_⟩
  · rw [hSame.opType, hTop.isFunc]
  · rw [hSame.properties]; exact hTop.hasName
  · rw [hSame.getParentOp! T.ctxSame funcIn]; exact hTop.isTopLevel

/-- A module is refined by its branch translation, in CTrees. -/
theorem isModuleRefinedByCTree (hKept : T.KeptOpsSim) (module : OperationPtr) :
    module.isModuleRefinedByCTree ctx module ctx' := by
  intro func funcIn name hTop
  have hBranch : ¬ func.IsLLVMBranch ctx.raw := by
    simp [OperationPtr.IsLLVMBranch, hTop.isFunc]
  exact ⟨func, (T.opSame funcIn hBranch).inBounds, T.isTopLevelFuncWithName funcIn hTop,
    T.isRefinedByAsFunctionCTree hKept funcIn hTop.isFunc⟩

end LLVMBranchTranslation

end Veir
