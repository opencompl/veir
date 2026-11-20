module

public import Veir.Passes.LLVMToGMIR.BranchSpec
public import Veir.Passes.InstructionSelection.Branches.SimulationCTree
public import Veir.Passes.KeptValuesSimulation

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

The translation keeps every value and its type (`KeptValues`), so it only has
to show that the operations of each block simulate those of the source
(`Veir.Passes.KeptValuesSimulation` lifts that to the module).

An operation that the translation keeps is then refined by itself if it is
monotone (`KeptOpsSim`), and a gMIR branch branches where its LLVM branch does,
with refined operands, whenever that one is defined: a refined condition that
is not poison is the condition, and a `g_brcond` takes its first successor on a
nonzero condition, an `llvm.cond_br` on an `i1` that is one.
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

include T

/-! ## The relations of the proof -/

/-- The translation keeps every value: it only replaces branches. -/
theorem keptValues : KeptValues ctx ctx' :=
  ⟨T.ctxSame, T.types, fun funcIn hFunc =>
    T.opSame funcIn (by simp [OperationPtr.IsLLVMBranch, hFunc])⟩

/-- Every value of the source stands for itself in the target. -/
abbrev mapping : ValueMapping ctx ctx' := T.keptValues.mapping

@[simp] theorem mapping_val {value : ValuePtr} {valueIn : value.InBounds ctx.raw} :
    (T.mapping ⟨value, valueIn⟩).val = value := rfl

theorem applyToArray_mapping {values : Array ValuePtr}
    (valuesIn : ∀ v ∈ values, v.InBounds ctx.raw) :
    T.mapping.applyToArray values valuesIn = values :=
  T.keptValues.applyToArray_mapping valuesIn

/-- Two states whose variables and memories refine. -/
abbrev StateRel := T.keptValues.StateRel

/-- How the outcomes of an operation and of its translation relate. -/
abbrev OpRel := T.keptValues.OpRel


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

/-- The blocks of the translation simulate those of the source. -/
theorem blockListsSim (hKept : T.KeptOpsSim) : T.keptValues.BlockListsSim := by
  intro block blockIn blockIn' state state' hState
  have hList := T.opList blockIn
  simp only [BlockPtr.opList] at hList
  rw [opListTree_congr hList]
  exact T.sim_opList hKept _ _ hState

/-- A module is refined by its branch translation, in CTrees. -/
theorem isModuleRefinedByCTree (hKept : T.KeptOpsSim) (module : OperationPtr) :
    module.isModuleRefinedByCTree ctx module ctx' :=
  T.keptValues.isModuleRefinedByCTree (T.blockListsSim hKept) module

end LLVMBranchTranslation

end Veir
