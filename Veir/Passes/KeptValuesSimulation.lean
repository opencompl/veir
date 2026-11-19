module

public import Veir.Passes.InstructionSelection.Branches.SimulationCTree
public import Veir.Passes.InstructionSelection.Branches.Frame

import Veir.Interpreter.Lemmas
import Veir.Interpreter.Refinement.Lemmas
import all Veir.Interpreter.VariableState
import all Veir.Interpreter.Refinement.Basic
import all Veir.IR.Basic
import all Veir.Interfaces.FunctionInterfaces
import all Veir.GlobalOpInfo
import all Veir.Dialects.Func.OpInfo
import all Veir.Interpreter.CTreeInterpreter

public section

/-!
# Transformations that keep every value refine the module, in CTrees

A transformation that keeps the blocks, the values and their types, and the functions of a module
(`KeptValues`) relates the states of the two runs through the identity on values, by refinement
of the values and the memory. A function of the target is called with arguments that refine those
of the source, so the values of the target refine those of the source rather than equal them.

If the operations of each block simulate those of the block in the source on related states
(`KeptValues.BlockListsSim`), the runs simulate each other block by block on the closed CFG loop,
and the module is refined. This is all the transformation has to show about its blocks: the
translation of the LLVM branches (`Veir.Passes.LLVMToGMIR.BranchSimulation`) replaces a branch by
another, the widening of the branch conditions (`Veir.Passes.Legalization.Validity.Brcond`) by a
`g_zext` and a branch.
-/

open CTree Veir.CTree

namespace Veir

/-- `ctx'` keeps the blocks and regions, the values and their types, and the functions of `ctx`. -/
structure KeptValues (ctx ctx' : WfIRContext OpCode) : Prop where
  /-- The blocks and regions stay. -/
  ctxSame : CtxSame ctx.raw ctx'.raw
  /-- The values and their types stay. -/
  types : ∀ value : ValuePtr, value.InBounds ctx.raw →
    value.InBounds ctx'.raw ∧ value.getType! ctx'.raw = value.getType! ctx.raw
  /-- The functions stay. -/
  funcSame {func : OperationPtr} : func.InBounds ctx.raw → func.getOpType! ctx.raw = .func .func →
    OpSame id ctx.raw ctx'.raw func

variable {ctx ctx' : WfIRContext OpCode}

namespace KeptValues

variable (K : KeptValues ctx ctx')

/-! ## The relations of the proof -/

/-- Every value of the source stands for itself in the target. -/
@[expose]
def mapping : ValueMapping ctx ctx' :=
  fun ⟨value, valueIn⟩ => ⟨value, (K.types value valueIn).1⟩

@[simp] theorem mapping_val {value : ValuePtr} {valueIn : value.InBounds ctx.raw} :
    (K.mapping ⟨value, valueIn⟩).val = value := rfl

theorem applyToArray_mapping {values : Array ValuePtr}
    (valuesIn : ∀ v ∈ values, v.InBounds ctx.raw) :
    K.mapping.applyToArray values valuesIn = values := by
  simp [ValueMapping.applyToArray]

/-- Two states whose variables and memories refine. -/
abbrev StateRel (source : InterpreterState ctx) (target : InterpreterState ctx') : Prop :=
  source.RefinedUnder (· ⊒ ·) target K.mapping

/-- How the outcomes of an operation and of what stands for it relate. -/
abbrev OpRel (target : InterpreterState ctx' × Option ControlFlowAction)
    (source : InterpreterState ctx × Option ControlFlowAction) : Prop :=
  K.StateRel source.1 target.1 ∧ ControlFlowAction.optionIsRefinedBy source.2 target.2

/--
  What the transformation has to show about its blocks: on related states, the operations of a
  block in the target simulate those of the block in the source.
-/
@[expose]
def BlockListsSim : Prop :=
  ∀ {block : BlockPtr} (blockIn : block.InBounds ctx.raw) (blockIn' : block.InBounds ctx'.raw)
    {state : InterpreterState ctx} {state' : InterpreterState ctx'},
    K.StateRel state state' →
    EqSim K.OpRel
      (opListTree (block.operationList ctx'.raw ctx'.wellFormed blockIn').toList state'
        (by grind [BlockPtr.operationListWF, BlockPtr.OpChain]))
      (opListTree (block.operationList ctx.raw ctx.wellFormed blockIn).toList state
        (by grind [BlockPtr.operationListWF, BlockPtr.OpChain]))

/-! ## Blocks -/

/-- The calls of the closed CFG loops of the two modules that correspond to each other. -/
@[expose]
def CallRel : BlockCallRel ctx ctx' :=
  fun block values state block' values' state' =>
    block' = block ∧ values ⊒ values' ∧ K.StateRel state state'

/-- The results of the two modules that correspond to each other. -/
abbrev ResultRel (source : CFGResult ctx) (target : CFGResult ctx') : Prop :=
  source.1.memory ⊒ target.1.memory ∧ source.2 ⊒ target.2

include K

/-- A block with the same arguments sets refined values on refined states. -/
theorem setArgumentValues? {block : BlockPtr} (blockIn : block.InBounds ctx.raw)
    {blockIn' : block.InBounds ctx'.raw} {state : InterpreterState ctx}
    {state' : InterpreterState ctx'} (hState : K.StateRel state state')
    {values values' : Array RuntimeValue} (hValues : values ⊒ values')
    {variables : VariableState ctx}
    (hSet : state.variables.setArgumentValues? block values blockIn = some variables) :
    ∃ variables',
      state'.variables.setArgumentValues? block values' blockIn' = some variables' ∧
      K.StateRel ⟨variables, state.memory⟩ ⟨variables', state'.memory⟩ := by
  have hNum := K.ctxSame.numArguments blockIn
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
    rw [(K.types _ (by grind)).2]
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

/-- A block step is refined by its transformation, and the blocks they branch to correspond again. -/
theorem sim_blockStep (hLists : K.BlockListsSim) {block : BlockPtr} (blockIn : block.InBounds ctx.raw)
    {blockIn' : block.InBounds ctx'.raw} {values values' : Array RuntimeValue}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    (hValues : values ⊒ values') (hState : K.StateRel state state') :
    EqSim (Sum.LiftRel (EntryRel K.CallRel) (fun t s => ResultRel s t))
      (blockStep (CFGState.entry blockIn' values' state'))
      (blockStep (CFGState.entry blockIn values state)) := by
  have hNum := K.ctxSame.numArguments blockIn
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
  obtain ⟨variables', hSet', hRel⟩ := K.setArgumentValues? blockIn (blockIn' := blockIn')
    hState hValues hSet
  simp only [hSet']
  rw [terminatedOpListTree_eq, terminatedOpListTree_eq, tree_bind_eq, tree_bind_eq, tree_bind_eq,
    tree_bind_eq]
  refine EqSim.bind (RR := fun (t : InterpreterState ctx' × ControlFlowAction)
      (s : InterpreterState ctx × ControlFlowAction) => K.StateRel s.1 t.1 ∧ s.2 ⊒ t.2) _ _ _ _
    (EqSim.bind _ _ _ _ (hLists blockIn blockIn' (state := ⟨variables, state.memory⟩)
      (state' := ⟨variables', state'.memory⟩) hRel) ?_) ?_
  · rintro ⟨target, action'⟩ ⟨source, action⟩ ⟨hRel, hAction⟩
    rcases action with _ | cf <;> rcases action' with _ | cf' <;>
      simp only [ControlFlowAction.optionIsRefinedBy] at hAction
    · exact sim_fail _ _
    · exact (EqSim.pure _ _ _).mpr ⟨hRel, hAction⟩
  · rintro ⟨target, cf'⟩ ⟨source, cf⟩ ⟨hRel, hCf⟩
    rcases cf with results | ⟨args, dest⟩ <;> rcases cf' with results' | ⟨args', dest'⟩ <;>
      simp only [ControlFlowAction.isRefinedBy] at hCf
    · simp only [finishBlock_return]
      exact (EqSim.pure _ _ _).mpr (Sum.LiftRel.inr ⟨hRel.1, hCf⟩)
    · obtain ⟨rfl, hArgs⟩ := hCf
      simp only [finishBlock_branch]
      by_cases destIn : dest.InBounds ctx.raw
      · simp only [destIn, K.ctxSame.blockIn destIn, ↓reduceDIte]
        exact (EqSim.pure _ _ _).mpr (Sum.LiftRel.inl ⟨dest, destIn, args, source, dest,
          K.ctxSame.blockIn destIn, args', target, rfl, rfl, rfl, hArgs, hRel⟩)
      · simp only [destIn, ↓reduceDIte]
        exact sim_fail _ _

/-- The closed CFG loop from a block is refined by that of its transformation. -/
theorem sim_cfg (hLists : K.BlockListsSim) {block : BlockPtr} (blockIn : block.InBounds ctx.raw)
    {blockIn' : block.InBounds ctx'.raw} {values values' : Array RuntimeValue}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    (hValues : values ⊒ values') (hState : K.StateRel state state') :
    EqSim (fun t s => ResultRel s t)
      (_root_.CTree.iter cfgStep (CFGState.entry blockIn' values' state'))
      (_root_.CTree.iter cfgStep (CFGState.entry blockIn values state)) :=
  iter_cfgStep_sim (Rel := K.CallRel)
    (fun _ blockIn _ _ _ _ _ _ hRel => by
      obtain ⟨rfl, hValues, hState⟩ := hRel
      exact K.sim_blockStep hLists blockIn hValues hState)
    blockIn blockIn' ⟨rfl, hValues, hState⟩

/-! ## Functions and modules -/

/-- A function is refined by its transformation. -/
theorem isRefinedByAsFunctionCTree (hLists : K.BlockListsSim) {func : OperationPtr}
    (funcIn : func.InBounds ctx.raw) (hFunc : func.getOpType! ctx.raw = .func .func)
    {funcIn' : func.InBounds ctx'.raw} :
    func.isRefinedByAsFunctionCTree ctx func ctx' funcIn funcIn' := by
  have hSame := K.funcSame funcIn hFunc
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
  refine EqSim.bind (RR := fun t s => ResultRel s t) _ _ _ _ ?_
    (fun ⟨_, results'⟩ ⟨_, results⟩ h => (EqSim.pure _ _ _).mpr h.2)
  rw [interpretRegion_eq_inflateCFGTree, interpretRegion_eq_inflateCFGTree]
  apply EqSim.interp
  simp only [interpretCFGTree]
  have hFirst := K.ctxSame.firstBlock regionIn
  split
  · next block' hBlock' =>
    split
    · next block hBlock =>
      have blockIn : block.InBounds ctx.raw := by grind
      obtain rfl : block' = block := by grind
      exact K.sim_cfg hLists blockIn (state := ⟨VariableState.empty ctx, mem⟩)
        (state' := ⟨VariableState.empty ctx', mem⟩) hValues
        ⟨MemoryState.isRefinedBy_refl _, fun v vIn sv hv => by
          simp [VariableState.empty, VariableState.getVar?] at hv⟩
    · exact sim_fail _ _
  · next hNone' =>
    split
    · next block hBlock => exfalso; grind
    · exact sim_fail _ _

/-- A top-level function of the source is one of the transformation. -/
theorem isTopLevelFuncWithName {func module : OperationPtr} {name : StringAttr}
    (funcIn : func.InBounds ctx.raw) (hTop : func.IsTopLevelFuncWithName module ctx.raw name) :
    func.IsTopLevelFuncWithName module ctx'.raw name := by
  have hSame := K.funcSame funcIn hTop.isFunc
  refine ⟨?_, ?_, ?_⟩
  · rw [hSame.opType, hTop.isFunc]
  · rw [hSame.properties]; exact hTop.hasName
  · rw [hSame.getParentOp! K.ctxSame funcIn]; exact hTop.isTopLevel

/-- A module is refined by its transformation, in CTrees. -/
theorem isModuleRefinedByCTree (hLists : K.BlockListsSim) (module : OperationPtr) :
    module.isModuleRefinedByCTree ctx module ctx' := by
  intro func funcIn name hTop
  exact ⟨func, (K.funcSame funcIn hTop.isFunc).inBounds,
    K.isTopLevelFuncWithName funcIn hTop, K.isRefinedByAsFunctionCTree hLists funcIn hTop.isFunc⟩

end KeptValues

end Veir
