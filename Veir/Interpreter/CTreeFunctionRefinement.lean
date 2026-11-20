module

public import Veir.Interpreter.CTreeStateRefinement
import all Veir.Interpreter.CTreeStateRefinement
public import Veir.Interpreter.CTreeSimulation
public import Veir.Interpreter.CTreePrimitiveRefinement
import all Veir.Interpreter.Lemmas
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.VariableState
import all Veir.Interpreter.CTreeInterpreter
import all Veir.IR.Basic
import all Veir.Interfaces.FunctionInterfaces
import all Veir.GlobalOpInfo
import all Veir.Dialects.Func.OpInfo

public section

namespace Veir

/-- The identity SSA renaming within one context. -/
def ValueMapping.identity (ctx : WfIRContext OpCode) : ValueMapping ctx ctx := id

theorem ValueMapping.identity_preserves (ctx : WfIRContext OpCode)
    (op : OperationPtr) (hop : op.InBounds ctx.raw) :
    (ValueMapping.identity ctx).PreservesOperation op op hop hop := by
  refine {
    opType := rfl
    props := rfl
    resultTypes := rfl
    successors := rfl
    operands := ?_
    results := ?_
    reflect := ?_ }
  · simp [ValueMapping.applyToArray, ValueMapping.identity]
  · simp [ValueMapping.applyToArray, ValueMapping.identity]
  · intro value valueIn i h
    exact h

/-- Refining block arguments can be installed in related variable states. -/
theorem VariableState.setArgumentValues?_isRefinedBy
    {ctx : WfIRContext OpCode} {source target source' : VariableState ctx}
    {block : BlockPtr} {hblock : block.InBounds ctx.raw}
    {sourceValues targetValues : Array RuntimeValue}
    (states : source.isRefinedBy target (ValueMapping.identity ctx))
    (values : RuntimeValue.arrayIsRefinedBy sourceValues targetValues)
    (sourceSet : source.setArgumentValues? block sourceValues hblock = some source') :
    ∃ target', target.setArgumentValues? block targetValues hblock = some target' ∧
      source'.isRefinedBy target' (ValueMapping.identity ctx) := by
  have hsourceSize : sourceValues.size = block.getNumArguments! ctx.raw := by
    unfold VariableState.setArgumentValues? at sourceSet
    split at sourceSet <;> simp_all
  have htargetSize : targetValues.size = block.getNumArguments! ctx.raw := by
    have := values.1
    omega
  have hsourceConforms :=
    (VariableState.setArgumentValues?_isSome_iff_conforms source hsourceSize).mpr ⟨source', sourceSet⟩
  obtain ⟨target', targetSet⟩ :=
    (VariableState.setArgumentValues?_isSome_iff_conforms target htargetSize).mp (by
      intro i hi
      exact (hsourceConforms i hi).of_isRefinedBy (values.2 i (by omega)))
  refine ⟨target', targetSet, ?_⟩
  intro pointer pointerIn sourceValue hvalue
  simp only [ValueMapping.identity, id_eq]
  have hsource := VariableState.getVar?_setArgumentValues? sourceSet (value := pointer)
  have htarget := VariableState.getVar?_setArgumentValues? targetSet (value := pointer)
  cases pointer with
  | opResult result =>
    simp only at hsource htarget
    rw [hsource] at hvalue
    obtain ⟨targetValue, ht, hr⟩ := states _ pointerIn _ hvalue
    exact ⟨targetValue, htarget.trans ht, hr⟩
  | blockArgument argument =>
    rcases argument with ⟨owner, index⟩
    by_cases hset : owner = block ∧ index < block.getNumArguments! ctx.raw
    · obtain ⟨rfl, hi⟩ := hset
      simp only [hi, true_and, ↓reduceIte] at hsource htarget
      rw [hsource] at hvalue
      cases hvalue
      exact ⟨_, htarget, values.2 index (by omega)⟩
    · simp only [hset, ↓reduceIte] at hsource htarget
      rw [hsource] at hvalue
      obtain ⟨targetValue, ht, hr⟩ := states _ pointerIn _ hvalue
      exact ⟨targetValue, htarget.trans ht, hr⟩

namespace CTree

/-- Same CFG location, with refining arguments at block entry and refining state. -/
def CFGStateRefines {ctx : WfIRContext OpCode}
    (target source : interpretCFG.StateLocation ctx × InterpreterState ctx) : Prop :=
  source.2.isRefinedBy target.2 (ValueMapping.identity ctx) ∧
    match target.1, source.1 with
    | .inl (targetBlock, targetValues), .inl (sourceBlock, sourceValues) =>
      targetBlock = sourceBlock ∧ RuntimeValue.arrayIsRefinedBy sourceValues targetValues
    | .inr targetOp, .inr sourceOp => targetOp = sourceOp
    | _, _ => False

/-- Result relation used while comparing two executions of an unchanged region. -/
def CFGResultRefines {ctx : WfIRContext OpCode}
    (target source : InterpreterState ctx × Array RuntimeValue) : Prop :=
  source.1.isRefinedBy target.1 (ValueMapping.identity ctx) ∧
    RuntimeValue.arrayIsRefinedBy source.2 target.2

/-- Refinement of actual operation steps extends to block entry and control-flow dispatch. -/
theorem sim_interpretCFGCore_iter {ctx : WfIRContext OpCode}
    (operations : ∀ (op : OperationPtr) (hop : op.InBounds ctx.raw)
      (target source : InterpreterState ctx),
      source.isRefinedBy target (ValueMapping.identity ctx) →
      _root_.CTree.Sim
        (fun t s => s.1.isRefinedBy t.1 (ValueMapping.identity ctx) ∧
          ControlFlowAction.optionIsRefinedBy s.2 t.2)
        (interpretOpCore op target hop) (interpretOpCore op source hop))
    {target source : interpretCFG.StateLocation ctx × InterpreterState ctx}
    (related : CFGStateRefines target source) :
    _root_.CTree.Sim (Sum.LiftRel CFGStateRefines CFGResultRefines)
      (interpretCFGCore.iter target.1 target.2) (interpretCFGCore.iter source.1 source.2) := by
  rcases target with ⟨targetLocation, targetState⟩
  rcases source with ⟨sourceLocation, sourceState⟩
  rcases related with ⟨states, locations⟩
  cases targetLocation with
  | inl targetEntry =>
    cases sourceLocation with
    | inr => contradiction
    | inl sourceEntry =>
      rcases targetEntry with ⟨targetBlock, targetValues⟩
      rcases sourceEntry with ⟨sourceBlock, sourceValues⟩
      rcases locations with ⟨rfl, values⟩
      rcases targetBlock with ⟨block, blockIn⟩
      by_cases sourceSize : sourceValues.size = block.getNumArguments! ctx.raw
      · have targetSize : targetValues.size = block.getNumArguments! ctx.raw := by
          have := values.1
          omega
        simp only [interpretCFGCore.iter, sourceSize, targetSize,
          BlockPtr.getNumArguments!_eq_getNumArguments blockIn, bne_self_eq_false, Bool.false_eq_true,
          ↓reduceIte]
        cases sourceSet : sourceState.variables.setArgumentValues? block sourceValues blockIn with
        | none =>
          exact sim_fail _ _
        | some sourceVariables =>
          obtain ⟨targetVariables, targetSet, variableRefinement⟩ :=
            VariableState.setArgumentValues?_isRefinedBy states.2 values sourceSet
          simp only [targetSet]
          split
          next nextOp nextEq =>
            apply (_root_.CTree.Sim.pure _ _ _).mpr
            exact .inl ⟨⟨states.1, variableRefinement⟩, rfl⟩
          next missing => exact sim_fail _ _
      · simp only [interpretCFGCore.iter]
        have sourceSize' : (sourceValues.size != block.getNumArguments ctx.raw blockIn) = true := by
          simpa [← BlockPtr.getNumArguments!_eq_getNumArguments blockIn] using sourceSize
        rw [sourceSize']
        simp only [↓reduceIte]
        exact sim_fail _ _
  | inr targetOp =>
    cases sourceLocation with
    | inl => contradiction
    | inr sourceOp =>
      have equal : targetOp = sourceOp := locations
      subst sourceOp
      rcases targetOp with ⟨op, hop⟩
      simp only [interpretCFGCore.iter]
      apply _root_.CTree.Sim.bind _ _ _ _ (operations op hop targetState sourceState states)
      rintro ⟨targetState', targetAction⟩ ⟨sourceState', sourceAction⟩ ⟨states', actions⟩
      cases sourceAction with
      | none =>
        cases targetAction with
        | some => contradiction
        | none =>
          simp only
          split
          next nextOp nextEq =>
            apply (_root_.CTree.Sim.pure _ _ _).mpr
            exact .inl ⟨states', rfl⟩
          next missing => exact sim_fail _ _
      | some sourceAction =>
        cases targetAction with
        | none => contradiction
        | some targetAction =>
          cases sourceAction <;> cases targetAction <;>
            simp only [ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy] at actions
          · apply (_root_.CTree.Sim.pure _ _ _).mpr
            exact .inr ⟨states', actions⟩
          · rcases actions with ⟨rfl, values⟩
            simp only
            split
            next destinationIn =>
              apply (_root_.CTree.Sim.pure _ _ _).mpr
              exact .inl ⟨states', rfl, values⟩
            next destinationOut => exact sim_fail _ _

/-- An unchanged CFG preserves refinement once its actual operation steps do. -/
theorem sim_interpretCFGCore_of_operations {ctx : WfIRContext OpCode}
    (operations : ∀ (op : OperationPtr) (hop : op.InBounds ctx.raw)
      (target source : InterpreterState ctx),
      source.isRefinedBy target (ValueMapping.identity ctx) →
      _root_.CTree.Sim
        (fun t s => s.1.isRefinedBy t.1 (ValueMapping.identity ctx) ∧
          ControlFlowAction.optionIsRefinedBy s.2 t.2)
        (interpretOpCore op target hop) (interpretOpCore op source hop))
    (region : RegionPtr) (regionIn : region.InBounds ctx.raw)
    (targetValues sourceValues : Array RuntimeValue)
    (targetState sourceState : InterpreterState ctx)
    (states : sourceState.isRefinedBy targetState (ValueMapping.identity ctx))
    (values : RuntimeValue.arrayIsRefinedBy sourceValues targetValues) :
    _root_.CTree.Sim CFGResultRefines
      (interpretCFGCore region targetValues targetState regionIn)
      (interpretCFGCore region sourceValues sourceState regionIn) := by
  unfold interpretCFGCore
  split
  next block entry =>
    apply _root_.CTree.Sim.iter
    · exact (show CFGStateRefines _ _ from ⟨states, rfl, values⟩)
    · exact fun _ _ h => sim_interpretCFGCore_iter operations h
  next missing => exact sim_fail _ _

/-- The primitive contract supplies the actual-step obligation in a verified context. -/
theorem sim_interpretOpCore_of_verified
    (primitive : ∀ opType, OpCode.interpretCTree_monotone opType)
    {ctx : WfIRContext OpCode} {root : OperationPtr} (verified : ctx.Verified root)
    (op : OperationPtr) (opIn : op.InBounds ctx.raw)
    (target source : InterpreterState ctx)
    (states : source.isRefinedBy target (ValueMapping.identity ctx)) :
    _root_.CTree.Sim
      (fun t s => s.1.isRefinedBy t.1 (ValueMapping.identity ctx) ∧
        ControlFlowAction.optionIsRefinedBy s.2 t.2)
      (interpretOpCore op target opIn) (interpretOpCore op source opIn) := by
  apply sim_interpretOpCore opIn opIn states (ValueMapping.identity_preserves ctx op opIn)
  intro sourceValues targetValues sourceGet targetGet values
  exact primitive (op.getOpType ctx.raw opIn) ctx op opIn rfl
    (OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants verified opIn)
    sourceValues targetValues source.memory target.memory
    (VariableState.getOperandValues_conforms sourceGet) values states.1

/-- Verified unchanged CFGs preserve refinement under the primitive interpreter contract. -/
theorem sim_interpretCFGCore_of_verified
    (primitive : ∀ opType, OpCode.interpretCTree_monotone opType)
    {ctx : WfIRContext OpCode} {root : OperationPtr} (verified : ctx.Verified root)
    (region : RegionPtr) (regionIn : region.InBounds ctx.raw)
    (targetValues sourceValues : Array RuntimeValue)
    (targetState sourceState : InterpreterState ctx)
    (states : sourceState.isRefinedBy targetState (ValueMapping.identity ctx))
    (values : RuntimeValue.arrayIsRefinedBy sourceValues targetValues) :
    _root_.CTree.Sim CFGResultRefines
      (interpretCFGCore region targetValues targetState regionIn)
      (interpretCFGCore region sourceValues sourceState regionIn) :=
  sim_interpretCFGCore_of_operations (sim_interpretOpCore_of_verified primitive verified)
    region regionIn targetValues sourceValues targetState sourceState states values

/-- The verified CFG result applies to the actual recursive region interpreter. -/
theorem sim_interpretRegion_of_verified
    (primitive : ∀ opType, OpCode.interpretCTree_monotone opType)
    {ctx : WfIRContext OpCode} {root : OperationPtr} (verified : ctx.Verified root)
    (region : RegionPtr) (regionIn : region.InBounds ctx.raw)
    (targetValues sourceValues : Array RuntimeValue)
    (targetState sourceState : InterpreterState ctx)
    (states : sourceState.isRefinedBy targetState (ValueMapping.identity ctx))
    (values : RuntimeValue.arrayIsRefinedBy sourceValues targetValues) :
    _root_.CTree.Sim CFGResultRefines
      (interpretRegion region targetValues targetState regionIn)
      (interpretRegion region sourceValues sourceState regionIn) := by
  have core := sim_interpretCFGCore_of_verified primitive verified region regionIn
    targetValues sourceValues targetState sourceState states values
  have targetNorm := (sim_interpretRegion_core region targetValues targetState regionIn).1
  have sourceNorm := (sim_interpretRegion_core region sourceValues sourceState regionIn).2
  exact _root_.CTree.Sim.trans (_root_.CTree.Sim.trans targetNorm core
    (fun _ _ _ equal related => equal ▸ related)) sourceNorm
    (fun _ _ _ related equal => equal ▸ related)

/-- Verified function execution is monotone in its runtime arguments for any initial memory. -/
theorem sim_interpretFunction_of_verified
    (primitive : ∀ opType, OpCode.interpretCTree_monotone opType)
    {ctx : WfIRContext OpCode} {root : OperationPtr} (verified : ctx.Verified root)
    (op : OperationPtr) (opIn : op.InBounds ctx.raw)
    (targetValues sourceValues : Array RuntimeValue)
    (mem : MemoryState)
    (values : RuntimeValue.arrayIsRefinedBy sourceValues targetValues) :
    _root_.CTree.Sim (fun target source => RuntimeValue.arrayIsRefinedBy source target)
      (interpretFunction op targetValues mem opIn) (interpretFunction op sourceValues mem opIn) := by
  apply sim_interpretFunction opIn opIn targetValues sourceValues mem
  intro function functionEq oneRegion
  refine ⟨function, functionEq, oneRegion, ?_⟩
  apply (sim_interpretRegion_of_verified primitive verified _ _ targetValues sourceValues
    ⟨.empty ctx, mem⟩ ⟨.empty ctx, mem⟩ ?_ values).mono
  · intro target source related
    exact related.2
  · refine ⟨MemoryState.isRefinedBy_refl _, ?_⟩
    exact VariableState.isRefinedBy_refl

end CTree

/-- A verified module refines itself, including when its arguments become more defined. -/
theorem OperationPtr.isModuleRefinedByCTree_refl
    {ctx : WfIRContext OpCode} {root : OperationPtr} (verified : ctx.Verified root)
    (moduleOp : OperationPtr) : moduleOp.isModuleRefinedByCTree ctx moduleOp ctx := by
  intro function functionIn name named
  refine ⟨function, functionIn, named, ?_⟩
  unfold OperationPtr.isRefinedByAsFunctionCTree
  cases view : FunctionOp.of? function ctx.raw with
  | none =>
    have functionLike : (HasOpInfo.functionInterface? (function.getOpType! ctx.raw)).isSome := by
      rw [named.isFunc]
      rfl
    unfold FunctionOp.of? at view
    split at view <;> simp_all
  | some functionView =>
    intro sourceValues targetValues mem values
    exact CTree.sim_interpretFunction_of_verified OpCode.interpretCTree_monotone_assumed
      verified function functionIn targetValues sourceValues mem values

/-- A verified named module function cannot be the regionless operation erased by the driver. -/
theorem OperationPtr.IsTopLevelFuncWithName.ne_regionless
    {ctx : WfIRContext OpCode} {moduleOp function erased : OperationPtr} {name : StringAttr}
    (named : function.IsTopLevelFuncWithName moduleOp ctx.raw name)
    (verified : ctx.Verified moduleOp) (functionIn : function.InBounds ctx.raw)
    (regions : erased.getNumRegions! ctx.raw = 0) : function ≠ erased := by
  intro equal
  subst erased
  have localVerified := OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants verified functionIn
  have count := (OperationPtr.Verified.func_func localVerified named.isFunc).2.2.2
  omega

end Veir
