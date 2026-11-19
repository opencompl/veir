module
public import Veir.Interpreter.CTreeFunctionRefinement
public import Veir.Interpreter.CTreeControlFlow
import all Veir.PatternRewriter.Puddle.CTreeSurvivingBranch
import all Veir.Interpreter.CTreeStateRefinement
import all Veir.Interpreter.CTreeFunctionRefinement
import all Veir.Interpreter.VariableState
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.CTreeInterpreter
import all Veir.IR.Basic
import all Veir.Dominance.Basic

public section
namespace Veir.CTree

/-- Same-pointer refinement does not require a total mapping for deleted,
unexecuted SSA slots: only pointers actually held by the source state are related. -/
def PointerVariableRefines {sourceCtx targetCtx : WfIRContext OpCode}
    (source : VariableState sourceCtx) (target : VariableState targetCtx) : Prop :=
  ∀ pointer sourceValue, source.getVar? pointer = some sourceValue →
    ∃ targetValue, target.getVar? pointer = some targetValue ∧ sourceValue ⊒ targetValue

def PointerStateRefines {sourceCtx targetCtx : WfIRContext OpCode}
    (source : InterpreterState sourceCtx) (target : InterpreterState targetCtx) : Prop :=
  source.memory.isRefinedBy target.memory ∧ PointerVariableRefines source.variables target.variables

/-- Concrete metadata required at an instruction retained in both contexts. -/
structure PointerOperationFrame {sourceCtx targetCtx : WfIRContext OpCode}
    (op : OperationPtr) : Prop where
  opcode : op.getOpType! targetCtx.raw = op.getOpType! sourceCtx.raw
  properties : ∀ code : OpCode, op.getProperties! targetCtx.raw code = op.getProperties! sourceCtx.raw code
  resultTypes : op.getResultTypes! targetCtx.raw = op.getResultTypes! sourceCtx.raw
  operands : op.getOperands! targetCtx.raw = op.getOperands! sourceCtx.raw
  successors : op.getSuccessors! targetCtx.raw = op.getSuccessors! sourceCtx.raw
  next : op.getNextOp! targetCtx.raw = op.getNextOp! sourceCtx.raw
  parent : op.getParent! targetCtx.raw = op.getParent! sourceCtx.raw

private theorem primitive_eq {sourceCtx targetCtx : WfIRContext OpCode}
    (op : OperationPtr) (sourceIn : op.InBounds sourceCtx.raw) (targetIn : op.InBounds targetCtx.raw)
    (frame : PointerOperationFrame (sourceCtx := sourceCtx) (targetCtx := targetCtx) op)
    (values : Array RuntimeValue) (memory : MemoryState) :
    OperationPtr.interpretCTree op targetIn values memory = OperationPtr.interpretCTree op sourceIn values memory := by
  unfold OperationPtr.interpretCTree
  have sourceCode := OperationPtr.getOpType!_eq_getOpType sourceIn
  have sourceProps := OperationPtr.getProperties!_eq_getProperties sourceIn
    (opCode := op.getOpType sourceCtx.raw sourceIn)
    (by simpa only [ofDialect_hasDialectRefl] using sourceCode)
  have targetCode := OperationPtr.getOpType!_eq_getOpType targetIn
  have targetProps := OperationPtr.getProperties!_eq_getProperties targetIn
    (opCode := op.getOpType targetCtx.raw targetIn)
    (by simpa only [ofDialect_hasDialectRefl] using targetCode)
  simp only [← sourceProps, ← targetProps,
    ← OperationPtr.getResultTypes!_eq_getResultTypes sourceIn,
    ← OperationPtr.getResultTypes!_eq_getResultTypes targetIn,
    ← OperationPtr.getSuccessors!_eq_getSuccessors sourceIn,
    ← OperationPtr.getSuccessors!_eq_getSuccessors targetIn]
  rw [← sourceCode, ← targetCode, frame.opcode, frame.properties, frame.resultTypes, frame.successors]
  rfl

private theorem pointer_results_refine
    {sourceCtx targetCtx : WfIRContext OpCode} {op : OperationPtr}
    {source sourceAfter : VariableState sourceCtx} {target targetAfter : VariableState targetCtx}
    (sourceIn : op.InBounds sourceCtx.raw) (targetIn : op.InBounds targetCtx.raw)
    (pointers : op.getResults! targetCtx.raw = op.getResults! sourceCtx.raw)
    (related : PointerVariableRefines source target)
    {sourceValues targetValues : Array RuntimeValue} (values : sourceValues ⊒ targetValues)
    (sourceSet : source.setResultValues? op sourceValues sourceIn = some sourceAfter)
    (targetSet : target.setResultValues? op targetValues targetIn = some targetAfter) :
    PointerVariableRefines sourceAfter targetAfter := by
  intro pointer sourceValue lookup
  by_cases member : pointer ∈ op.getResults! sourceCtx.raw
  · obtain ⟨index, bound, equal⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp member
    have sourceLookup := VariableState.getVar?_getResult_of_setResultValues? bound sourceSet
    have targetBound : index < op.getNumResults! targetCtx.raw := by
      have := congrArg Array.size pointers
      grind
    have targetLookup := VariableState.getVar?_getResult_of_setResultValues? targetBound targetSet
    have sourceSize := VariableState.setResultValues?.getNumRseults!_eq_size sourceSet
    exact ⟨targetValues[index]!, by grind, by grind [RuntimeValue.arrayIsRefinedBy]⟩
  · have targetNotMember : pointer ∉ op.getResults! targetCtx.raw := by simpa only [pointers] using member
    rw [VariableState.getVar?_setResultValues?_of_notMem_getResults! member sourceSet] at lookup
    obtain ⟨targetValue, targetLookup, refined⟩ := related pointer sourceValue lookup
    exact ⟨targetValue,
      (VariableState.getVar?_setResultValues?_of_notMem_getResults! targetNotMember targetSet).trans targetLookup,
      refined⟩

private theorem pointer_operandValues
    {sourceCtx targetCtx : WfIRContext OpCode} {op : OperationPtr}
    {source : VariableState sourceCtx} {target : VariableState targetCtx}
    (same : op.getOperands! targetCtx.raw = op.getOperands! sourceCtx.raw)
    (related : PointerVariableRefines source target)
    {sourceValues : Array RuntimeValue} (sourceGet : source.getOperandValues op = some sourceValues) :
    ∃ targetValues, target.getOperandValues op = some targetValues ∧ sourceValues ⊒ targetValues := by
  have available : ∃ values, (op.getOperands! sourceCtx.raw).mapM target.getVar? = some values := by
    apply Array.exists_mapM_option_eq_some_iff.mpr
    intro index indexIn
    have lookup := Array.mapM_option_eq_some_implies sourceGet index (by grind [VariableState.getOperandValues])
    obtain ⟨value, get, _⟩ := related _ _ lookup
    exact ⟨value, get⟩
  obtain ⟨targetValues, targetGet⟩ := available
  refine ⟨targetValues, ?_, ?_⟩
  · simpa only [VariableState.getOperandValues, same] using targetGet
  · constructor
    · grind [VariableState.getOperandValues]
    · intro index indexIn
      have sourceLookup := Array.mapM_option_eq_some_implies sourceGet index (by grind [VariableState.getOperandValues])
      have targetLookup := Array.mapM_option_eq_some_implies targetGet index (by grind [VariableState.getOperandValues])
      obtain ⟨value, get, refined⟩ := related _ _ sourceLookup
      grind

/-- Verified retained instructions preserve the direct pointer relation across contexts. -/
theorem sim_interpretOpCore_pointer
    (primitive : ∀ opType, OpCode.interpretCTree_monotone opType)
    {sourceCtx targetCtx : WfIRContext OpCode} (op : OperationPtr)
    (sourceIn : op.InBounds sourceCtx.raw) (targetIn : op.InBounds targetCtx.raw)
    (verified : op.Verified sourceCtx sourceIn)
    (frame : PointerOperationFrame (sourceCtx := sourceCtx) (targetCtx := targetCtx) op)
    (source : InterpreterState sourceCtx) (target : InterpreterState targetCtx)
    (related : PointerStateRefines source target) :
    _root_.CTree.Sim (fun t s => PointerStateRefines s.1 t.1 ∧ ControlFlowAction.optionIsRefinedBy s.2 t.2)
      (interpretOpCore op target targetIn) (interpretOpCore op source sourceIn) := by
  cases sourceGet : source.variables.getOperandValues op with
  | none =>
    simp only [interpretOpCore, runOpWith, sourceGet]
    exact sim_fail _ _
  | some sourceValues =>
    obtain ⟨targetValues, targetGet, values⟩ := pointer_operandValues frame.operands related.2 sourceGet
    simp only [interpretOpCore, runOpWith, sourceGet, targetGet]
    have raw := primitive (op.getOpType sourceCtx.raw sourceIn) sourceCtx op sourceIn rfl
      verified sourceValues targetValues source.memory target.memory
      (VariableState.getOperandValues_conforms sourceGet) values related.1
    rw [← primitive_eq op sourceIn targetIn frame targetValues target.memory] at raw
    apply _root_.CTree.Sim.bind _ _ _ _ raw
    intro targetResult sourceResult resultRelation
    cases sourceSet : source.variables.setResultValues? op sourceResult.1 sourceIn with
    | none =>
      simp only [commitOpResults, sourceSet]
      exact sim_fail _ _
    | some sourceVariables =>
      have targetConforms : RuntimeValue.ArrayConforms targetResult.1 (op.getResultTypes! targetCtx.raw) := by
        simpa only [frame.resultTypes] using resultRelation.2
      obtain ⟨targetVariables, targetSet⟩ :=
        (VariableState.setResultValues?_isSome_iff_conforms target.variables targetIn).mp targetConforms
      have pointers : op.getResults! targetCtx.raw = op.getResults! sourceCtx.raw := by
        have counts := congrArg Array.size frame.resultTypes
        grind [OperationPtr.getResults!]
      have variables := pointer_results_refine sourceIn targetIn pointers related.2 resultRelation.1.1 sourceSet targetSet
      simp only [commitOpResults, sourceSet, targetSet, _root_.CTree.Sim.pure]
      exact ⟨⟨resultRelation.1.2.1, variables⟩, resultRelation.1.2.2⟩

/-- Only source-reachable instructions and blocks must be retained. In particular,
unreachable erased SSA definitions need no target pointer image. -/
structure ReachableContextFrame (sourceCtx targetCtx : WfIRContext OpCode) (moduleOp : OperationPtr) : Prop where
  operation : ∀ (op : OperationPtr) (region : RegionPtr), op.InBounds sourceCtx.raw → op.getParentRegion! sourceCtx.raw = some region → op.RootedAt moduleOp sourceCtx → op.HierarchicallyReachable sourceCtx →
    op.InBounds targetCtx.raw ∧ PointerOperationFrame (sourceCtx := sourceCtx) (targetCtx := targetCtx) op
  block : ∀ (block : BlockPtr), block.InBounds sourceCtx.raw → block.RootedAt moduleOp sourceCtx → block.HierarchicallyReachable sourceCtx →
    block.InBounds targetCtx.raw ∧
    block.getArgumentTypes! targetCtx.raw = block.getArgumentTypes! sourceCtx.raw ∧
    block.getFirstOp! targetCtx.raw = block.getFirstOp! sourceCtx.raw

private theorem pointer_arguments_refine
    {sourceCtx targetCtx : WfIRContext OpCode} {block : BlockPtr}
    {source sourceAfter : VariableState sourceCtx} {target : VariableState targetCtx}
    (sourceIn : block.InBounds sourceCtx.raw) (targetIn : block.InBounds targetCtx.raw)
    (types : block.getArgumentTypes! targetCtx.raw = block.getArgumentTypes! sourceCtx.raw)
    (related : PointerVariableRefines source target)
    {sourceValues targetValues : Array RuntimeValue} (values : sourceValues ⊒ targetValues)
    (sourceSet : source.setArgumentValues? block sourceValues sourceIn = some sourceAfter) :
    ∃ targetAfter, target.setArgumentValues? block targetValues targetIn = some targetAfter ∧
      PointerVariableRefines sourceAfter targetAfter := by
  have sourceSize : sourceValues.size = block.getNumArguments! sourceCtx.raw := by
    unfold VariableState.setArgumentValues? at sourceSet
    split at sourceSet <;> simp_all
  have counts : block.getNumArguments! targetCtx.raw = block.getNumArguments! sourceCtx.raw := by
    have size := congrArg Array.size types
    simpa only [BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] using size
  have targetSize : targetValues.size = block.getNumArguments! targetCtx.raw := by
    have := values.1
    omega
  have sourceConforms :=
    (VariableState.setArgumentValues?_isSome_iff_conforms source sourceSize).mpr ⟨sourceAfter, sourceSet⟩
  obtain ⟨targetAfter, targetSet⟩ :=
    (VariableState.setArgumentValues?_isSome_iff_conforms target targetSize).mp (by
      intro index bound
      have sourceBound : index < block.getNumArguments! sourceCtx.raw := by omega
      have conforms := (sourceConforms index sourceBound).of_isRefinedBy (values.2 index (by omega))
      have typeEq : (block.getArgument index : ValuePtr).getType! targetCtx.raw =
          (block.getArgument index : ValuePtr).getType! sourceCtx.raw := by
        have same := congrArg (fun types : Array TypeAttr => types[index]!) types
        simpa only [BlockPtr.getArgumentTypes!.getElem!_eq_getArgument (by omega : index < block.getNumArguments! targetCtx.raw),
          BlockPtr.getArgumentTypes!.getElem!_eq_getArgument sourceBound, ValuePtr.getType!] using same
      simpa only [typeEq] using conforms)
  refine ⟨targetAfter, targetSet, ?_⟩
  intro pointer sourceValue lookup
  have sourceLookup := VariableState.getVar?_setArgumentValues? sourceSet (value := pointer)
  have targetLookup := VariableState.getVar?_setArgumentValues? targetSet (value := pointer)
  cases pointer with
  | opResult result =>
    simp only at sourceLookup targetLookup
    rw [sourceLookup] at lookup
    obtain ⟨targetValue, targetGet, refined⟩ := related _ _ lookup
    exact ⟨targetValue, targetLookup.trans targetGet, refined⟩
  | blockArgument argument =>
    rcases argument with ⟨owner, index⟩
    by_cases installed : owner = block ∧ index < block.getNumArguments! sourceCtx.raw
    · obtain ⟨rfl, bound⟩ := installed
      simp only [counts, bound, true_and, ↓reduceIte] at sourceLookup targetLookup
      rw [sourceLookup] at lookup
      cases lookup
      exact ⟨_, targetLookup, values.2 index (by omega)⟩
    · simp only [counts, installed, ↓reduceIte] at sourceLookup targetLookup
      rw [sourceLookup] at lookup
      obtain ⟨targetValue, targetGet, refined⟩ := related _ _ lookup
      exact ⟨targetValue, targetLookup.trans targetGet, refined⟩

/-- The invariant records only source control locations that execution can visit. -/
def ReachableLocation {sourceCtx targetCtx : WfIRContext OpCode}
    (moduleOp : OperationPtr) (region : RegionPtr)
    (target : interpretCFG.StateLocation targetCtx) (source : interpretCFG.StateLocation sourceCtx) : Prop :=
  match target, source with
  | .inl (targetBlock, targetValues), .inl (sourceBlock, sourceValues) =>
    targetBlock.val = sourceBlock.val ∧ sourceValues ⊒ targetValues ∧
    sourceBlock.val.getParent! sourceCtx.raw = some region ∧
    sourceBlock.val.RootedAt moduleOp sourceCtx ∧ sourceBlock.val.HierarchicallyReachable sourceCtx
  | .inr targetOp, .inr sourceOp =>
    targetOp.val = sourceOp.val ∧ sourceOp.val.getParentRegion! sourceCtx.raw = some region ∧
    sourceOp.val.RootedAt moduleOp sourceCtx ∧ sourceOp.val.HierarchicallyReachable sourceCtx
  | _, _ => False

def ReachableCFGStateRefines {sourceCtx targetCtx : WfIRContext OpCode}
    (moduleOp : OperationPtr) (region : RegionPtr)
    (target : interpretCFG.StateLocation targetCtx × InterpreterState targetCtx)
    (source : interpretCFG.StateLocation sourceCtx × InterpreterState sourceCtx) : Prop :=
  PointerStateRefines source.2 target.2 ∧ ReachableLocation moduleOp region target.1 source.1

def PointerCFGResultRefines {sourceCtx targetCtx : WfIRContext OpCode}
    (target : InterpreterState targetCtx × Array RuntimeValue)
    (source : InterpreterState sourceCtx × Array RuntimeValue) : Prop :=
  PointerStateRefines source.1 target.1 ∧ source.2 ⊒ target.2

private theorem reachable_first {ctx : WfIRContext OpCode} {moduleOp : OperationPtr}
    {region : RegionPtr} {block : BlockPtr} {op : OperationPtr}
    (blockIn : block.InBounds ctx.raw) (parent : block.getParent! ctx.raw = some region)
    (rooted : block.RootedAt moduleOp ctx) (reachable : block.HierarchicallyReachable ctx)
    (first : block.getFirstOp! ctx.raw = some op) :
    op.getParentRegion! ctx.raw = some region ∧ op.RootedAt moduleOp ctx ∧ op.HierarchicallyReachable ctx := by
  have opParent : op.getParent! ctx.raw = some block := by grind
  exact ⟨by grind, rooted.of_parent (by grind), .of_parent_block reachable opParent⟩

private theorem reachable_next {ctx : WfIRContext OpCode} {moduleOp : OperationPtr}
    {region : RegionPtr} {op next : OperationPtr}
    (opIn : op.InBounds ctx.raw) (parent : op.getParentRegion! ctx.raw = some region)
    (rooted : op.RootedAt moduleOp ctx) (reachable : op.HierarchicallyReachable ctx)
    (nextEq : op.getNextOp! ctx.raw = some next) :
    next.getParentRegion! ctx.raw = some region ∧ next.RootedAt moduleOp ctx ∧ next.HierarchicallyReachable ctx := by
  have attached : ∃ block, op.getParent! ctx.raw = some block := by grind [OperationPtr.getParentRegion!]
  obtain ⟨block, opParent⟩ := attached
  have nextParent : next.getParent! ctx.raw = some block := by grind
  exact ⟨by grind, rooted.of_same_parent (parent := .block block) (by simp [IRNode.parent!, opParent]) (by simp [IRNode.parent!, nextParent]),
    .of_parent_block (reachable.parent_block opParent) nextParent⟩

private theorem reachable_branch {ctx : WfIRContext OpCode} {moduleOp : OperationPtr}
    (verified : ctx.Verified moduleOp) {region : RegionPtr} {op : OperationPtr}
    (opIn : op.InBounds ctx.raw) (parent : op.getParentRegion! ctx.raw = some region)
    (rooted : op.RootedAt moduleOp ctx) (reachable : op.HierarchicallyReachable ctx)
    {destination : BlockPtr} (edge : destination ∈ op.getSuccessors! ctx.raw) :
    destination.InBounds ctx.raw ∧ destination.getParent! ctx.raw = some region ∧
    destination.RootedAt moduleOp ctx ∧ destination.HierarchicallyReachable ctx := by
  obtain ⟨block, opParent, blockParent⟩ := (show ∃ block,
    op.getParent! ctx.raw = some block ∧ block.getParent! ctx.raw = some region by
      grind [OperationPtr.getParentRegion!])
  have noNext := Veir.Puddle.CTree.verified_next_none_of_successor verified opIn opParent edge
  have blockIn : block.InBounds ctx.raw := by grind
  have last : block.getLastOp! ctx.raw = some op := by grind
  have blockEdge : destination ∈ block.getSuccessors! ctx.raw := by
    simpa [BlockPtr.getSuccessors!, last] using edge
  have destParent := verified.successor_parent blockIn blockParent blockEdge
  have destIn : destination.InBounds ctx.raw := by grind [BlockPtr.getParent!_of_not_inBounds]
  have blockRooted : block.RootedAt moduleOp ctx := rooted.of_ancestor (.of_parent (by grind))
  exact ⟨destIn, destParent,
    blockRooted.of_same_parent (parent := .region region)
      (by simp [IRNode.parent!, blockParent]) (by simp [IRNode.parent!, destParent]),
    Veir.Puddle.CTree.successor_reachable (reachable.parent_block opParent) blockParent destParent blockEdge⟩

/-- One source-reachable step uses only fields retained by the reachable frame. -/
theorem sim_interpretCFGCore_reachable_step
    (primitive : ∀ opType, OpCode.interpretCTree_monotone opType)
    {sourceCtx targetCtx : WfIRContext OpCode} {moduleOp : OperationPtr}
    (verified : sourceCtx.Verified moduleOp)
    (frame : ReachableContextFrame sourceCtx targetCtx moduleOp) (region : RegionPtr)
    {target : interpretCFG.StateLocation targetCtx × InterpreterState targetCtx}
    {source : interpretCFG.StateLocation sourceCtx × InterpreterState sourceCtx}
    (related : ReachableCFGStateRefines moduleOp region target source) :
    _root_.CTree.Sim (Sum.LiftRel (ReachableCFGStateRefines moduleOp region) PointerCFGResultRefines)
      (interpretCFGCore.iter target.1 target.2) (interpretCFGCore.iter source.1 source.2) := by
  rcases target with ⟨targetLocation, targetState⟩
  rcases source with ⟨sourceLocation, sourceState⟩
  rcases related with ⟨states, locations⟩
  cases targetLocation with
  | inl targetEntry =>
    cases sourceLocation with
    | inr => contradiction
    | inl sourceEntry =>
      rcases targetEntry with ⟨⟨targetBlock, targetIn⟩, targetValues⟩
      rcases sourceEntry with ⟨⟨block, sourceIn⟩, sourceValues⟩
      rcases locations with ⟨equal, values, parent, rooted, reachable⟩
      change targetBlock = block at equal
      subst targetBlock
      obtain ⟨_, types, firstEq⟩ := frame.block block sourceIn rooted reachable
      have counts : block.getNumArguments! targetCtx.raw = block.getNumArguments! sourceCtx.raw := by
        simpa only [BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] using congrArg Array.size types
      by_cases sourceSize : sourceValues.size = block.getNumArguments! sourceCtx.raw
      · have targetSize : targetValues.size = block.getNumArguments! targetCtx.raw := by have := values.1; omega
        simp only [interpretCFGCore.iter, ← BlockPtr.getNumArguments!_eq_getNumArguments sourceIn,
          ← BlockPtr.getNumArguments!_eq_getNumArguments targetIn, sourceSize, targetSize,
          bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        cases sourceSet : sourceState.variables.setArgumentValues? block sourceValues sourceIn with
        | none => exact sim_fail _ _
        | some sourceVariables =>
          obtain ⟨targetVariables, targetSet, variableRefinement⟩ :=
            pointer_arguments_refine sourceIn targetIn types states.2 values sourceSet
          simp only [targetSet]
          have firstSame : block.getFirstOp targetCtx.raw targetIn = block.getFirstOp sourceCtx.raw sourceIn := by grind
          split <;> split
          · rename_i targetFirst targetGet sourceFirst sourceGet
            have equal : targetFirst = sourceFirst := by grind
            subst targetFirst
            have firstBang : block.getFirstOp! sourceCtx.raw = some sourceFirst := by grind
            obtain ⟨firstParent, firstRooted, firstReachable⟩ := reachable_first sourceIn parent rooted reachable firstBang
            apply (_root_.CTree.Sim.pure _ _ _).mpr
            exact .inl ⟨⟨states.1, variableRefinement⟩, rfl, firstParent, firstRooted, firstReachable⟩
          · exact sim_fail _ _
          · grind
          · exact sim_fail _ _
      · simp only [interpretCFGCore.iter]
        have sourceSize' : (sourceValues.size != block.getNumArguments sourceCtx.raw sourceIn) = true := by
          simpa [← BlockPtr.getNumArguments!_eq_getNumArguments sourceIn] using sourceSize
        rw [sourceSize']
        simp only [↓reduceIte]
        exact sim_fail _ _
  | inr targetOp =>
    cases sourceLocation with
    | inl => contradiction
    | inr sourceOp =>
      rcases targetOp with ⟨targetOp, targetIn⟩
      rcases sourceOp with ⟨op, sourceIn⟩
      rcases locations with ⟨equal, parent, rooted, reachable⟩
      change targetOp = op at equal
      subst targetOp
      have opFrame := (frame.operation op region sourceIn parent rooted reachable).2
      have operation := sim_interpretOpCore_pointer primitive op sourceIn targetIn
        (OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants verified sourceIn)
        opFrame sourceState targetState states
      have operation := Veir.Puddle.CTree.sim_with_outcomes
        (interpretOpCore_pureOrErr op targetState targetIn)
        (interpretOpCore_pureOrErr op sourceState sourceIn) _ operation
      simp only [interpretCFGCore.iter]
      apply _root_.CTree.Sim.bind _ _ _ _ operation
      rintro ⟨targetFinal, targetAction⟩ ⟨sourceFinal, sourceAction⟩ ⟨⟨states', actions⟩, _, sourceOutcome⟩
      cases sourceAction with
      | none =>
        cases targetAction with
        | some => contradiction
        | none =>
          simp only
          have nextSame : op.getNextOp targetCtx.raw targetIn = op.getNextOp sourceCtx.raw sourceIn := by grind [opFrame.next]
          split <;> split
          · rename_i targetNext targetGet sourceNext sourceGet
            have equal : targetNext = sourceNext := by grind
            subst targetNext
            have nextBang : op.getNextOp! sourceCtx.raw = some sourceNext := by grind
            obtain ⟨nextParent, nextRooted, nextReachable⟩ := reachable_next sourceIn parent rooted reachable nextBang
            apply (_root_.CTree.Sim.pure _ _ _).mpr
            exact .inl ⟨states', rfl, nextParent, nextRooted, nextReachable⟩
          · exact sim_fail _ _
          · grind
          · exact sim_fail _ _
      | some sourceAction =>
        cases targetAction with
        | none => contradiction
        | some targetAction =>
          cases sourceAction <;> cases targetAction <;>
            simp only [ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy] at actions
          · apply (_root_.CTree.Sim.pure _ _ _).mpr
            exact .inr ⟨states', actions⟩
          · rcases actions with ⟨rfl, values⟩
            have edge := Veir.Puddle.CTree.interpretOpCore_branch_mem sourceIn sourceOutcome
            obtain ⟨destIn, destParent, destRooted, destReachable⟩ := reachable_branch verified sourceIn parent rooted reachable edge
            have targetDestIn := (frame.block _ destIn destRooted destReachable).1
            simp only [dite_eq_left destIn, dite_eq_left targetDestIn]
            apply (_root_.CTree.Sim.pure _ _ _).mpr
            exact .inl ⟨states', rfl, values, destParent, destRooted, destReachable⟩

/-- Reachable-context framing extends to the actual possibly infinite CFG loop. -/
theorem sim_interpretCFGCore_reachable_frame
    (primitive : ∀ opType, OpCode.interpretCTree_monotone opType)
    {sourceCtx targetCtx : WfIRContext OpCode} {moduleOp : OperationPtr}
    (verified : sourceCtx.Verified moduleOp)
    (frame : ReachableContextFrame sourceCtx targetCtx moduleOp) (region : RegionPtr)
    {target : interpretCFG.StateLocation targetCtx × InterpreterState targetCtx}
    {source : interpretCFG.StateLocation sourceCtx × InterpreterState sourceCtx}
    (related : ReachableCFGStateRefines moduleOp region target source) :
    _root_.CTree.Sim PointerCFGResultRefines
      (_root_.CTree.iter (fun next => interpretCFGCore.iter next.1 next.2) target)
      (_root_.CTree.iter (fun next => interpretCFGCore.iter next.1 next.2) source) := by
  exact _root_.CTree.Sim.iter _ _ target source related
    (fun _ _ h => sim_interpretCFGCore_reachable_step primitive verified frame region h)

end Veir.CTree
