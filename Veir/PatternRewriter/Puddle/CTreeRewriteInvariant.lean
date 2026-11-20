module
public import Veir.PatternRewriter.Puddle.CTreeModuleSoundness
public import Veir.PatternRewriter.Puddle.MatcherResolverHistory
public import Veir.Interpreter.CTreeFunctionRefinement
import all Veir.IRNesting
import all Veir.Interpreter.VariableState
import all Veir.Interpreter.CTreeEntryInvariant
import all Veir.PatternRewriter.Puddle.MatcherResolverHistory
import all Veir.PatternRewriter.Puddle.ReplacementScope
public section
namespace Veir.Puddle.CTree

/-- Source instruction locations are redirected only at the rewritten root. -/
def redirectedOperation (source : IRContext OpCode) (root : OperationPtr)
    (newOps : Array OperationPtr) (op : OperationPtr) : Option OperationPtr :=
  if op = root then newOps[0]? <|> root.getNextOp! source else some op

/-- Runtime invariant at aligned instruction entries. Historical matcher facts
refer to the original program and to the target's concrete resolver. -/
structure RewriteOpInvariant {sourceCtx targetCtx : WfIRContext OpCode}
    (mapping : ValueMapping sourceCtx targetCtx) (rewriteRoot : OperationPtr)
    (newOps : Array OperationPtr) (sourceRegion targetRegion : RegionPtr)
    (sourceOp : {op : OperationPtr // op.InBounds sourceCtx.raw})
    (targetOp : {op : OperationPtr // op.InBounds targetCtx.raw})
    (sourceState : InterpreterState sourceCtx) (targetState : InterpreterState targetCtx) : Prop where
  aligned : redirectedOperation sourceCtx.raw rewriteRoot newOps sourceOp = some targetOp.val
  sourceParent : sourceOp.val.getParentRegion! sourceCtx.raw = some sourceRegion
  targetParent : targetOp.val.getParentRegion! targetCtx.raw = some targetRegion
  sourceReachable : sourceOp.val.HierarchicallyReachable sourceCtx
  targetReachable : targetOp.val.HierarchicallyReachable targetCtx
  states : ScopedStateRefines mapping (.at (.before sourceOp)) (.at (.before targetOp))
    (by grind) (by grind) sourceState targetState
  sourceDefined : sourceState.DefinesDominatingIn sourceRegion (.before sourceOp)
  targetDefined : targetState.DefinesDominatingIn targetRegion (.before targetOp)
  matcherValues : ∀ value, value.InBounds sourceCtx.raw → value.DefinedInRegion sourceRegion sourceCtx →
    value.DominatesIp (.before rewriteRoot) sourceCtx → value.DominatesIp (.before sourceOp) sourceCtx →
    ∀ sourceValue targetValue,
      sourceState.variables.getVar? value = some sourceValue →
      targetState.variables.getVar? value = some targetValue →
      RuntimeValue.isRefinedBy sourceValue targetValue
  matcherDefined : ValueResolver.DefinesDominatingIn targetState.variables.getVar?
    sourceCtx sourceRegion rewriteRoot (.before sourceOp)
  matcherHistory : ValueResolver.CTreeEquationLemmaIn targetState.variables.getVar?
    sourceCtx sourceRegion rewriteRoot (.before sourceOp)

/-- The CFG relation keeps block arguments pending until the actual block-entry
step installs them. This avoids requiring argument slots in the initial empty state. -/
inductive RewriteCFGInvariant {sourceCtx targetCtx : WfIRContext OpCode}
    (mapping : ValueMapping sourceCtx targetCtx) (rewriteRoot : OperationPtr)
    (newOps : Array OperationPtr) (sourceRegion targetRegion : RegionPtr) :
    (Veir.CTree.interpretCFG.StateLocation targetCtx × InterpreterState targetCtx) →
    (Veir.CTree.interpretCFG.StateLocation sourceCtx × InterpreterState sourceCtx) → Prop
  | operation {sourceOp targetOp sourceState targetState}
      (invariant : RewriteOpInvariant mapping rewriteRoot newOps sourceRegion targetRegion
        sourceOp targetOp sourceState targetState) :
      RewriteCFGInvariant mapping rewriteRoot newOps sourceRegion targetRegion
        (.inr targetOp, targetState) (.inr sourceOp, sourceState)
  | block {sourceBlock : {b : BlockPtr // b.InBounds sourceCtx.raw}}
      {targetBlock : {b : BlockPtr // b.InBounds targetCtx.raw}}
      {sourceArgs targetArgs : Array RuntimeValue} {sourceState targetState}
      (sameBlock : targetBlock.val = sourceBlock.val)
      (pending : ∀ sourceVariables,
        sourceState.variables.setArgumentValues? sourceBlock sourceArgs sourceBlock.property = some sourceVariables →
        ∀ sourceFirst (sourceFirstIn : sourceFirst.InBounds sourceCtx.raw),
        sourceBlock.val.getFirstOp! sourceCtx.raw = some sourceFirst →
        ∃ (targetVariables : VariableState targetCtx) (targetFirst : OperationPtr)
          (targetFirstIn : targetFirst.InBounds targetCtx.raw),
          targetState.variables.setArgumentValues? targetBlock targetArgs targetBlock.property = some targetVariables ∧
          targetBlock.val.getFirstOp! targetCtx.raw = some targetFirst ∧
          RewriteOpInvariant mapping rewriteRoot newOps sourceRegion targetRegion
            ⟨sourceFirst, sourceFirstIn⟩ ⟨targetFirst, targetFirstIn⟩
            ⟨sourceVariables, sourceState.memory⟩ ⟨targetVariables, targetState.memory⟩) :
      RewriteCFGInvariant mapping rewriteRoot newOps sourceRegion targetRegion
        (.inl (targetBlock, targetArgs), targetState) (.inl (sourceBlock, sourceArgs), sourceState)


/-- Function-local definedness supplies every operand once IR scope/isolation
has established that those operands belong to the current region. -/
theorem exists_operandValues_of_definesDominatingIn
    {ctx : WfIRContext OpCode} (op : OperationPtr) (_opIn : op.InBounds ctx.raw)
    (state : InterpreterState ctx) (defined : state.DefinesDominatingIn region (.before op))
    (localOperands : ∀ value ∈ op.getOperands! ctx.raw, value.DefinedInRegion region ctx)
    (operandScopes : ∀ value ∈ op.getOperands! ctx.raw, value.DominatesIp (.before op) ctx) :
    ∃ values, state.variables.getOperandValues op = some values := by
  simp only [VariableState.getOperandValues, Array.exists_mapM_option_eq_some_iff]
  intro index indexIn
  have member : (op.getOperands! ctx.raw)[index] ∈ op.getOperands! ctx.raw := by grind
  have available := defined _ (by grind) (localOperands _ member) (operandScopes _ member)
  exact Option.isSome_iff_exists.mp available

/-- The target groups the newly inserted instruction list into one transition. -/
def rewriteTargetBatch {ctx : WfIRContext OpCode} (newOps : Array OperationPtr)
    (state : Veir.CTree.interpretCFG.StateLocation ctx × InterpreterState ctx) : Nat :=
  match state.1 with
  | .inl _ => 1
  | .inr op => if newOps[0]? = some op.val then max 1 newOps.size else 1

/-- Empty replacements group the deleted source root with its following step. -/
def rewriteSourceBatch {ctx : WfIRContext OpCode} (root : OperationPtr) (newOps : Array OperationPtr)
    (state : Veir.CTree.interpretCFG.StateLocation ctx × InterpreterState ctx) : Nat :=
  match state.1 with
  | .inl _ => 1
  | .inr op => if newOps.isEmpty && decide (op.val = root) then 2 else 1

theorem rewriteTargetBatch_positive {ctx : WfIRContext OpCode} (newOps : Array OperationPtr)
    (state : Veir.CTree.interpretCFG.StateLocation ctx × InterpreterState ctx) :
    0 < rewriteTargetBatch newOps state := by
  unfold rewriteTargetBatch
  split
  · omega
  · split <;> omega

theorem rewriteSourceBatch_positive {ctx : WfIRContext OpCode} (root : OperationPtr)
    (newOps : Array OperationPtr)
    (state : Veir.CTree.interpretCFG.StateLocation ctx × InterpreterState ctx) :
    0 < rewriteSourceBatch root newOps state := by
  unfold rewriteSourceBatch
  split
  · omega
  · split <;> omega

/-- The static dependency invariant resolves original root operands even when
a replacement does not read them, and supplies their pointwise refinement. -/
theorem RewriteOpInvariant.root_operandValues
    {sourceCtx targetCtx : WfIRContext OpCode} {mapping : ValueMapping sourceCtx targetCtx}
    {root : OperationPtr} {newOps : Array OperationPtr} {sourceRegion targetRegion : RegionPtr}
    {rootIn : root.InBounds sourceCtx.raw} {targetOp : {op : OperationPtr // op.InBounds targetCtx.raw}}
    {sourceState : InterpreterState sourceCtx} {targetState : InterpreterState targetCtx}
    (invariant : RewriteOpInvariant mapping root newOps sourceRegion targetRegion
      ⟨root, rootIn⟩ targetOp sourceState targetState)
    (localOperands : ∀ value ∈ root.getOperands! sourceCtx.raw, value.DefinedInRegion sourceRegion sourceCtx)
    (operandScopes : ∀ value ∈ root.getOperands! sourceCtx.raw, value.DominatesIp (.before root) sourceCtx) :
    ∃ (sourceValues : Array RuntimeValue) (targetValues : List RuntimeValue),
      sourceState.variables.getOperandValues root = some sourceValues ∧
      (root.getOperands! sourceCtx.raw).toList.mapM targetState.variables.getVar? = some targetValues ∧
      RuntimeValue.arrayIsRefinedBy sourceValues targetValues.toArray := by
  obtain ⟨sourceValues, sourceGet⟩ := exists_operandValues_of_definesDominatingIn root rootIn sourceState
    invariant.sourceDefined localOperands operandScopes
  have targetAvailable : ∃ values, (root.getOperands! sourceCtx.raw).mapM targetState.variables.getVar? = some values := by
    apply Array.exists_mapM_option_eq_some_iff.mpr
    intro index indexIn
    have member : (root.getOperands! sourceCtx.raw)[index] ∈ root.getOperands! sourceCtx.raw := by grind
    obtain ⟨value, lookup, _⟩ := invariant.matcherDefined _ (by grind) (localOperands _ member)
      (operandScopes _ member) (operandScopes _ member)
    exact ⟨value, lookup⟩
  obtain ⟨targetArray, targetGet⟩ := targetAvailable
  have refined : RuntimeValue.arrayIsRefinedBy sourceValues targetArray := by
    have sourceOperands : (root.getOperands! sourceCtx.raw).mapM sourceState.variables.getVar? = some sourceValues := sourceGet
    constructor
    · grind
    · intro index indexIn
      have sourceLookup := Array.mapM_option_eq_some_implies sourceOperands index (by grind)
      have targetLookup := Array.mapM_option_eq_some_implies targetGet index (by grind)
      have operandIndex : index < (root.getOperands! sourceCtx.raw).size := by grind
      have member : (root.getOperands! sourceCtx.raw)[index] ∈ root.getOperands! sourceCtx.raw := by grind
      have valueRef := invariant.matcherValues _ (by grind) (localOperands _ member)
        (operandScopes _ member) (operandScopes _ member) _ _ sourceLookup targetLookup
      grind
  rw [Array.mapM_eq_mapM_toList] at targetGet
  cases listGet : (root.getOperands! sourceCtx.raw).toList.mapM targetState.variables.getVar? with
  | none => rw [listGet] at targetGet; contradiction
  | some targetValues =>
    rw [listGet] at targetGet
    change some targetValues.toArray = some targetArray at targetGet
    cases targetGet
    exact ⟨sourceValues, targetValues, sourceGet, rfl, refined⟩

/-- The root writes no statically watched dependency, and the actual fresh
batch writes no original SSA slot. Static dependency refinement therefore
survives root replacement at every following source program point. -/
theorem RewriteOpInvariant.matcherValues_after_root
    {sourceCtx targetCtx : WfIRContext OpCode} {mapping : ValueMapping sourceCtx targetCtx}
    {root : OperationPtr} {newOps : Array OperationPtr} {sourceRegion targetRegion : RegionPtr}
    {rootIn : root.InBounds sourceCtx.raw} {targetOp : {op : OperationPtr // op.InBounds targetCtx.raw}}
    {sourceState : InterpreterState sourceCtx} {targetState targetAfter : InterpreterState targetCtx}
    (invariant : RewriteOpInvariant mapping root newOps sourceRegion targetRegion
      ⟨root, rootIn⟩ targetOp sourceState targetState)
    (rootRooted : root.RootedAt irRoot sourceCtx)
    (rootSSA : sourceRegion.hasSSADominance sourceCtx)
    {sourceValues : Array RuntimeValue} {sourceAfter : VariableState sourceCtx}
    (sourceSet : sourceState.variables.setResultValues? root sourceValues rootIn = some sourceAfter)
    (targetFrame : ∀ value, value.InBounds sourceCtx.raw →
      targetAfter.variables.getVar? value = targetState.variables.getVar? value)
    (next : InsertPoint) :
    ∀ value, value.InBounds sourceCtx.raw → value.DefinedInRegion sourceRegion sourceCtx →
      value.DominatesIp (.before root) sourceCtx → value.DominatesIp next sourceCtx →
      ∀ sourceValue targetValue,
        sourceAfter.getVar? value = some sourceValue →
        targetAfter.variables.getVar? value = some targetValue →
        RuntimeValue.isRefinedBy sourceValue targetValue := by
  intro value valueIn localValue staticScope _ sourceValue targetValue sourceLookup targetLookup
  have notResult : value ∉ root.getResults! sourceCtx.raw := by
    intro member
    obtain ⟨index, bound, equal⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp member
    have scope : ReplacementValueScope sourceCtx root value := .inl staticScope
    exact scope.notOwn rootRooted invariant.sourceParent rootSSA rootIn index bound equal
  have sourceFrame := VariableState.getVar?_setResultValues?_of_notMem_getResults! notResult sourceSet
  rw [sourceFrame] at sourceLookup
  rw [targetFrame value valueIn] at targetLookup
  exact invariant.matcherValues value valueIn localValue staticScope staticScope
    sourceValue targetValue sourceLookup targetLookup

theorem rewriteTargetBatch_at_head {ctx : WfIRContext OpCode} (newOps : Array OperationPtr)
    (op : {op : OperationPtr // op.InBounds ctx.raw}) (state : InterpreterState ctx)
    (head : newOps[0]? = some op.val) (positive : 0 < newOps.size) :
    rewriteTargetBatch newOps (.inr op, state) = newOps.size := by
  unfold rewriteTargetBatch
  dsimp only
  rw [ite_eq_left head]
  omega

theorem rewriteSourceBatch_nonempty {ctx : WfIRContext OpCode} (root : OperationPtr)
    (newOps : Array OperationPtr) (state : Veir.CTree.interpretCFG.StateLocation ctx × InterpreterState ctx)
    (positive : 0 < newOps.size) : rewriteSourceBatch root newOps state = 1 := by
  unfold rewriteSourceBatch
  have notEmpty : newOps.isEmpty = false := by simp [Array.isEmpty, Nat.ne_of_gt positive]
  split
  · rfl
  · simp only [notEmpty, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem operation_rootedAt_of_parentRegion {ctx : WfIRContext OpCode}
    {region : RegionPtr} {op : OperationPtr} {irRoot : IRNode}
    (rooted : region.RootedAt irRoot ctx) (parent : op.getParentRegion! ctx.raw = some region) :
    op.RootedAt irRoot ctx := by
  obtain ⟨block, opParent, blockParent⟩ := OperationPtr.getParentRegion!_eq_some_iff.mp parent
  have blockRooted : block.RootedAt irRoot ctx := rooted.of_parent (by
    simp only [IRNode.parent!_block, blockParent, Option.map_some])
  exact blockRooted.of_parent (by simp only [IRNode.parent!_operation, opParent, Option.map_some])

end Veir.Puddle.CTree
