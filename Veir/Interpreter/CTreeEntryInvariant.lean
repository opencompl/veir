module

public import Veir.Interpreter.CTreeEquationLemma
import all Veir.Dominance.Basic
import all Veir.Interpreter.VariableState
import all Veir.IR.Basic

public section

namespace Veir

/-- No block properly dominates the entry of its own SSA region. -/
theorem BlockPtr.not_properlyDominatesInRegion_entry {ctx : WfIRContext OpCode}
    {region : RegionPtr} {entry dominator : BlockPtr}
    (first : region.getFirstBlock! ctx.raw = some entry)
    (parent : entry.getParent! ctx.raw = some region)
    (ssa : region.hasSSADominance ctx) :
    ¬ dominator.ProperlyDominatesInRegion entry region ctx := by
  intro dominance
  cases dominance with
  | Graph h => grind [BlockPtr.ProperlyDominatesInGraphRegion]
  | Ssa h =>
    have member := h.mem_of_path first (.Single parent)
    have equal : dominator = entry := by simpa using member
    exact h.2.2.2.1 equal

/-- Within an SSA function body, no operation dominates its entry point. -/
theorem OperationPtr.not_dominatesIp_region_entry {ctx : WfIRContext OpCode}
    {region : RegionPtr} {entry : BlockPtr} {op : OperationPtr} {root : IRNode}
    (first : region.getFirstBlock! ctx.raw = some entry)
    (parent : entry.getParent! ctx.raw = some region)
    (ssa : region.hasSSADominance ctx) (rooted : entry.RootedAt root ctx)
    (inside : region.Ancestor op ctx) :
    ¬op.DominatesIp (InsertPoint.atStart! entry ctx.raw) ctx := by
  intro dominance
  have blockDom := dominance.properlyDominatesBlock_of_atStart parent ssa
  obtain ⟨opRegion, opParentRegion⟩ := blockDom.exists_parentRegion
  obtain ⟨block, opParent, _⟩ := OperationPtr.getParentRegion!_eq_some_iff.mp opParentRegion
  exact BlockPtr.not_properlyDominatesInRegion_entry first parent ssa
    (blockDom.properlyDominatesInRegion_of_ancestor_region rooted parent opParent inside)

/-- The part of historical SSA information belonging to the currently interpreted region. -/
def VariableState.CTreeEquationLemmaIn {ctx : WfIRContext OpCode} (state : VariableState ctx)
    (region : RegionPtr) (location : InsertPoint) : Prop :=
  ∀ (op : OperationPtr), op.InBounds ctx.raw → region.Ancestor op ctx →
    HasOpInfo.isTerminator (op.getOpType! ctx.raw) = false →
    op.DominatesIp location ctx → state.CTreeEquationHolds op

/-- Initial historical SSA information is empty within the function body. -/
theorem VariableState.ctreeEquationLemmaIn_entry {ctx : WfIRContext OpCode}
    (state : VariableState ctx) {region : RegionPtr} {entry : BlockPtr} {root : IRNode}
    (first : region.getFirstBlock! ctx.raw = some entry)
    (parent : entry.getParent! ctx.raw = some region)
    (ssa : region.hasSSADominance ctx) (rooted : entry.RootedAt root ctx) :
    state.CTreeEquationLemmaIn region (InsertPoint.atStart! entry ctx.raw) := by
  intro op _ inside _ dominance
  exact False.elim
    (OperationPtr.not_dominatesIp_region_entry first parent ssa rooted inside dominance)

/-- A value is defined directly by an operation or block in this region. -/
def ValuePtr.DefinedInRegion (value : ValuePtr) (region : RegionPtr)
    (ctx : WfIRContext OpCode) : Prop :=
  match value with
  | .opResult result => result.op.getParentRegion! ctx.raw = some region
  | .blockArgument argument => argument.block.getParent! ctx.raw = some region

/-- Only values belonging to this function's region must be present during its execution. -/
def InterpreterState.DefinesDominatingIn {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (region : RegionPtr) (location : InsertPoint) : Prop :=
  ∀ (value : ValuePtr), value.InBounds ctx.raw → value.DefinedInRegion region ctx →
    value.DominatesIp location ctx → (state.variables.getVar? value).isSome

/-- Installing the entry arguments initializes every dominating value of the function body. -/
theorem InterpreterState.definesDominatingIn_entry {ctx : WfIRContext OpCode}
    {before after : VariableState ctx} {region : RegionPtr} {entry : BlockPtr} {root : IRNode}
    {values : Array RuntimeValue} {entryIn : entry.InBounds ctx.raw}
    (memory : MemoryState)
    (first : region.getFirstBlock! ctx.raw = some entry)
    (parent : entry.getParent! ctx.raw = some region)
    (ssa : region.hasSSADominance ctx) (rooted : entry.RootedAt root ctx)
    (set : before.setArgumentValues? entry values entryIn = some after) :
    (InterpreterState.mk after memory).DefinesDominatingIn region
      (InsertPoint.atStart! entry ctx.raw) := by
  intro value valueIn inside dominance
  cases value with
  | opResult result =>
    cases dominance with
    | OpResult _ dominance =>
      exact False.elim (OperationPtr.not_dominatesIp_region_entry first parent ssa rooted
        (IRNode.Ancestor.of_getParentRegion!_eq_some inside) dominance)
  | blockArgument argument =>
    cases dominance with
    | BlockArg argumentIn ipParent dominance =>
      rename_i ipBlockPtr
      have ipBlock := InsertPoint.block!_atStart!_eq ctx.wellFormed entryIn
      have sameIpBlock : ipBlockPtr = entry := Option.some.inj (ipParent.symm.trans ipBlock)
      subst ipBlockPtr
      have blockParent : argument.block.getParent! ctx.raw = some region := inside
      rcases dominance.eq_or_properlyDominatesInRegion_of_same_parent_region
          rooted blockParent parent with same | proper
      · have indexBound : argument.index < entry.getNumArguments! ctx.raw := by
          rw [BlockPtr.getNumArguments!_eq_getNumArguments entryIn]
          simpa only [BlockPtr.getNumArguments, same] using argumentIn.2
        have valueEq : ValuePtr.blockArgument argument = entry.getArgument argument.index := by
          cases argument
          simp_all [BlockPtr.getArgument_def]
        rw [valueEq]
        grind
      · exact False.elim (BlockPtr.not_properlyDominatesInRegion_entry first parent ssa proper)

/-- Checked result installation preserves function-local definedness at the next program point. -/
theorem InterpreterState.DefinesDominatingIn.setResultValues
    {ctx : WfIRContext OpCode} {state state' : VariableState ctx}
    {region : RegionPtr} {op : OperationPtr} {block : BlockPtr}
    {results : Array RuntimeValue} {opIn : op.InBounds ctx.raw}
    {before after : MemoryState}
    (prior : (InterpreterState.mk state before).DefinesDominatingIn region (.before op))
    (opParent : op.getParent! ctx.raw = some block)
    (blockParent : block.getParent! ctx.raw = some region)
    (set : state.setResultValues? op results opIn = some state') :
    (InterpreterState.mk state' after).DefinesDominatingIn region
      (InsertPoint.after op ctx.raw block) := by
  intro value valueIn inside dominance
  rcases (ValuePtr.DominatesIp.after_iff blockParent).mp dominance with old | result
  · have present := prior value valueIn inside old
    grind
  · grind [OperationPtr.getResults!.mem_iff_exists_index]

/-- Installing successor arguments preserves function-local definedness across a CFG edge. -/
theorem InterpreterState.DefinesDominatingIn.setArgumentValues_succ_entry
    {ctx : WfIRContext OpCode} {state state' : VariableState ctx}
    {region : RegionPtr} {block succ : BlockPtr} {values : Array RuntimeValue}
    {succIn : succ.InBounds ctx.raw} {memory : MemoryState}
    (blockParent : block.getParent! ctx.raw = some region)
    (succParent : succ.getParent! ctx.raw = some region)
    (ssa : region.hasSSADominance ctx) (successor : succ ∈ block.getSuccessors! ctx.raw)
    (prior : (InterpreterState.mk state memory).DefinesDominatingIn region (.atEnd block))
    (set : state.setArgumentValues? succ values succIn = some state') :
    (InterpreterState.mk state' memory).DefinesDominatingIn region
      (InsertPoint.atStart! succ ctx.raw) := by
  intro value valueIn inside dominance
  rcases ValuePtr.DominatesIp.predecessor_exit_of_successor_entry
      blockParent succParent ssa successor dominance with old | argument
  · have present := prior value valueIn inside old
    grind
  · obtain ⟨index, bound, rfl⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp argument
    simp only [VariableState.getVar?_getArgument_of_setArgumentValues? bound set, Option.isSome_some]

/-- A successful local opcode event extends the function's historical execution invariant. -/
theorem VariableState.ctreeEquationLemmaIn_after_outcome
    {ctx : WfIRContext OpCode} {state state' : VariableState ctx}
    {op : OperationPtr} {operands results : Array RuntimeValue} {before after : MemoryState}
    {root : IRNode} {region : RegionPtr} {block : BlockPtr} {opIn : op.InBounds ctx.raw}
    (ctxDom : ctx.Dom root) (opRooted : op.RootedAt root ctx)
    (opRegion : op.getParentRegion! ctx.raw = some region) (ssa : region.hasSSADominance ctx)
    (opReachable : op.HierarchicallyReachable ctx)
    (opParent : op.getParent! ctx.raw = some block)
    (prior : state.CTreeEquationLemmaIn region (.before op))
    (operandsGet : state.getOperandValues op = some operands)
    (set : state.setResultValues? op results opIn = some state')
    (outcome : PureOrErr.CanInterpretTo
      (CTree.interpretOp' (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw) operands (op.getSuccessors! ctx.raw) before
        (op.getRegions! ctx.raw)) (.ok (results, after, none))) :
    state'.CTreeEquationLemmaIn region (InsertPoint.after op ctx.raw block) := by
  intro observed observedIn inside nonterm dominance
  simp [OperationPtr.DominatesIp.after_iff opRooted
    (show block.getParent! ctx.raw = some region by grind)] at dominance
  simp [OperationPtr.dominates_iff_properlyDominates_or_eq] at dominance
  rcases dominance with old | self
  · have equation : state.CTreeEquationHolds observed :=
      prior observed observedIn inside nonterm (by grind)
    apply equation.setResultValues_of_dominates ctxDom (by grind) opRegion ssa opReachable
      (by grind) ?_ set
    grind
  · subst observed
    exact VariableState.ctreeEquationHolds_of_outcome_self ctxDom opRooted opRegion
      (by grind) ssa operandsGet set outcome

/-- Historical executions within a function survive a CFG edge and argument installation. -/
theorem VariableState.CTreeEquationLemmaIn.after_terminator
    {ctx : WfIRContext OpCode} {state state' : VariableState ctx}
    {op : OperationPtr} {results : Array RuntimeValue}
    {root : IRNode} {region : RegionPtr} {block : BlockPtr} {opIn : op.InBounds ctx.raw}
    (ctxDom : ctx.Dom root) (opRooted : op.RootedAt root ctx)
    (opRegion : op.getParentRegion! ctx.raw = some region) (ssa : region.hasSSADominance ctx)
    (opReachable : op.HierarchicallyReachable ctx)
    (opParent : op.getParent! ctx.raw = some block)
    (terminator : HasOpInfo.isTerminator (op.getOpType! ctx.raw) = true)
    (prior : state.CTreeEquationLemmaIn region (.before op))
    (set : state.setResultValues? op results opIn = some state') :
    state'.CTreeEquationLemmaIn region (InsertPoint.after op ctx.raw block) := by
  intro observed observedIn inside nonterm dominance
  simp [OperationPtr.DominatesIp.after_iff opRooted
    (show block.getParent! ctx.raw = some region by grind)] at dominance
  simp [OperationPtr.dominates_iff_properlyDominates_or_eq] at dominance
  rcases dominance with old | self
  · have equation : state.CTreeEquationHolds observed :=
      prior observed observedIn inside nonterm (by grind)
    apply equation.setResultValues_of_dominates ctxDom (by grind) opRegion ssa opReachable
      (by grind) ?_ set
    grind
  · subst observed
    simp [terminator] at nonterm

/-- Historical executions within a function survive a CFG edge and argument installation. -/
theorem VariableState.CTreeEquationLemmaIn.setArgumentValues_succ_entry
    {ctx : WfIRContext OpCode} {state state' : VariableState ctx}
    {block succ : BlockPtr} {values : Array RuntimeValue} {succIn : succ.InBounds ctx.raw}
    {root : IRNode} {region : RegionPtr}
    (ctxDom : ctx.Dom root) (_blockIn : block.InBounds ctx.raw)
    (blockParent : block.getParent! ctx.raw = some region) (successor : succ ∈ block.getSuccessors! ctx.raw)
    (succParent : succ.getParent! ctx.raw = some region) (ssa : region.hasSSADominance ctx)
    (succRooted : succ.RootedAt root ctx) (succReachable : succ.HierarchicallyReachable ctx)
    (prior : state.CTreeEquationLemmaIn region (.atEnd block))
    (set : state.setArgumentValues? succ values succIn = some state') :
    state'.CTreeEquationLemmaIn region (InsertPoint.atStart! succ ctx.raw) := by
  intro op opIn inside nonterm dominance
  have old : op.DominatesIp (.atEnd block) ctx := by
    grind [OperationPtr.DominatesIp.predecessor_exit_of_successor_entry]
  exact (prior op opIn inside nonterm old).setArgumentValues_of_dominatesIp
    ctxDom succParent ssa succRooted succReachable dominance set

end Veir
