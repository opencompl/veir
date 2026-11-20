module

public import Veir.Interpreter.CTreeInterpreter
public import Veir.Interpreter.EquationLemma
public import Veir.Interpreter.Lemmas
import all Veir.Interpreter.VariableState
import all Veir.Dominance.Basic

namespace Veir

public section

/-- Historical SSA equation: the current operands and results occurred together in a successful
past execution. Current memory is deliberately absent, so later stores cannot invalidate it. -/
def VariableState.CTreeEquationHolds {ctx : WfIRContext OpCode} (state : VariableState ctx)
    (op : OperationPtr) : Prop :=
  ∃ operands results before after,
    state.getOperandValues op = some operands ∧
    (op.getResults! ctx.raw).mapM state.getVar? = some results ∧
    PureOrErr.CanInterpretTo
      (CTree.interpretOp' (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw) operands (op.getSuccessors! ctx.raw) before
        (op.getRegions! ctx.raw)) (.ok (results, after, none))

/-- Historical equations depend only on the SSA variable component of an interpreter state. -/
def InterpreterState.CTreeEquationHolds {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (op : OperationPtr) : Prop := state.variables.CTreeEquationHolds op

private theorem mapM_eq_of_mem {α β : Type} (xs : Array α) (f g : α → Option β)
    (h : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  have hlist (ys : List α) (hy : ∀ x ∈ ys, f x = g x) : ys.mapM f = ys.mapM g := by
    induction ys with
    | nil => rfl
    | cons y ys ih =>
      simp only [List.mapM_cons]
      rw [hy y (by simp), ih (by intro x hx; exact hy x (by simp [hx]))]
  simp only [Array.mapM_eq_mapM_toList]
  rw [hlist xs.toList (by simpa using h)]

/-- Preserving operand and result lookups preserves historical executions without replaying choices. -/
theorem VariableState.CTreeEquationHolds.of_lookup_eq {ctx : WfIRContext OpCode}
    {state state' : VariableState ctx} {op : OperationPtr} (h : state.CTreeEquationHolds op)
    (hoperands : state'.getOperandValues op = state.getOperandValues op)
    (hresults : ∀ value ∈ op.getResults! ctx.raw, state'.getVar? value = state.getVar? value) :
    state'.CTreeEquationHolds op := by
  obtain ⟨operands, results, before, after, ho, hr, ht⟩ := h
  exact ⟨operands, results, before, after, hoperands.trans ho,
    (mapM_eq_of_mem _ _ _ hresults).trans hr, ht⟩

/-- Checked result installation records exactly the returned result array. -/
theorem VariableState.getResults_of_setResultValues {ctx : WfIRContext OpCode}
    {state state' : VariableState ctx} {op : OperationPtr} {results : Array RuntimeValue}
    {hop : op.InBounds ctx.raw} (hset : state.setResultValues? op results hop = some state') :
    (op.getResults! ctx.raw).mapM state'.getVar? = some results := by
  have hsize := VariableState.setResultValues?.getNumRseults!_eq_size hset
  apply (Array.mapM_eq_some_iff_of_size_eq (by simpa using hsize)).mpr
  intro i hi
  have hi' : i < op.getNumResults! ctx.raw := by simpa using hi
  rw [OperationPtr.getResults!.getElem!_eq_getResult hi']
  exact VariableState.getVar?_getResult_of_setResultValues? hi' hset

/-- A newly observed raw opcode return establishes its historical equation after checked binding. -/
theorem VariableState.ctreeEquationHolds_of_outcome {ctx : WfIRContext OpCode}
    {state state' : VariableState ctx} {op : OperationPtr} {operands results : Array RuntimeValue}
    {before after : MemoryState} {hop : op.InBounds ctx.raw}
    (hoperands : state.getOperandValues op = some operands)
    (hpreserved : state'.getOperandValues op = state.getOperandValues op)
    (hset : state.setResultValues? op results hop = some state')
    (houtcome : PureOrErr.CanInterpretTo
      (CTree.interpretOp' (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw) operands (op.getSuccessors! ctx.raw) before
        (op.getRegions! ctx.raw)) (.ok (results, after, none))) :
    state'.CTreeEquationHolds op :=
  ⟨operands, results, before, after, hpreserved.trans hoperands,
    VariableState.getResults_of_setResultValues hset, houtcome⟩

/-- Dominance supplies the operand stability needed to record a just-executed operation. -/
theorem VariableState.ctreeEquationHolds_of_outcome_self {ctx : WfIRContext OpCode}
    {state state' : VariableState ctx} {op : OperationPtr} {operands results : Array RuntimeValue}
    {before after : MemoryState} {hop : op.InBounds ctx.raw}
    (ctxDom : ctx.Dom root) (opRooted : op.RootedAt root ctx)
    (opRegion : op.getParentRegion! ctx.raw = some region)
    (opReachable : op.LocallyReachable region ctx) (ssa : region.hasSSADominance ctx)
    (hoperands : state.getOperandValues op = some operands)
    (hset : state.setResultValues? op results hop = some state')
    (houtcome : PureOrErr.CanInterpretTo
      (CTree.interpretOp' (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw) operands (op.getSuccessors! ctx.raw) before
        (op.getRegions! ctx.raw)) (.ok (results, after, none))) :
    state'.CTreeEquationHolds op := by
  apply VariableState.ctreeEquationHolds_of_outcome hoperands ?_ hset houtcome
  exact VariableState.getOperandValues_setResultValues?_self ctxDom opRooted opRegion opReachable ssa hset

/-- Setting results of a distinct dominated operation preserves a dominator's historical equation. -/
theorem VariableState.CTreeEquationHolds.setResultValues_of_dominates
    {ctx : WfIRContext OpCode} {state state' : VariableState ctx} {op observed : OperationPtr}
    {results : Array RuntimeValue} {hop : op.InBounds ctx.raw}
    (ctxDom : ctx.Dom root) (observedRooted : observed.RootedAt root ctx)
    (opRegion : op.getParentRegion! ctx.raw = some region) (ssa : region.hasSSADominance ctx)
    (opReachable : op.HierarchicallyReachable ctx)
    (hdom : observed.Dominates op ctx false) (hne : observed ≠ op)
    (heq : state.CTreeEquationHolds observed)
    (hset : state.setResultValues? op results hop = some state') :
    state'.CTreeEquationHolds observed := by
  apply heq.of_lookup_eq
  · exact VariableState.getOperandValues_setResultValues?_of_dominates
      ctxDom observedRooted hdom opRegion ssa opReachable hset
  · intro value hvalue
    apply VariableState.getVar?_setResultValues?_of_notMem_getResults! _ hset
    intro hother
    grind [OperationPtr.getResults!.mem_iff_exists_index, OperationPtr.getResult_def]

/-- Entering a block preserves an operation's historical results and any disjoint operands. -/
theorem VariableState.CTreeEquationHolds.setArgumentValues_of_disjoint
    {ctx : WfIRContext OpCode} {state state' : VariableState ctx} {op : OperationPtr}
    {block : BlockPtr} {values : Array RuntimeValue} {hblock : block.InBounds ctx.raw}
    (heq : state.CTreeEquationHolds op)
    (hoperands : ∀ value ∈ op.getOperands! ctx.raw, value ∉ block.getArguments! ctx.raw)
    (hset : state.setArgumentValues? block values hblock = some state') :
    state'.CTreeEquationHolds op := by
  apply heq.of_lookup_eq
  · apply VariableState.getOperandValues_eq_of_getVar?_eq
    intro value hvalue
    exact VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! (hoperands value hvalue) hset
  · intro value hvalue
    apply VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! _ hset
    intro hargument
    grind [OperationPtr.getResults!.mem_iff_exists_index, BlockPtr.getArguments!.mem_iff_exists_index,
      OperationPtr.getResult_def, BlockPtr.getArgument_def]

/-- Historical equations of operations dominating a successor entry survive argument installation. -/
theorem VariableState.CTreeEquationHolds.setArgumentValues_of_dominatesIp
    {ctx : WfIRContext OpCode} {state state' : VariableState ctx} {op : OperationPtr}
    {succ : BlockPtr} {values : Array RuntimeValue} {hsucc : succ.InBounds ctx.raw}
    (ctxDom : ctx.Dom root) (succParent : succ.getParent! ctx.raw = some region)
    (ssa : region.hasSSADominance ctx) (succRooted : succ.RootedAt root ctx)
    (succReachable : succ.HierarchicallyReachable ctx)
    (opDom : op.DominatesIp (InsertPoint.atStart! succ ctx.raw) ctx)
    (heq : state.CTreeEquationHolds op)
    (hset : state.setArgumentValues? succ values hsucc = some state') :
    state'.CTreeEquationHolds op := by
  have opRooted : op.RootedAt root ctx := by grind
  have opReachable : op.HierarchicallyReachable ctx := by grind
  have ipParent : (InsertPoint.atStart! succ ctx.raw).block! ctx.raw = some succ := by grind
  obtain ⟨opRegion, opParentRegion⟩ := opDom.exists_parentRegion ipParent succParent
  have succLocallyReachable : succ.LocallyReachable region ctx := by grind
  have argumentsNotDominating : ∀ value, value ∈ succ.getArguments! ctx.raw →
      ¬value.DominatesIp (InsertPoint.before op) ctx := by grind
  apply heq.setArgumentValues_of_disjoint ?_ hset
  intro value hoperand hargument
  have hd : value.DominatesIp (InsertPoint.before op) ctx := by grind
  exact argumentsNotDominating value hargument hd

/-- At a program point, each dominating nonterminator retains a successful historical equation. -/
def VariableState.CTreeEquationLemmaAt {ctx : WfIRContext OpCode} (state : VariableState ctx)
    (location : InsertPoint) : Prop :=
  ∀ (op : OperationPtr) (_ : op.InBounds ctx.raw),
    HasOpInfo.isTerminator (op.getOpType! ctx.raw) = false →
    op.DominatesIp location ctx → state.CTreeEquationHolds op

/-- A successful non-control-flow opcode event preserves the historical SSA invariant after it. -/
theorem VariableState.ctreeEquationLemmaAt_after_outcome
    {ctx : WfIRContext OpCode} {state state' : VariableState ctx}
    {op : OperationPtr} {operands results : Array RuntimeValue} {before after : MemoryState}
    {hop : op.InBounds ctx.raw}
    (ctxDom : ctx.Dom root) (opRooted : op.RootedAt root ctx)
    (opRegion : op.getParentRegion! ctx.raw = some region) (ssa : region.hasSSADominance ctx)
    (opReachable : op.HierarchicallyReachable ctx)
    (opParent : op.getParent! ctx.raw = some block)
    (hprior : state.CTreeEquationLemmaAt (InsertPoint.before op))
    (hoperands : state.getOperandValues op = some operands)
    (hset : state.setResultValues? op results hop = some state')
    (houtcome : PureOrErr.CanInterpretTo
      (CTree.interpretOp' (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw) operands (op.getSuccessors! ctx.raw) before
        (op.getRegions! ctx.raw)) (.ok (results, after, none))) :
    state'.CTreeEquationLemmaAt (InsertPoint.after op ctx.raw block) := by
  intro observed hobserved hnonterm hdom
  simp [OperationPtr.DominatesIp.after_iff opRooted
    (show block.getParent! ctx.raw = some region by grind)] at hdom
  simp [OperationPtr.dominates_iff_properlyDominates_or_eq] at hdom
  rcases hdom with hdom | hself
  · have heq : state.CTreeEquationHolds observed := by
      apply hprior observed hobserved hnonterm
      grind
    apply heq.setResultValues_of_dominates ctxDom (by grind) opRegion ssa opReachable (by grind) ?_ hset
    grind
  · subst observed
    exact VariableState.ctreeEquationHolds_of_outcome_self ctxDom opRooted opRegion
      (by grind) ssa hoperands hset houtcome

/-- The historical SSA invariant passes from predecessor exit to successor entry. -/
theorem VariableState.CTreeEquationLemmaAt.setArgumentValues_succ_entry
    {ctx : WfIRContext OpCode} {state state' : VariableState ctx}
    {block succ : BlockPtr} {values : Array RuntimeValue} {hsucc : succ.InBounds ctx.raw}
    (ctxDom : ctx.Dom root) (_blockIn : block.InBounds ctx.raw)
    (blockParent : block.getParent! ctx.raw = some region) (hsuccessor : succ ∈ block.getSuccessors! ctx.raw)
    (succParent : succ.getParent! ctx.raw = some region) (ssa : region.hasSSADominance ctx)
    (succRooted : succ.RootedAt root ctx) (succReachable : succ.HierarchicallyReachable ctx)
    (hprior : state.CTreeEquationLemmaAt (InsertPoint.atEnd block))
    (hset : state.setArgumentValues? succ values hsucc = some state') :
    state'.CTreeEquationLemmaAt (InsertPoint.atStart! succ ctx.raw) := by
  intro op hop hnonterm hdom
  have hbefore : op.DominatesIp (InsertPoint.atEnd block) ctx := by
    grind [OperationPtr.DominatesIp.predecessor_exit_of_successor_entry]
  exact (hprior op hop hnonterm hbefore).setArgumentValues_of_dominatesIp
    ctxDom succParent ssa succRooted succReachable hdom hset

/-- Once a historical opcode is known not to modify memory, its historical event directly supplies
an existential unchanged-memory outcome. No independence from other memory states is needed. -/
theorem VariableState.CTreeEquationHolds.witness_of_memory_preserving
    {ctx : WfIRContext OpCode} {state : VariableState ctx} {op : OperationPtr}
    (heq : state.CTreeEquationHolds op)
    (hmem : ∀ operands results before after,
      PureOrErr.CanInterpretTo
        (CTree.interpretOp' (op.getOpType! ctx.raw)
          (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
          (op.getResultTypes! ctx.raw) operands (op.getSuccessors! ctx.raw) before
          (op.getRegions! ctx.raw)) (.ok (results, after, none)) → after = before) :
    ∃ operands results memory,
      state.getOperandValues op = some operands ∧
      (op.getResults! ctx.raw).mapM state.getVar? = some results ∧
      PureOrErr.CanInterpretTo
        (CTree.interpretOp' (op.getOpType! ctx.raw)
          (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
          (op.getResultTypes! ctx.raw) operands (op.getSuccessors! ctx.raw) memory
          (op.getRegions! ctx.raw)) (.ok (results, memory, none)) := by
  obtain ⟨operands, results, before, after, ho, hr, ht⟩ := heq
  have hm := hmem operands results before after ht
  subst after
  exact ⟨operands, results, before, ho, hr, ht⟩

/-- The invariant initially holds whenever no operation can dominate the initial point.
The premise is structural, rather than a collection of assumed matching equations. -/
theorem VariableState.ctreeEquationLemmaAt_initial {ctx : WfIRContext OpCode}
    (state : VariableState ctx) (location : InsertPoint)
    (hentry : ∀ (op : OperationPtr), op.InBounds ctx.raw →
      HasOpInfo.isTerminator (op.getOpType! ctx.raw) = false → ¬op.DominatesIp location ctx) :
    state.CTreeEquationLemmaAt location := by
  intro op hop hnonterm hdom
  exact False.elim (hentry op hop hnonterm hdom)

end

end Veir
