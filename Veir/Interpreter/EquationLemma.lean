module

public import Veir.Interpreter.Basic
public import Veir.Dominance
public import Veir.Verifier

import Veir.Interpreter.Lemmas

/-!
# Equation Lemma and SSA Invariant

This file contains the definition of the equation lemma (`EquationLemmaAt`) and the proof of
preservation when interpreting an operation.

The equation lemma is based on the paper "A formally verified SSA-based middle-end" from
Gilles Barthe, Delphine Demange, and David Pichardie. Our definition is slightly different as
CompCertSSA semantics are based on small-step operational semantics.
-/

namespace Veir
public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-!
## Equation Lemma
-/

/--
An operation is *pure* when its interpretation does not depend on, and does not modify, the
memory state: running it under any memory yields the same result values and control flow, with
the memory threaded through unchanged.

Concretely, the result under `memory₁` is the result under `memory₂` with the output memory
rewritten to the input memory.
-/
def OperationPtr.Pure (op : OperationPtr) (ctx : IRContext OpCode) : Prop :=
  ∀ operands memory₁ memory₂,
    interpretOp' (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
      (op.getResultTypes! ctx) operands (op.getSuccessors! ctx) memory₁ =
    (interpretOp' (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
      (op.getResultTypes! ctx) operands (op.getSuccessors! ctx) memory₂ |>.map
      (fun (r, _, cf) => (r, memory₁, cf)))

namespace OperationPtr.Pure

variable {op : OperationPtr} {ctx : IRContext OpCode}

theorem interpretOp'_eq_interpretOp'_other_memory
    (opPure : op.Pure ctx) (memory₂ : MemoryState) :
      interpretOp' (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
        (op.getResultTypes! ctx) operands (op.getSuccessors! ctx) memory₁ =
      (interpretOp' (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
        (op.getResultTypes! ctx) operands (op.getSuccessors! ctx) memory₂ |>.map
      (fun (r, _, cf) => (r, memory₁, cf))) := by
  grind [Pure]

theorem interpretOp'_eq_ok_implies_memory_eq (h : op.Pure ctx) :
      interpretOp' (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
        (op.getResultTypes! ctx) operands (op.getSuccessors! ctx) memory₁ =
          .ok (resValues, memory₂, cf) →
      memory₁ = memory₂ := by
  rw [h operands memory₁ memory₁]
  simp only [Interp.map]
  grind

end OperationPtr.Pure

/--
`state.EquationHolds ctx op` holds when `state` records the result of interpreting `op`.
This is encoded by stating that interpreting `op` in `state` produces `state` itself, which is
equivalent to saying that the results of interpreting `op` on the given `state` are present in
`state` itself.
-/
def InterpreterState.EquationHolds {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (op : OperationPtr) (inBounds : op.InBounds ctx.raw := by grind) : Prop :=
  ∃ controlFlow, interpretOp op state = .ok (state, controlFlow)

theorem interpretOp_equationHolds_self
    {ctx : WfIRContext OpCode} {state state' : InterpreterState ctx} (ctxDom : ctx.Dom root)
    (opRooted : op.RootedAt root ctx)
    (opReachable : op.LocallyReachable region ctx)
    (opRegionSSA : region.hasSSADominance ctx)
    (inBounds : op.InBounds ctx.raw) :
    op.Pure ctx →
    interpretOp op state = .ok (state', controlFlow) →
    state'.EquationHolds op := by
  simp only [InterpreterState.EquationHolds]
  grind [OperationPtr.Pure.interpretOp'_eq_ok_implies_memory_eq, interpretOp_some_iff]

theorem interpretOp_equationHolds_other
    {ctx : WfIRContext OpCode} {state state' : InterpreterState ctx} (ctxDom : ctx.Dom root)
    (op₂Rooted : op₂.RootedAt root ctx)
    (op₁Region : op₁.getParentRegion! ctx.raw = some region)
    (op₁RegionSSA : region.hasSSADominance ctx)
    (op₁Reachable : op₁.HierarchicallyReachable ctx)
    {inBounds₁ : op₁.InBounds ctx.raw} {inBounds₂ : op₂.InBounds ctx.raw} :
    op₂.Pure ctx →
    interpretOp op₁ state inBounds₁ = .ok (state', cf₁) →
    op₂.Dominates op₁ ctx false →
    state.EquationHolds op₂ →
    state'.EquationHolds op₂ := by
  intro op₂Pure hInterp₁ hDom
  simp only [InterpreterState.EquationHolds]
  rintro ⟨cf₂, hInterp₂⟩
  exists cf₂
  have ⟨operandValues₁, resValues₁, memory₁, resState₂, hOperandValues₁, hInterp₁', hResValues₁, hState'⟩ := interpretOp_some_iff.mp hInterp₁
  have ⟨operandValues₂, resValues₂, memory₂, resState₁, hOperandValues₂, hInterp₂', hResValues₂, hState⟩ := interpretOp_some_iff.mp hInterp₂
  subst state state'; simp_all only
  simp only [interpretOp, bind, pure, liftM, monadLift, MonadLift.monadLift]
  simp only [VariableState.getOperandValues_setResultValues?_of_dominates
    ctxDom op₂Rooted hDom op₁Region op₁RegionSSA op₁Reachable hResValues₁]
  simp only [hOperandValues₂, OperationPtr.interpret]
  rw [OperationPtr.Pure.interpretOp'_eq_interpretOp'_other_memory op₂Pure memory₂]
  simp only [hInterp₂', Interp.map]
  by_cases hOp : op₂ = op₁
  · grind
  · have := VariableState.setResultValues?_comm hOp hResValues₂ hResValues₁
    grind

/-!
## SSA Invariant at a Program Point
-/

/--
An interpreter state satisfies the SSA invariant at a program point if it satisfies the equation
lemma for all operations that dominate that program point.
In other words, all operations that dominate the given location have already been interpreted and
their results are present in the state.
-/
def InterpreterState.EquationLemmaAt {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (location : InsertPoint) (_locInBounds : location.InBounds ctx.raw := by grind) : Prop :=
  ∀ (op : OperationPtr) (_opInBounds : op.InBounds ctx.raw),
  op.Pure ctx →
  op.DominatesIp location ctx →
  state.EquationHolds op

theorem interpretOp_equationLemmaAt {ctx : WfIRContext OpCode} {opInBounds} {state state' : InterpreterState ctx}
    (ctxDom : ctx.Dom root) (opRooted : op.RootedAt root ctx)
    (opRegion : op.getParentRegion! ctx.raw = some region)
    (opRegionSSA : region.hasSSADominance ctx)
    (opReachable : op.HierarchicallyReachable ctx)
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) opInBounds)
    (opHasParent : op.getParent! ctx.raw = some block) :
    interpretOp op state = .ok (state', controlFlow) →
    state'.EquationLemmaAt (InsertPoint.after op ctx.raw block) := by
  intro hInterp
  simp only [InterpreterState.EquationLemmaAt] at stateWf ⊢
  intro op' op'InBounds hPure hDom
  simp [OperationPtr.DominatesIp.after_iff] at hDom
  simp [OperationPtr.dominates_iff_properlyDominates_or_eq] at hDom
  rcases hDom with hDom | hDom
  · grind [interpretOp_equationHolds_other]
  · grind [interpretOp_equationHolds_self]

/-- An interpreter state satisfies the `DefinesDominating` invariant at a program point if it
defines all values that dominate that program point. This should be satisfied by any state in the
interpreter. -/
def InterpreterState.DefinesDominating {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (location : InsertPoint) (_locInBounds : location.InBounds ctx.raw := by grind) : Prop :=
  ∀ (value : ValuePtr) (_valueInBounds : value.InBounds ctx.raw),
  value.DominatesIp location ctx →
  (state.variables.getVar? value).isSome

/-- Getting a dominating value from a state satisfying `DefinesDominating` at a program point is
always successful. -/
theorem InterpreterState.DefinesDominating.isSome_getVar_of_dominatesIp
    {state : InterpreterState ctx}
    (eqLemma : state.DefinesDominating location locInBounds)
    {value : ValuePtr} (valueInBounds : value.InBounds ctx.raw)
    (valueDom : value.DominatesIp location ctx) :
    (state.variables.getVar? value).isSome := by
  grind [InterpreterState.DefinesDominating]

/-- Getting a dominating value from a state satisfying `DefinesDominating` at a program point is
always successful. -/
theorem InterpreterState.DefinesDominating.exists_getVar_of_dominatesIp
    {state : InterpreterState ctx}
    (eqLemma : state.DefinesDominating location locInBounds)
    {value : ValuePtr} (valueInBounds : value.InBounds ctx.raw)
    (valueDom : value.DominatesIp location ctx) :
    ∃ val, state.variables.getVar? value = some val := by
  simp only [← Option.isSome_iff_exists]
  grind [InterpreterState.DefinesDominating.isSome_getVar_of_dominatesIp]

/-- All operands of a locally reachable operation in a well-dominated program exist in a state
that is `DefinesDominating` right before the operation. -/
theorem InterpreterState.DefinesDominating.exists_getOperandValues_eq_some
    (ctxDom : ctx.Dom root) (opInRoot : root.Ancestor op ctx) {state : InterpreterState ctx}
    (opReachable : op.LocallyReachable region ctx)
    (stateDom : state.DefinesDominating (InsertPoint.before op) opInBounds) :
    ∃ val, state.variables.getOperandValues op = some val := by
  simp only [VariableState.getOperandValues, Array.exists_mapM_option_eq_some_iff]
  intro i hi
  apply InterpreterState.DefinesDominating.exists_getVar_of_dominatesIp stateDom (by grind)
  grind [WfIRContext.Dom.operand_dominatesIp_before]

/-- `InterpreterState.DefinesDominating` is preserved when interpreting an operation: if every value
dominating the program point *before* `op` is available in `state`, then after running `op` every
value dominating the point *after* `op` is available in the resulting state. -/
theorem interpretOp_DefinesDominating {ctx : WfIRContext OpCode} {opInBounds}
    {state state' : InterpreterState ctx}
    (stateDom : state.DefinesDominating (InsertPoint.before op) opInBounds)
    (opHasParent : op.getParent! ctx.raw = some block) :
    interpretOp op state = .ok (state', controlFlow) →
    state'.DefinesDominating (InsertPoint.after op ctx.raw block) := by
  intro hinterp
  simp only [InterpreterState.DefinesDominating] at stateDom ⊢
  simp only [interpretOp_some_iff] at hinterp
  have ⟨operandValues, resValues, mem', varState', hoperand, hinterp, hresValues, hstate⟩ := hinterp
  subst state'
  intro value valueInBounds valueDom
  cases ValuePtr.DominatesIp.after_iff.mp valueDom
  case inl =>
    have := stateDom value (by grind) (by grind)
    grind
  case inr =>
    grind [OperationPtr.getResults!.mem_iff_exists_index]

/-- Setting a successor's block arguments preserves `DefinesDominating` in a state satisfying it at
the predecessor's exit. -/
theorem InterpreterState.DefinesDominating.setArgumentValues?_succ_entry
    {exitState : InterpreterState ctx}
    {block : BlockPtr} (blockInBounds : block.InBounds ctx.raw)
    (blockParent : block.getParent! ctx.raw = some region)
    (succParent : succ.getParent! ctx.raw = some region)
    (regionSSA : region.hasSSADominance ctx)
    (hsucc : succ ∈ block.getSuccessors! ctx.raw)
    (hExit : exitState.DefinesDominating (InsertPoint.atEnd block))
    (hArgs : exitState.variables.setArgumentValues? succ res succInBounds = some newVars) :
    InterpreterState.DefinesDominating ⟨newVars, exitState.memory⟩ (InsertPoint.atStart! succ ctx.raw) := by
  intro value valueInBounds valueDom
  cases ValuePtr.DominatesIp.predecessor_exit_of_successor_entry
    blockParent succParent regionSSA hsucc valueDom
  · grind [InterpreterState.DefinesDominating]
  · grind [BlockPtr.getArguments!.mem_iff_exists_index]

/-- `EquationHolds` for an `op` dominating `succ`'s entry is preserved when setting `succ`'s block
arguments, provided `succ` is hierarchically reachable. -/
theorem InterpreterState.EquationHolds.setArgumentValues?_of_dominatesIp (ctxDom : ctx.Dom root)
    {region : RegionPtr}
    (succParent : succ.getParent! ctx.raw = some region)
    (ssa : region.hasSSADominance ctx = true)
    (succRooted : succ.RootedAt root ctx)
    (succReachable : succ.HierarchicallyReachable ctx)
    (opDom : op.DominatesIp (InsertPoint.atStart! succ ctx.raw) ctx)
    {exitState : InterpreterState ctx} (hEq : exitState.EquationHolds op opIn)
    (hArgs : exitState.variables.setArgumentValues? succ res succInBounds = some newVars) :
    InterpreterState.EquationHolds ⟨newVars, exitState.memory⟩ op := by
  simp only [InterpreterState.EquationHolds] at hEq ⊢
  obtain ⟨cf, hinterp⟩ := hEq
  simp only [interpretOp_some_iff] at hinterp ⊢
  have opRooted : op.RootedAt root ctx := by grind
  have opReachable : op.HierarchicallyReachable ctx := by grind
  have ipParent : (InsertPoint.atStart! succ ctx.raw).block! ctx.raw = some succ := by
    grind
  obtain ⟨opRegion, opParentRegion⟩ := opDom.exists_parentRegion ipParent succParent
  have succLocallyReachable : succ.LocallyReachable region ctx := by grind
  have argumentsNotDominating : ∀ value, value ∈ succ.getArguments! ctx.raw →
      ¬ value.DominatesIp (InsertPoint.before op) ctx := by grind
  grind [VariableState.getOperandValues_eq_of_getVar?_eq,
      VariableState.getVar?_setArgumentValues?_of_notMem_getArguments!,
      → VariableState.setResultValues?_setArgumentValues?_comm]

/-- Setting a successor's block arguments preserves `EquationLemmaAt` in a state satisfying it at
the predecessor's exit, provided the successor is hierarchically reachable. -/
theorem InterpreterState.EquationLemmaAt.setArgumentValues?_succ_entry (ctxDom : ctx.Dom root)
    {block : BlockPtr} {region : RegionPtr} (blockInBounds : block.InBounds ctx.raw)
    (blockParent : block.getParent! ctx.raw = some region)
    (hsucc : succ ∈ block.getSuccessors! ctx.raw)
    (succParent : succ.getParent! ctx.raw = some region)
    (ssa : region.hasSSADominance ctx = true)
    (succRooted : succ.RootedAt root ctx)
    (succReachable : succ.HierarchicallyReachable ctx)
    {exitState : InterpreterState ctx}
    (hExit : exitState.EquationLemmaAt (InsertPoint.atEnd block))
    (hArgs : exitState.variables.setArgumentValues? succ res succInBounds = some newVars) :
    InterpreterState.EquationLemmaAt ⟨newVars, exitState.memory⟩
      (InsertPoint.atStart! succ ctx.raw) := by
  intro op opIn hPure hDom
  have opDomAtEnd : op.DominatesIp (InsertPoint.atEnd block) ctx := by
    grind [OperationPtr.DominatesIp.predecessor_exit_of_successor_entry]
  have := hExit op opIn hPure opDomAtEnd
  grind [InterpreterState.EquationHolds.setArgumentValues?_of_dominatesIp]

/-- Interpreting a locally reachable verified operation never fails on a state satisfying
`DefinesDominating` at the operation's location. -/
theorem InterpreterState.DefinesDominating.interpretOp_ne_fail
    (ctxDom : ctx.Dom root) (opInRoot : root.Ancestor op ctx) {state : InterpreterState ctx}
    (opReachable : op.LocallyReachable region ctx)
    (stateDom : state.DefinesDominating (InsertPoint.before op) ipInBounds)
    (opVerif : op.Verified ctx opInBounds) :
    (interpretOp op state opInBounds).isFail = false := by
  simp only [interpretOp, Interp.isFail_withBlame]
  have ⟨operandValues, hOperandValues⟩ :=
    stateDom.exists_getOperandValues_eq_some ctxDom opInRoot opReachable
  simp only [hOperandValues]
  have hconforms : RuntimeValue.ArrayConforms operandValues (op.getOperandTypes! ctx.raw) := by
    grind [VariableState.getOperandValues_conforms]
  have hne := interpretOp'_ne_fail opVerif hconforms state.memory
  rcases hresValues : op.interpret ctx operandValues state.memory with _ | _ | ⟨resValues, mem', act⟩
  · simp [hresValues] at hne
  · simp
  · simp only [liftM, monadLift, MonadLift.monadLift]
    have := interpretOp'_results_conform opVerif hconforms hresValues
    have ⟨v, hv⟩ :=
      (VariableState.setResultValues?_isSome_iff_conforms state.variables opInBounds).mp this
    simp [hv]

/-- `interpretOpList` never fails (returns `.fail`) on a slice of an operation chain in a locally
reachable block, given a verified and well-dominated context and an interpreter state containing
all values dominating the first operation in the slice. -/
theorem InterpreterState.DefinesDominating.interpretOpList_ne_fail
    {root : OperationPtr} (ctxVerif : ctx.Verified root) (ctxDom : ctx.Dom root) {block : BlockPtr}
    (blockInRoot : root.Ancestor block ctx)
    (blockReachable : block.LocallyReachable region ctx)
    (hChain : block.OpChainSlice ctx.raw ops)
    {state : InterpreterState ctx}
    (stateDom : ∀ head, (hhead : ops.head? = some head) →
      state.DefinesDominating (.before head) (by grind [List.mem_of_head? hhead])) :
    (interpretOpList ops state).isFail = false := by
  induction ops generalizing state with
  | nil => simp
  | cons a l ih =>
    have hDom : state.DefinesDominating (.before a) := stateDom a (by simp)
    obtain ⟨headInBounds, headParent, headNext, hChainTail⟩ := hChain
    have headInRoot : root.Ancestor a ctx := by
      grind [IRNode.Ancestor.of_ancestor_parent_of_parent_descendant]
    simp only [interpretOpList_cons]
    rcases hi : interpretOp a state (by grind) with _ | _ | ⟨s, act⟩
    · grind [InterpreterState.DefinesDominating.interpretOp_ne_fail]
    · simp
    · grind [interpretOp_DefinesDominating hDom headParent hi]

/-- If the equation lemma holds at the point *before* an operation chain, interpreting the chain
keeps the equation lemma valid at the point *after* the chain. -/
theorem interpretOpList_equationLemmaAt {ctx : WfIRContext OpCode}
    {state state' : InterpreterState ctx} (ctxDom : ctx.Dom root)
    {block : BlockPtr} (blockRooted : block.RootedAt root ctx)
    (blockParent : block.getParent! ctx.raw = some region)
    (regionSSA : region.hasSSADominance ctx)
    (blockReachable : block.HierarchicallyReachable ctx)
    (hChain : block.OpChainSlice ctx.raw ops)
    (hfstElem : ops.head? = some fstOp)
    (eqLemma : state.EquationLemmaAt (.before fstOp) (by
      grind [List.head?_eq_getElem?, hChain.inBounds_of_mem]))
    (hLastElem : ops.getLast? = some lastOp)
    (hrun : interpretOpList ops state (by grind) = .ok (state', none)) :
    state'.EquationLemmaAt (InsertPoint.after lastOp ctx.raw block) := by
  induction ops generalizing state fstOp with
  | nil => grind
  | cons head tail ih =>
    obtain ⟨headInBounds, headParent, headNext, hChainTail⟩ := hChain
    have : head = fstOp := by grind
    subst head
    simp only [interpretOpList_cons] at hrun
    rcases hi : interpretOp fstOp state headInBounds with _ | _ | ⟨s, act⟩ <;>
      simp only [hi] at hrun
    · simp at hrun
    · grind
    · have headRooted : fstOp.RootedAt root ctx := blockRooted.of_parent (by grind)
      have hAfter : s.EquationLemmaAt (InsertPoint.after fstOp ctx.raw block) := by
        grind [interpretOp_equationLemmaAt]
      cases tail <;> grind

/-- If `DefinesDominating` holds at the point *before* an operation chain, interpreting the chain
keeps `DefinesDominating` at the point *after* the chain. -/
theorem interpretOpList_DefinesDominating {ctx : WfIRContext OpCode}
    {state state' : InterpreterState ctx}
    {block : BlockPtr} (hChain : block.OpChainSlice ctx.raw ops)
    (head : ops.head? = some fstOp)
    (stateDom : state.DefinesDominating (.before fstOp) (by
      grind [List.head?_eq_getElem?, hChain.inBounds_of_mem]))
    (hLastElem : ops.getLast? = some lastOp)
    (hrun : interpretOpList ops state (by grind) = .ok (state', none)) :
    state'.DefinesDominating (InsertPoint.after lastOp ctx.raw block) := by
  induction ops generalizing state fstOp with
  | nil => simp at hLastElem
  | cons a tail ih =>
    obtain ⟨headInBounds, headParent, headNext, hChainTail⟩ := hChain
    obtain rfl : a = fstOp := by simpa using head
    simp only [interpretOpList_cons] at hrun
    rcases hi : interpretOp a state headInBounds with _ | _ | ⟨s, act⟩ <;>
      simp only [hi] at hrun
    · simp at hrun
    · grind
    · cases act
      case none =>
        have hAfter := interpretOp_DefinesDominating stateDom headParent hi
        cases tail <;> grind
      case some cf => grind
