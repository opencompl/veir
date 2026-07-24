module

public import Veir.IR.OpInfo
public import Veir.IR.Basic
public import Veir.GlobalOpInfo
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
          some (.ok (resValues, memory₂, cf)) →
      memory₁ = memory₂ := by
  rw [h operands memory₁ memory₁]
  simp only [Interp.map, Option.map, Interp, UBOr.map]
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
  ∃ controlFlow, interpretOp op state = some (.ok (state, controlFlow))

theorem interpretOp_equationHolds_self
    {ctx : WfIRContext OpCode} {state state' : InterpreterState ctx} (ctxDom : ctx.Dom)
    (opAcyclic : op.OperandsAreDominanceAcyclic ctx)
    (inBounds : op.InBounds ctx.raw) :
    op.Pure ctx →
    interpretOp op state = some (.ok (state', controlFlow)) →
    state'.EquationHolds op := by
  simp only [InterpreterState.EquationHolds]
  grind [OperationPtr.Pure.interpretOp'_eq_ok_implies_memory_eq, interpretOp_some_iff]

theorem interpretOp_equationHolds_other
    {ctx : WfIRContext OpCode} {state state' : InterpreterState ctx} (ctxDom : ctx.Dom)
    (op₂Acyclic : op₂.OperandsAreDominanceAcyclic ctx)
    {inBounds₁ : op₁.InBounds ctx.raw} {inBounds₂ : op₂.InBounds ctx.raw} :
    op₂.Pure ctx →
    interpretOp op₁ state inBounds₁ = some (.ok (state', cf₁)) →
    op₂.Dominates op₁ ctx →
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
    ctxDom op₂Acyclic hDom hResValues₁]
  simp only [hOperandValues₂, OperationPtr.interpret]
  rw [OperationPtr.Pure.interpretOp'_eq_interpretOp'_other_memory op₂Pure memory₂]
  simp only [hInterp₂', Interp.map, Option.map, UBOr.map]
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
    (ctxDom : ctx.Dom)
    (opDominatingOperandsAcyclic : op.DominatingOperandUsesAreWellFounded ctx)
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) opInBounds)
    (opHasParent : (op.get! ctx.raw).parent = some block) :
    interpretOp op state = some (.ok (state', controlFlow)) →
    state'.EquationLemmaAt (InsertPoint.after op ctx.raw block) := by
  intro hInterp
  simp only [InterpreterState.EquationLemmaAt] at stateWf ⊢
  intro op' op'InBounds hPure hDom
  simp [OperationPtr.dominatesIp_iff] at hDom
  simp [OperationPtr.dominates_iff_strictlyDominates_or_eq] at hDom
  rcases hDom with hDom | hDom
  · apply interpretOp_equationHolds_other ctxDom
      (opDominatingOperandsAcyclic.of_dominates hDom.1) (by grind) hInterp
    · grind [OperationPtr.dominates_of_strictlyDominates]
    · grind [interpretOp_equationHolds_other]
    · grind
  · subst op'
    exact interpretOp_equationHolds_self ctxDom
      opDominatingOperandsAcyclic.self opInBounds hPure hInterp

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

/-- All operands operation in a well-dominated program exist in a state that is `DefinesDominating`
right before the operation. -/
theorem InterpreterState.DefinesDominating.exists_getOperandValues_eq_some
    {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom) {state : InterpreterState ctx}
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    (opReachable : op.ReachableFromEntry ctx)
    (stateDom : state.DefinesDominating (InsertPoint.before op) opInBounds) :
    ∃ val, state.variables.getOperandValues op = some val := by
  simp only [VariableState.getOperandValues, Array.exists_mapM_option_eq_some_iff]
  intro i hi
  apply InterpreterState.DefinesDominating.exists_getVar_of_dominatesIp stateDom (by grind)
  grind [WfIRContext.Dom.operand_dominates_op]

/-- `InterpreterState.DefinesDominating` is preserved when interpreting an operation: if every value
dominating the program point *before* `op` is available in `state`, then after running `op` every
value dominating the point *after* `op` is available in the resulting state. -/
theorem interpretOp_DefinesDominating {ctx : WfIRContext OpCode} {opInBounds}
    (ctxDom : ctx.Dom) {state state' : InterpreterState ctx}
    (stateDom : state.DefinesDominating (InsertPoint.before op) opInBounds)
    (opHasParent : (op.get! ctx.raw).parent = some block)
    {region : RegionPtr}
    (blockParent : (block.get! ctx.raw).parent = some region) :
    interpretOp op state = some (.ok (state', controlFlow)) →
    state'.DefinesDominating (InsertPoint.after op ctx.raw block) := by
  intro hinterp
  simp only [InterpreterState.DefinesDominating] at stateDom ⊢
  simp only [interpretOp_some_iff] at hinterp
  have ⟨operandValues, resValues, mem', varState', hoperand, hinterp, hresValues, hstate⟩ := hinterp
  subst state'
  intro value valueInBounds valueDom
  cases (WfIRContext.Dom.value_dominatesIp_after_iff ctxDom blockParent).mp valueDom
  case inl =>
    have := stateDom value (by grind) (by grind)
    grind
  case inr =>
    grind [OperationPtr.getResults!.mem_iff_exists_index]

/-- Setting a successor's block arguments preserves `DefinesDominating` in a state satisfying it at
the predecessor's exit. -/
theorem InterpreterState.DefinesDominating.setArgumentValues?_succ_entry
    (ctxDom : ctx.Dom) (ctxVerified : ctx.Verified)
    {exitState : InterpreterState ctx}
    {block : BlockPtr} {region : RegionPtr}
    (blockParent : (block.get! ctx.raw).parent = some region)
    (blockInBounds : block.InBounds ctx.raw)
    (hsucc : succ ∈ block.getSuccessors! ctx.raw)
    (hExit : exitState.DefinesDominating (InsertPoint.atEnd block))
    (hArgs : exitState.variables.setArgumentValues? succ res succInBounds = some newVars) :
    InterpreterState.DefinesDominating ⟨newVars, exitState.memory⟩ (InsertPoint.atStart! succ ctx.raw) := by
  intro value valueInBounds valueDom
  cases WfIRContext.Dom.value_dominatesIp_successor_entry
    ctxDom ctxVerified blockParent blockInBounds hsucc valueDom
  · grind [InterpreterState.DefinesDominating]
  · grind [BlockPtr.getArguments!.mem_iff_exists_index]

/-- `EquationHolds` for an `op` dominating `succ`'s entry is preserved when setting `succ`'s block
arguments. -/
theorem InterpreterState.EquationHolds.setArgumentValues?_of_dominatesIp
    (opBlockArgumentsAcyclic : op.BlockArgumentUsesAreDominanceAcyclic ctx)
    (opDom : op.DominatesIp (InsertPoint.atStart! succ ctx.raw) ctx)
    {exitState : InterpreterState ctx} (hEq : exitState.EquationHolds op opIn)
    (hArgs : exitState.variables.setArgumentValues? succ res succInBounds = some newVars) :
    InterpreterState.EquationHolds ⟨newVars, exitState.memory⟩ op := by
  simp only [InterpreterState.EquationHolds] at hEq ⊢
  obtain ⟨cf, hinterp⟩ := hEq
  simp only [interpretOp_some_iff] at hinterp ⊢
  grind [VariableState.getOperandValues_eq_of_getVar?_eq,
      VariableState.getVar?_setArgumentValues?_of_notMem_getArguments!,
      OperationPtr.BlockArgumentUsesAreDominanceAcyclic,
      → VariableState.setResultValues?_setArgumentValues?_comm]

/-- Setting a successor's block arguments preserves `EquationLemmaAt` in a state satisfying it at
the predecessor's exit. -/
theorem InterpreterState.EquationLemmaAt.setArgumentValues?_succ_entry
    (ctxVerified : ctx.Verified)
    {block : BlockPtr} {region : RegionPtr}
    (blockParent : (block.get! ctx.raw).parent = some region)
    (blockInBounds : block.InBounds ctx.raw)
    (hsucc : succ ∈ block.getSuccessors! ctx.raw)
    (dominatingOpsBlockArgumentsAcyclic : ∀ {op : OperationPtr},
      op.InBounds ctx.raw →
      op.DominatesIp (InsertPoint.atStart! succ ctx.raw) ctx →
      op.BlockArgumentUsesAreDominanceAcyclic ctx)
    {exitState : InterpreterState ctx}
    (hExit : exitState.EquationLemmaAt (InsertPoint.atEnd block))
    (hArgs : exitState.variables.setArgumentValues? succ res succInBounds = some newVars) :
    InterpreterState.EquationLemmaAt ⟨newVars, exitState.memory⟩
      (InsertPoint.atStart! succ ctx.raw) := by
  intro op opIn hPure hDom
  have opDomAtEnd : op.DominatesIp (InsertPoint.atEnd block) ctx := by
    exact ctxVerified.op_dominatesIp_successor_entry
      blockParent blockInBounds hsucc hDom
  have := hExit op opIn hPure opDomAtEnd
  have opBlockArgumentsAcyclic :
      op.BlockArgumentUsesAreDominanceAcyclic ctx :=
    dominatingOpsBlockArgumentsAcyclic opIn hDom
  exact InterpreterState.EquationHolds.setArgumentValues?_of_dominatesIp
    opBlockArgumentsAcyclic hDom this hArgs

/-- Interpreting a verified operation never fails on a state satisfying `DefinesDominating` at the
operation's location. -/
theorem InterpreterState.DefinesDominating.interpretOp_ne_none
    (ctxDom : ctx.Dom) (opInBounds : op.InBounds ctx.raw) {state : InterpreterState ctx}
    (opReachable : op.ReachableFromEntry ctx)
    (stateDom : state.DefinesDominating (InsertPoint.before op) opInBounds)
    (opVerif : op.Verified ctx opInBounds) :
    ∃ state', interpretOp op state opInBounds = some state' := by
  simp only [interpretOp]
  have ⟨operandValues, hOperandValues⟩ :=
    stateDom.exists_getOperandValues_eq_some ctxDom opInBounds opReachable
  simp only [hOperandValues]
  have hconforms : RuntimeValue.ArrayConforms operandValues (op.getOperandTypes! ctx.raw) := by
    grind [VariableState.getOperandValues_conforms]
  have ⟨resValues, hresValues⟩ := exists_interpretOp'_eq_some opVerif hconforms state.memory
  simp only [hresValues, bind]
  rcases resValues with ⟨resValues, mem', act⟩ | _
  · simp only [liftM, monadLift, MonadLift.monadLift, pure, Interp]
    have := interpretOp'_results_conform opVerif hconforms hresValues
    have ⟨v, hv⟩ :=
      (VariableState.setResultValues?_isSome_iff_conforms state.variables opInBounds).mp this
    simp [hv]
  · simp [Interp]

/-- `interpretOpList` never fails (returns `none`) on a slice of an operation chain given a verified
and well-dominated context, on an interpreter state containing all values dominating the first
operation in the slice. -/
theorem InterpreterState.DefinesDominating.interpretOpList_ne_none
    (ctxVerif : ctx.Verified) (ctxDom : ctx.Dom)
    {block : BlockPtr} {region : RegionPtr}
    (blockParent : (block.get! ctx.raw).parent = some region)
    (hChain : block.OpChainSlice ctx.raw ops)
    (opsReachable : ∀ op, op ∈ ops → op.ReachableFromEntry ctx)
    {state : InterpreterState ctx}
    (stateDom : ∀ head, (hhead : ops.head? = some head) →
      state.DefinesDominating (.before head) (by grind [List.mem_of_head? hhead])) :
    interpretOpList ops state ≠ none := by
  induction ops generalizing state with
  | nil => simp
  | cons a l ih =>
    have hDom : state.DefinesDominating (.before a) := stateDom a (by simp)
    obtain ⟨headInBounds, headParent, headNext, hChainTail⟩ := hChain
    simp only [interpretOpList_cons]
    rcases hi : interpretOp a state (by grind) with _ | (⟨s, act⟩ | _)
    · have aReachable : a.ReachableFromEntry ctx := opsReachable a (by simp)
      grind [InterpreterState.DefinesDominating.interpretOp_ne_none ctxDom]
    · grind [interpretOp_DefinesDominating ctxDom hDom headParent blockParent hi]
    · simp

/-- If the equation lemma holds at the point *before* an operation chain, interpreting the chain
keeps the equation lemma valid at the point *after* the chain. -/
theorem interpretOpList_equationLemmaAt {ctx : WfIRContext OpCode}
    {state state' : InterpreterState ctx} (ctxDom : ctx.Dom)
    {block : BlockPtr} (hChain : block.OpChainSlice ctx.raw ops)
    (opsAcyclic : ∀ op, op ∈ ops → op.DominatingOperandUsesAreWellFounded ctx)
    (hfstElem : ops.head? = some fstOp)
    (eqLemma : state.EquationLemmaAt (.before fstOp) (by
      grind [List.head?_eq_getElem?, hChain.inBounds_of_mem]))
    (hLastElem : ops.getLast? = some lastOp)
    (hrun : interpretOpList ops state (by grind) = some (.ok (state', none))) :
    state'.EquationLemmaAt (InsertPoint.after lastOp ctx.raw block) := by
  induction ops generalizing state fstOp with
  | nil => grind
  | cons head tail ih =>
    obtain ⟨headInBounds, headParent, headNext, hChainTail⟩ := hChain
    have : head = fstOp := by grind
    subst head
    simp only [interpretOpList_cons] at hrun
    rcases hi : interpretOp fstOp state headInBounds with _ | (⟨s, act⟩ | _) <;>
      simp only [hi] at hrun
    · simp at hrun
    · have hAfter := interpretOp_equationLemmaAt ctxDom
        (opsAcyclic fstOp (by simp)) eqLemma headParent hi
      cases act with
      | some cf =>
        change some (UBOr.ok (s, some cf)) =
          some (UBOr.ok (state', none)) at hrun
        have pairEq : (s, some cf) = (state', none) :=
          UBOr.ok.inj (Option.some.inj hrun)
        nomatch congrArg Prod.snd pairEq
      | none =>
        change interpretOpList tail s (by grind) =
          some (UBOr.ok (state', none)) at hrun
        cases tail with
        | nil =>
          have pairEq : (s, none) = (state', none) :=
            UBOr.ok.inj (Option.some.inj hrun)
          have stateEq : s = state' := congrArg Prod.fst pairEq
          have lastEq : fstOp = lastOp := by simpa using hLastElem
          subst state'
          subst lastOp
          exact hAfter
        | cons next rest =>
          have nextEq : (fstOp.get! ctx.raw).next = some next :=
            headNext next rfl
          have hAfterNext :
              s.EquationLemmaAt (InsertPoint.before next) := by
            change ∀ op (opIn : op.InBounds ctx.raw), op.Pure ctx →
              op.DominatesIp (InsertPoint.before next) ctx →
                s.EquationHolds op opIn
            intro op opIn opPure opDom
            change ∀ op (opIn : op.InBounds ctx.raw), op.Pure ctx →
              op.DominatesIp
                (InsertPoint.after fstOp ctx.raw block headParent headInBounds) ctx →
                s.EquationHolds op opIn at hAfter
            apply hAfter op opIn opPure
            simpa only [InsertPoint.after_eq_of_some_next nextEq] using opDom
          exact ih (state := s) (fstOp := next) hChainTail
            (fun op opMem => opsAcyclic op (by simp [opMem]))
            (hfstElem := rfl) hAfterNext hLastElem hrun
    · nomatch Option.some.inj hrun

/-- If `DefinesDominating` holds at the point *before* an operation chain, interpreting the chain
keeps `DefinesDominating` at the point *after* the chain. -/
theorem interpretOpList_DefinesDominating {ctx : WfIRContext OpCode}
    {state state' : InterpreterState ctx} (ctxDom : ctx.Dom)
    {block : BlockPtr} {region : RegionPtr}
    (blockParent : (block.get! ctx.raw).parent = some region)
    (hChain : block.OpChainSlice ctx.raw ops)
    (head : ops.head? = some fstOp)
    (stateDom : state.DefinesDominating (.before fstOp) (by
      grind [List.head?_eq_getElem?, hChain.inBounds_of_mem]))
    (hLastElem : ops.getLast? = some lastOp)
    (hrun : interpretOpList ops state (by grind) = some (.ok (state', none))) :
    state'.DefinesDominating (InsertPoint.after lastOp ctx.raw block) := by
  induction ops generalizing state fstOp with
  | nil => simp at hLastElem
  | cons a tail ih =>
    obtain ⟨headInBounds, headParent, headNext, hChainTail⟩ := hChain
    obtain rfl : a = fstOp := by simpa using head
    simp only [interpretOpList_cons] at hrun
    rcases hi : interpretOp a state headInBounds with _ | (⟨s, act⟩ | _) <;>
      simp only [hi] at hrun
    · simp at hrun
    · cases act
      case none =>
        have hAfter := interpretOp_DefinesDominating
          ctxDom stateDom headParent blockParent hi
        cases tail <;> grind
      case some cf => grind
    · grind
