module

public import Veir.Analysis.DataFlow.SCCPSoundness
public import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis
public import Veir.Interfaces.ControlFlowInterfaces
public import Veir.Interpreter.CollectingRefinement
import Veir.Interpreter.Lemmas
import all Veir.Interpreter.VariableState

public section

namespace Veir.SCCP

/-!
# Checking SCCP after solving

`checkFacts` checks a single immutable candidate, independently of the solver's
worklist and subscriptions. `checkFacts_sound` turns acceptance into `Facts.Valid`,
assuming the explicit, local interpreter contracts in `TransfersSound`.

The test is post-fixedness: joining each incoming fact into its stored fact has
no effect. Neither leastness nor monotonicity of the transfers is required.
-/

/-- Executable facts, without worklist, subscription, or materializer metadata. -/
structure Candidate where
  constant : ValuePtr → AbstractConstant
  blockLive : BlockPtr → Bool
  edgeLive : BlockPtr → BlockPtr → Bool

@[expose] def Candidate.toFacts (candidate : Candidate) : Facts where
  constant := candidate.constant
  blockLive := fun block => candidate.blockLive block = true
  edgeLive := fun source target => candidate.edgeLive source target = true

/-- Snapshot the semantic output of the joint SCCP/dead-code solver. Missing
facts mean bottom/dead, exactly as in `Facts.ofDataFlow`. -/
@[expose] def Candidate.ofDataFlow (facts : DataFlowContext) (ctx : WfIRContext OpCode) : Candidate where
  constant := fun value => SparseFact.getElement .sparseConstant value facts
  blockLive := fun block =>
    (facts.getOrMkFact .liveness (.InsertPoint (InsertPoint.atStart! block ctx.raw))).live
  edgeLive := fun source target =>
    (facts.getOrMkFact .liveness (.CFGEdge ⟨source, target⟩)).live

theorem Candidate.ofDataFlow_toFacts (facts : DataFlowContext) (ctx : WfIRContext OpCode) :
    (Candidate.ofDataFlow facts ctx).toFacts = Facts.ofDataFlow facts ctx := rfl

/-- The join-based update would leave the stored value unchanged. -/
@[expose] def Absorbs (stored incoming : AbstractConstant) : Prop :=
  stored ⊔ incoming = stored

instance (stored incoming : AbstractConstant) : Decidable (Absorbs stored incoming) :=
  inferInstanceAs (Decidable (stored ⊔ incoming = stored))

theorem absorbs_iff (stored incoming : AbstractConstant) :
    Absorbs stored incoming ↔ incoming ≤ stored := by
  constructor
  · intro h
    exact h ▸ AbstractConstant.le_join_right stored incoming
  · intro h
    exact AbstractConstant.le_antisymm _ _
      (AbstractConstant.join_le _ _ _ (AbstractConstant.le_refl _) h)
      (AbstractConstant.le_join_left _ _)

theorem Absorbs.covers {stored incoming : AbstractConstant} (h : Absorbs stored incoming)
    {runtime : RuntimeValue} (covered : AbstractConstant.γ incoming runtime) :
    AbstractConstant.γ stored runtime :=
  AbstractConstant.γ_monotone _ _ ((absorbs_iff _ _).mp h) covered

/-- Reuse the actual constant propagation transfer on the candidate's operands. -/
def resultUpdates (ctx : WfIRContext OpCode) (candidate : Candidate) (op : OperationPtr) :
    Array AbstractConstant :=
  SparseConstantPropagation.transfer op
    ((op.getOperands! ctx.raw).map candidate.constant) ctx

/-- Read branch operands from the candidate; bottom delays propagation.
Unlike the solver's literal shortcut, this also uses the candidate for literal
operands. Thus the branch transfer describes *every* state covered by the
candidate, even when a literal's fact has been widened to top. -/
def branchOperands (ctx : WfIRContext OpCode) (candidate : Candidate) (op : OperationPtr) :
    Option (Array (Option RuntimeValue)) :=
  (op.getOperands! ctx.raw).mapM fun operand =>
    match candidate.constant operand with
    | .bottom => none
    | .top => some none
    | .constant value => some (some value)

/-- Edges enabled by rerunning branch selection against this candidate. Unknown
interfaces conservatively enable every syntactic successor. -/
def enabledSuccessors (ctx : WfIRContext OpCode) (candidate : Candidate) (op : OperationPtr) :
    Array BlockPtr :=
  if op.isBranchLike ctx.raw then
    match branchOperands ctx candidate op with
    | none => #[]
    | some operands =>
      match BranchOpInterface.getSuccessorForOperands? op operands ctx.raw with
      | some successor => #[successor]
      | none => op.getSuccessors! ctx.raw
  else op.getSuccessors! ctx.raw

/-- Incoming fact for a successor argument, using the same forwarding interface
and conservative fallback as the sparse analysis. Indices distinguish two
successor occurrences even when they name the same destination block. -/
def argumentUpdate (ctx : WfIRContext OpCode) (candidate : Candidate) (op : OperationPtr)
    (successorIndex argumentIndex : Nat) : AbstractConstant :=
  if (op.getOpType! ctx.raw).isTerminator then
    match BranchOpInterface.getSuccessorOperand? op successorIndex argumentIndex ctx.raw with
    | some operand => candidate.constant operand
    | none => .top
  else .top

/-- External arguments may have any runtime values. Initialization is checked
even if the candidate claims the entry is dead. -/
@[expose] def EntryClosed (ctx : WfIRContext OpCode) (candidate : Candidate) (block : BlockPtr) : Prop :=
  candidate.blockLive block = true ∧
    ∀ i : Fin (block.getNumArguments! ctx.raw),
      Absorbs (candidate.constant (block.getArgument i)) .top

instance : Decidable (EntryClosed ctx candidate block) := by
  unfold EntryClosed
  infer_instance

/-- Constraints generated by a live operation. All result positions are checked;
a malformed transfer array cannot silently truncate the check via `zip`.
Argument propagation checks *every stored live edge*, including edges retained
from an earlier, less precise candidate. -/
@[expose] def OperationClosed (ctx : WfIRContext OpCode) (candidate : Candidate)
    (op : OperationPtr) : Prop :=
  (resultUpdates ctx candidate op).size = op.getNumResults! ctx.raw ∧
  (∀ i : Fin (op.getNumResults! ctx.raw),
    Absorbs (candidate.constant (op.getResult i))
      ((resultUpdates ctx candidate op)[i.val]?.getD .top)) ∧
  (∀ i : Fin (op.getNumRegions! ctx.raw),
    match (((op.get! ctx.raw).regions[i.val]!).get! ctx.raw).firstBlock with
    | none => True
    | some block => EntryClosed ctx candidate block) ∧
  (match (op.get! ctx.raw).parent with
  | none => True
  | some block =>
    (∀ i : Fin (enabledSuccessors ctx candidate op).size,
      candidate.edgeLive block (enabledSuccessors ctx candidate op)[i] = true ∧
      candidate.blockLive (enabledSuccessors ctx candidate op)[i] = true) ∧
    (∀ i : Fin (op.getSuccessors! ctx.raw).size,
      candidate.edgeLive block (op.getSuccessors! ctx.raw)[i] = true →
      candidate.blockLive (op.getSuccessors! ctx.raw)[i] = true ∧
      ∀ j : Fin (((op.getSuccessors! ctx.raw)[i]).getNumArguments! ctx.raw),
        Absorbs (candidate.constant (((op.getSuccessors! ctx.raw)[i]).getArgument j))
          (argumentUpdate ctx candidate op i j)))

instance : Decidable (OperationClosed ctx candidate op) := by
  letI (i : Fin (op.getNumRegions! ctx.raw)) : Decidable
      (match (((op.get! ctx.raw).regions[i.val]!).get! ctx.raw).firstBlock with
      | none => True
      | some block => EntryClosed ctx candidate block) := by
    split <;> infer_instance
  unfold OperationClosed
  split <;> infer_instance

/-- Operations in live blocks generate constraints. External entry initialization
is checked separately: the arena can also contain parser wrappers or detached
roots outside the analyzed program, which must not become implicit entry points. -/
@[expose] def operationLive (ctx : WfIRContext OpCode) (candidate : Candidate)
    (op : OperationPtr) : Bool :=
  match (op.get! ctx.raw).parent with
  | none => false
  | some block => candidate.blockLive block

private def checkOperations (ctx : WfIRContext OpCode) (candidate : Candidate) :
    Except OperationPtr PUnit.{1} :=
  ctx.raw.forOpsDepM fun op _ =>
    if operationLive ctx candidate op = true → OperationClosed ctx candidate op then
      .ok ⟨⟩
    else .error op

/-- Check entry initialization and every operation in the context's finite arena.
No caller-provided operation list can accidentally omit a constraint. The
candidate remains immutable throughout the check. -/
def checkFacts (ctx : WfIRContext OpCode) (candidate : Candidate) (entries : Array BlockPtr) : Bool :=
  decide (∀ i : Fin entries.size, EntryClosed ctx candidate entries[i]) &&
    (checkOperations ctx candidate).isOk

/-- The executable check establishes all initialization and transfer constraints. -/
theorem checkFacts_closed {ctx : WfIRContext OpCode} {candidate : Candidate} {entries}
    (accepted : checkFacts ctx candidate entries = true) :
    (∀ block ∈ entries, EntryClosed ctx candidate block) ∧
    (∀ op, op.InBounds ctx.raw → operationLive ctx candidate op = true →
      OperationClosed ctx candidate op) := by
  simp only [checkFacts, Bool.and_eq_true, decide_eq_true_eq] at accepted
  constructor
  · intro block member
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp member
    exact accepted.1 ⟨i, hi⟩
  · intro op opIn live
    have allChecked : checkOperations ctx candidate = .ok ⟨⟩ := by
      cases h : checkOperations ctx candidate <;> simp_all [Except.isOk, Except.toBool]
    unfold checkOperations at allChecked
    have checked := ctx.raw.forOpsDepM_except_ok allChecked op opIn
    split at checked
    · rename_i closed
      exact closed live
    · contradiction

/-- The remaining dialect/interface proof obligations. These are local transfer
soundness, independent of the solver and of checker acceptance. In particular,
they do not assume that a stored result already covers its runtime value.

`results` relates computed result facts to actual interpretation. `branch`
identifies an enabled successor occurrence and covers the arguments passed on
that occurrence. The latter includes branch selection and operand forwarding;
using only the destination block would lose information on duplicate successors.
-/
structure TransfersSound (ctx : WfIRContext OpCode) : Prop where
  results : ∀ (candidate : Candidate) op (opIn : op.InBounds ctx.raw) state next action,
    candidate.toFacts.CoversState state → interpretOp op state opIn = .ok (next, action) →
    ∀ (i : Fin (op.getNumResults! ctx.raw)) runtime,
      next.variables.getVar? (op.getResult i) = some runtime →
      AbstractConstant.γ ((resultUpdates ctx candidate op)[i.val]?.getD .top) runtime
  branch : ∀ (candidate : Candidate) op (opIn : op.InBounds ctx.raw) state next arguments destination,
    candidate.toFacts.CoversState state →
    interpretOp op state opIn = .ok (next, some (.branch arguments destination)) →
    ∃ i : Fin (op.getSuccessors! ctx.raw).size,
      (op.getSuccessors! ctx.raw)[i] = destination ∧
      destination ∈ enabledSuccessors ctx candidate op ∧
      ∀ j : Fin (destination.getNumArguments! ctx.raw),
        AbstractConstant.γ (argumentUpdate ctx candidate op i j) arguments[j.val]!

private theorem covers_binding {ctx : WfIRContext OpCode} {facts : Facts}
    {state : InterpreterState ctx} {block arguments variables} {blockIn : block.InBounds ctx.raw}
    (covered : facts.CoversState state)
    (incoming : ∀ i : Fin (block.getNumArguments! ctx.raw),
      AbstractConstant.γ (facts.constant (block.getArgument i)) arguments[i.val]!)
    (bound : state.variables.setArgumentValues? block arguments blockIn = some variables) :
    facts.CoversState ⟨variables, state.memory⟩ := by
  intro value runtime observed
  by_cases member : value ∈ block.getArguments! ctx.raw
  · obtain ⟨i, hi, rfl⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp member
    have assigned := VariableState.getVar?_getArgument_of_setArgumentValues? hi bound
    have equal : runtime = arguments[i]! := by simpa [observed] using assigned
    subst runtime
    exact incoming ⟨i, hi⟩
  · exact covered value runtime
      ((VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! member bound).symm.trans observed)

private theorem covers_execution {ctx : WfIRContext OpCode} {candidate : Candidate}
    (transfers : TransfersSound ctx) {op} {opIn : op.InBounds ctx.raw}
    (closed : OperationClosed ctx candidate op) {state next action}
    (covered : candidate.toFacts.CoversState state)
    (executed : interpretOp op state opIn = .ok (next, action)) :
    candidate.toFacts.CoversState next := by
  intro value runtime observed
  by_cases member : value ∈ op.getResults! ctx.raw
  · obtain ⟨i, hi, rfl⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp member
    exact (closed.2.1 ⟨i, hi⟩).covers
      (transfers.results candidate op opIn state next action covered executed ⟨i, hi⟩ runtime observed)
  · obtain ⟨_, _, _, _, _, _, bound, rfl⟩ := interpretOp_some_iff.mp executed
    exact covered value runtime
      ((VariableState.getVar?_setResultValues?_of_notMem_getResults! member bound).symm.trans observed)

/-- **Checked SCCP facts are valid.** The solver is absent from the statement:
any candidate that passes the check is an inductive invariant, provided the
local transfer functions satisfy their interpreter contracts. -/
theorem checkFacts_sound {ctx : WfIRContext OpCode} {candidate : Candidate}
    {functionOp : OperationPtr} {function : FunctionOp ctx.raw functionOp}
    (source : Collecting.FunctionBody function)
    (transfers : TransfersSound ctx)
    (accepted : checkFacts ctx candidate #[source.entry] = true) :
    candidate.toFacts.Valid source.Initial := by
  obtain ⟨entries, operations⟩ := checkFacts_closed accepted
  have entryClosed := entries source.entry (by simp)
  have operationClosed : ∀ block op, op.InBounds ctx.raw →
      (op.get! ctx.raw).parent = some block → candidate.toFacts.blockLive block →
      OperationClosed ctx candidate op := by
    intro block op opIn parent live
    exact operations op opIn (by simpa [operationLive, parent, Candidate.toFacts] using live)
  constructor
  · rintro entry ⟨arguments, memory, rfl⟩
    refine ⟨entryClosed.1, ?_⟩
    intro variables bound
    apply covers_binding (state := ⟨.empty ctx, memory⟩) _ _ bound
    · intro value runtime observed
      simp [VariableState.getVar?, VariableState.empty] at observed
    · intro i
      exact (entryClosed.2 i).covers trivial
  · intro block op opIn state next action parent live covered executed
    exact covers_execution transfers (operationClosed block op opIn parent live) covered executed
  · intro block op opIn state next arguments destination destinationIn parent live covered executed
    have closed := operationClosed block op opIn parent live
    have nextCovered := covers_execution transfers closed covered executed
    obtain ⟨i, destinationEq, enabled, incoming⟩ :=
      transfers.branch candidate op opIn state next arguments destination covered executed
    have edges := closed.2.2.2
    rw [parent] at edges
    obtain ⟨k, hk, selected⟩ := Array.mem_iff_getElem.mp enabled
    have enabledLive := edges.1 ⟨k, hk⟩
    change candidate.edgeLive block (enabledSuccessors ctx candidate op)[k] = true ∧
      candidate.blockLive (enabledSuccessors ctx candidate op)[k] = true at enabledLive
    rw [selected] at enabledLive
    refine ⟨enabledLive.1, enabledLive.2, ?_⟩
    intro variables bound
    apply covers_binding nextCovered _ bound
    intro j
    have forwarded := edges.2 i (by simp [destinationEq, enabledLive.1])
    have absorbed := forwarded.2 ⟨j.val, by simp [destinationEq]⟩
    simp only [destinationEq] at absorbed
    exact absorbed.covers (incoming j)

end Veir.SCCP
