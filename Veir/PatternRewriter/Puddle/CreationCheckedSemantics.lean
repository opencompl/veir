module

public import Veir.PatternRewriter.Puddle.CreationOperationSemantics
public import Veir.Interpreter.CTreeStateRefinement
public import Veir.Interpreter.CTreeMemoryPreservation
public import Veir.Interpreter.CTreeResultConformance
import all Veir.IR.Basic
import all Veir.IR.OpCode
import all Veir.IR.OpInfo
import all Veir.GlobalOpInfo
import all Veir.Interpreter.CTree
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.CTreeStateRefinement
import all Veir.Interpreter.VariableState
import all Veir.PatternRewriter.Puddle.CreationOperationSemantics

namespace Veir
public section
open _root_.CTree

/-- Finite primitive computations simulate themselves while retaining their successful outcome witness. -/
theorem PureOrErr.sim_with_outcome {tree : Tree α} (shape : PureOrErr tree) :
    Sim (fun x y => x = y ∧ PureOrErr.CanInterpretTo tree (.ok x)) tree tree := by
  induction shape with
  | ret value => simp [CTree.ret_pure]
  | tau choice branches shapes ih =>
      apply Sim.tau_id
      intro x
      exact (ih x).mono (by
        rintro t s ⟨heq, hw⟩
        exact ⟨heq, .tau choice branches x _ hw⟩)
  | fail => apply Sim.ub; trivial
  | ub => apply Sim.ub; trivial

namespace Puddle.CTree

/-- Retain the final SSA resolver, rather than projecting immediately to replacement values. -/
def interpretCreatedOpsEnriched (ctx : IRContext OpCode) (ops : List OperationPtr)
    (resolve : ValueResolver) (memory : MemoryState) : Tree (ValueResolver × MemoryState) :=
  interpretCreatedOps ctx ops resolve memory (fun r m => pure (r, m))

/-- Checked state execution of a finite operation batch, using the actual operation core. -/
def interpretCreatedOpsChecked (ctx : WfIRContext OpCode) (ops : List OperationPtr)
    (state : InterpreterState ctx) : Tree (InterpreterState ctx) :=
  match ops with
  | [] => pure state
  | op :: ops =>
    if inBounds : op.InBounds ctx.raw then do
      let (next, _) ← Veir.CTree.interpretOpCore op state inBounds
      interpretCreatedOpsChecked ctx ops next
    else fail

/-- The raw resolver agrees with the checked state on every meaningful SSA pointer. -/
def ResolverRealizes (ctx : WfIRContext OpCode) (state : InterpreterState ctx)
    (raw : ValueResolver × MemoryState) : Prop :=
  state.memory = raw.2 ∧ ∀ pointer, pointer.InBounds ctx.raw →
    state.variables.getVar? pointer = raw.1 pointer

private theorem list_mapM_agrees (xs : List α) (f g : α → Option β)
    (agree : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mapM_cons, agree x (by simp), ih (by
        intro y hy; exact agree y (by simp [hy]))]

/-- Valid operand pointers make the raw and checked operand collectors agree. -/
theorem ResolverRealizes.operands {ctx : WfIRContext OpCode} {state : InterpreterState ctx}
    {resolve : ValueResolver} {memory : MemoryState} (realizes : ResolverRealizes ctx state (resolve, memory))
    (op : OperationPtr) (bound : ∀ p ∈ op.getOperands! ctx.raw, p.InBounds ctx.raw) :
    state.variables.getOperandValues op =
      ((op.getOperands! ctx.raw).toList.mapM resolve).map List.toArray := by
  unfold VariableState.getOperandValues
  rw [Array.mapM_eq_mapM_toList]
  congr 1
  exact list_mapM_agrees _ _ _ (fun p hp => realizes.2 p (bound p (by simpa using hp)))

/-- The exact per-primitive obligation needed by checked installation; it quantifies only
successful raw returns on conforming inputs. -/
def CreatedResultsConform (ctx : WfIRContext OpCode) (ops : List OperationPtr) : Prop :=
  ∀ op ∈ ops, ∀ operands memory results after action,
    RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw) →
    PureOrErr.CanInterpretTo
      (Veir.CTree.interpretOp' (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw)) (op.getResultTypes! ctx.raw)
        operands #[] memory) (.ok (results, after, action)) →
    RuntimeValue.ArrayConforms results (op.getResultTypes! ctx.raw)

/-- Raw result updates agree with successful checked installation even if the raw resolver
has arbitrary entries outside the context. -/
theorem ResolverRealizes.setResults {ctx : WfIRContext OpCode}
    {state : InterpreterState ctx} {resolve : ValueResolver} {memory : MemoryState}
    (realizes : ResolverRealizes ctx state (resolve, memory))
    {op : OperationPtr} {values : Array RuntimeValue} {variables : VariableState ctx}
    {hop : op.InBounds ctx.raw}
    (installed : state.variables.setResultValues? op values hop = some variables)
    (after : MemoryState) :
    ResolverRealizes ctx ⟨variables, after⟩ (resolve.setResultsDefault op values, after) := by
  refine ⟨rfl, ?_⟩
  intro pointer hp
  rw [← ValueResolver.setResultsDefault_eq_checked installed pointer hp]
  cases pointer with
  | blockArgument => exact realizes.2 _ hp
  | opResult result =>
      by_cases heq : result.op = op
      · simp [ValueResolver.setResultsDefault, heq]
      · simpa [ValueResolver.setResultsDefault, heq] using realizes.2 (.opResult result) hp

/-- Output verification discharges every checked-result obligation for nonterminator batches. -/
theorem CreatedResultsConform.of_verified {ctx : WfIRContext OpCode} {ops : List OperationPtr}
    (bounds : ∀ op ∈ ops, op.InBounds ctx.raw)
    (verified : ∀ op (member : op ∈ ops), op.Verified ctx (bounds op member))
    (nonterm : ∀ op ∈ ops, (op.getOpType! ctx.raw).isTerminator = false) :
    CreatedResultsConform ctx ops := by
  intro op member operands memory results after action conforms outcome
  have hsucc := Veir.CTree.interpretOp'_successors_irrelevant (op.getOpType! ctx.raw)
    (op.getProperties! ctx.raw (op.getOpType! ctx.raw)) (op.getResultTypes! ctx.raw)
    operands (op.getSuccessors! ctx.raw) #[] memory (op.getRegions! ctx.raw) (nonterm op member)
  apply Veir.CTree.interpretOp'_results_conform (verified op member) conforms
  rw [hsucc]
  exact outcome

/-- Checked execution of the actual operations realizes the enriched raw creation semantics.
The only semantic side condition is checked result conformance on successful primitive returns. -/
theorem sim_interpretCreatedOpsChecked {ctx : WfIRContext OpCode} (ops : List OperationPtr)
    (bounds : ∀ op ∈ ops, op.InBounds ctx.raw)
    (nonterm : ∀ op ∈ ops, (op.getOpType! ctx.raw).isTerminator = false)
    (conforms : CreatedResultsConform ctx ops)
    (state : InterpreterState ctx) (resolve : ValueResolver) (memory : MemoryState)
    (realizes : ResolverRealizes ctx state (resolve, memory)) :
    Sim (ResolverRealizes ctx) (interpretCreatedOpsChecked ctx ops state)
      (interpretCreatedOpsEnriched ctx.raw ops resolve memory) := by
  induction ops generalizing state resolve memory with
  | nil =>
      simpa [interpretCreatedOpsChecked, interpretCreatedOpsEnriched, interpretCreatedOps]
        using realizes
  | cons op ops ih =>
      have hop := bounds op (by simp)
      have getEq := realizes.operands op (by intro p hp; grind)
      unfold interpretCreatedOpsEnriched
      simp only [interpretCreatedOpsChecked, hop, dite_true, interpretCreatedOps,
        interpretCreatedOp, Veir.CTree.interpretOpCore, Veir.CTree.runOpWith]
      cases lookup : (op.getOperands! ctx.raw).toList.mapM resolve with
      | none =>
          simp only [lookup, Option.map_none] at getEq
          simp only [getEq]
          simp [Veir.fail, _root_.CTree.CTree.trigger_def, Bind.bind, _root_.CTree.CTree.bind_vis]
          apply Sim.ub; trivial
      | some operands =>
          simp only [lookup, Option.map_some] at getEq
          simp only [getEq]
          have primitiveEq : Veir.OperationPtr.interpretCTree op hop operands.toArray state.memory =
              Veir.CTree.interpretOp' (op.getOpType! ctx.raw)
                (op.getProperties! ctx.raw (op.getOpType! ctx.raw)) (op.getResultTypes! ctx.raw)
                operands.toArray #[] memory := by
            unfold Veir.OperationPtr.interpretCTree
            rw [realizes.1]
            have codeEq := OperationPtr.getOpType!_eq_getOpType hop
            have propertyEq := OperationPtr.getProperties!_eq_getProperties hop
              (opCode := op.getOpType ctx.raw hop)
              (by simpa only [ofDialect_hasDialectRefl] using codeEq)
            simp only [← propertyEq, ← OperationPtr.getResultTypes!_eq_getResultTypes hop,
              ← OperationPtr.getSuccessors!_eq_getSuccessors hop]
            rw [← codeEq]
            exact Veir.CTree.interpretOp'_successors_irrelevant _ _ _ _ _ _ _ _
              (nonterm op (by simp))

          rw [primitiveEq]
          rw [_root_.CTree.bind_assoc]
          apply Sim.bind _ _ _ _ (PureOrErr.sim_with_outcome
            (Veir.CTree.interpretOp'_pureOrErr _ _ _ _ _ _))
          rintro target source ⟨equal, outcome⟩
          subst source
          have hconf := conforms op (by simp) operands.toArray memory target.1 target.2.1 target.2.2
            (state.variables.getOperandValues_conforms getEq) outcome
          obtain ⟨variables, installed⟩ :=
            (VariableState.setResultValues?_isSome_iff_conforms state.variables hop).mp hconf
          simp only [Veir.CTree.commitOpResults, installed, Pure.pure, Bind.bind,
            _root_.CTree.CTree.bind_ret]
          exact ih (fun x hx => bounds x (by simp [hx]))
            (fun x hx => nonterm x (by simp [hx]))
            (fun x hx => conforms x (by simp [hx]))
            ⟨variables, target.2.1⟩ (resolve.setResultsDefault op target.1) target.2.1
            (realizes.setResults installed target.2.1)

end Puddle.CTree
end
end Veir
