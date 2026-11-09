module

public import Veir.Interpreter.CTreeInterpreter
public import CTree.IterSim
public import Veir.Interpreter.CTreeOpcodeLemmas
import all CTree.Interp
import all CTree.Iter
import all CTree.Defs
import all CTree.Effect
public import Veir.Interpreter.Refinement.Monotonicity
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.CTree
import all Veir.Interpreter.Refinement.Basic

public section

namespace Veir

namespace CTree

theorem interp_ret_eq {EIn FIn CIn α : Type}
    {E : EIn → Type} {F : FIn → Type} {C : CIn → Type}
    (handler : (e : EIn) → _root_.CTree.CTree F C (E e)) (value : α) :
    _root_.CTree.interp handler (_root_.CTree.CTree.ret value) = pure value := by
  unfold _root_.CTree.interp
  rw [_root_.CTree.iter.eq_def]
  simp

theorem interp_tau_eq {EIn FIn CIn α : Type}
    {E : EIn → Type} {F : FIn → Type} {C : CIn → Type}
    (handler : (e : EIn) → _root_.CTree.CTree F C (E e))
    (choice : _root_.CTree.C1In ⊕ CIn)
    (next : (_root_.CTree.C1 ⊕ₑ C) choice → _root_.CTree.CTree E C α) :
    _root_.CTree.interp handler (_root_.CTree.CTree.tauG choice next) =
      _root_.CTree.CTree.tauG choice (fun x =>
        _root_.CTree.CTree.tau1 (_root_.CTree.interp handler (next x))) := by
  unfold _root_.CTree.interp
  rw [_root_.CTree.iter.eq_def]
  simp

theorem interp_vis_eq {EIn FIn CIn α : Type}
    {E : EIn → Type} {F : FIn → Type} {C : CIn → Type}
    (handler : (e : EIn) → _root_.CTree.CTree F C (E e)) (event : EIn)
    (next : E event → _root_.CTree.CTree E C α) :
    _root_.CTree.interp handler (_root_.CTree.CTree.vis event next) =
      (handler event >>= fun x =>
        _root_.CTree.CTree.tau1 (_root_.CTree.interp handler (next x))) := by
  unfold _root_.CTree.interp
  rw [_root_.CTree.iter.eq_def]
  simp

/-- A handler that leaves error and UB events alone preserves a finite pure/error
tree up to the silent steps inserted by `interp`. Other events are unreachable. -/
theorem interp_sim_of_pureOrErr {FIn CIn α : Type}
    {F : FIn → Type} {C : CIn → Type}
    [_root_.CTree.HasUB FIn] [ErrorE -< F] [_root_.CTree.UBE -< F]
    (handler : (event : FIn) → _root_.CTree.CTree F C (F event))
    (errorSame : handler (_root_.CTree.Subeffect.mapEff ErrorE F ErrorEIn.mk) =
      _root_.CTree.CTree.trigger (_root_.CTree.Subeffect.mapEff ErrorE F ErrorEIn.mk))
    (ubSame : handler (_root_.CTree.Subeffect.mapEff _root_.CTree.UBE F _root_.CTree.UBEIn.mk) =
      _root_.CTree.CTree.trigger
        (_root_.CTree.Subeffect.mapEff _root_.CTree.UBE F _root_.CTree.UBEIn.mk))
    (errorUB : _root_.CTree.HasUB.isUB
      (_root_.CTree.Subeffect.mapEff ErrorE F ErrorEIn.mk))
    (ubUB : _root_.CTree.HasUB.isUB
      (_root_.CTree.Subeffect.mapEff _root_.CTree.UBE F _root_.CTree.UBEIn.mk))
    {tree : _root_.CTree.CTree F C α} (shape : PureOrErr tree) :
    _root_.CTree.Sim Eq (_root_.CTree.interp handler tree) tree ∧
      _root_.CTree.Sim Eq tree (_root_.CTree.interp handler tree) := by
  induction shape with
  | ret value =>
    rw [interp_ret_eq]
    exact ⟨_root_.CTree.Sim.refl _ (fun _ => rfl) _,
      _root_.CTree.Sim.refl _ (fun _ => rfl) _⟩
  | tau choice next _ ih =>
    rw [interp_tau_eq]
    constructor
    · apply _root_.CTree.Sim.tau_id
      intro x
      simp only [_root_.CTree.CTree.tau1_def, _root_.CTree.Sim.tau_l]
      intro _
      exact (ih x).1
    · apply _root_.CTree.Sim.tau_id
      intro x
      apply _root_.CTree.Sim.tau_r _ (.inl .c1) _ _ .unit
      exact (ih x).2
  | fail =>
    constructor
    · exact _root_.CTree.Sim.ub _ _ errorUB
    · rw [interp_vis_eq, errorSame]
      simp only [_root_.CTree.CTree.trigger_def, Bind.bind, _root_.CTree.CTree.bind_vis]
      exact _root_.CTree.Sim.ub _ _ errorUB
  | ub =>
    constructor
    · exact _root_.CTree.Sim.ub _ _ ubUB
    · rw [interp_vis_eq, ubSame]
      simp only [_root_.CTree.CTree.trigger_def, Bind.bind, _root_.CTree.CTree.bind_vis]
      exact _root_.CTree.Sim.ub _ _ ubUB

/-- Embed a raw tree into the unresolved region-effect family. -/
def embedRaw {ctx : WfIRContext OpCode} {σ α : Type} (tree : Tree α) :
    RegionTree ctx σ α :=
  _root_.CTree.interp _root_.CTree.CTree.trigger tree

theorem embedRaw_pureOrErr {ctx : WfIRContext OpCode} {σ α : Type} {tree : Tree α}
    (shape : PureOrErr tree) : PureOrErr (embedRaw (ctx := ctx) (σ := σ) tree) := by
  induction shape with
  | ret value =>
    unfold embedRaw
    rw [interp_ret_eq]
    exact .ret _
  | tau choice next _ ih =>
    unfold embedRaw at *
    rw [interp_tau_eq]
    apply PureOrErr.tau
    intro x
    apply PureOrErr.tau
    intro _
    exact ih x
  | fail =>
    unfold embedRaw
    rw [interp_vis_eq]
    simp only [_root_.CTree.CTree.trigger_def, Bind.bind, _root_.CTree.CTree.bind_vis]
    exact .fail
  | ub =>
    unfold embedRaw
    rw [interp_vis_eq]
    simp only [_root_.CTree.CTree.trigger_def, Bind.bind, _root_.CTree.CTree.bind_vis]
    exact .ub

/-- Embedding distributes over binding a finite pure/error prefix, up to the
silent steps introduced by the interpreter. The continuation may be infinite. -/
theorem sim_embedRaw_bind {ctx : WfIRContext OpCode} {σ α β : Type}
    {tree : Tree α} (shape : PureOrErr tree) (next : α → Tree β) :
    _root_.CTree.Sim Eq (embedRaw (ctx := ctx) (σ := σ) (tree >>= next))
        (embedRaw tree >>= fun x => embedRaw (next x)) ∧
      _root_.CTree.Sim Eq (embedRaw tree >>= fun x => embedRaw (next x))
        (embedRaw (ctx := ctx) (σ := σ) (tree >>= next)) := by
  induction shape with
  | ret value =>
    simp only [Bind.bind, _root_.CTree.CTree.bind_ret, embedRaw, interp_ret_eq]
    simp only [Pure.pure, _root_.CTree.CTree.bind_ret]
    exact ⟨_root_.CTree.Sim.refl _ (fun _ => rfl) _,
      _root_.CTree.Sim.refl _ (fun _ => rfl) _⟩
  | tau choice continuation _ ih =>
    simp only [Bind.bind, _root_.CTree.CTree.bind_tau, embedRaw, interp_tau_eq,
      _root_.CTree.CTree.tau1_def]
    constructor
    · apply _root_.CTree.Sim.tau_id
      intro x
      apply _root_.CTree.Sim.tau_id
      intro _
      exact (ih x).1
    · apply _root_.CTree.Sim.tau_id
      intro x
      apply _root_.CTree.Sim.tau_id
      intro _
      exact (ih x).2
  | fail =>
    simp [Bind.bind, _root_.CTree.CTree.bind_vis, embedRaw, interp_vis_eq,
      _root_.CTree.CTree.trigger_def]
    constructor <;> apply _root_.CTree.Sim.ub <;> trivial
  | ub =>
    simp [Bind.bind, _root_.CTree.CTree.bind_vis, embedRaw, interp_vis_eq,
      _root_.CTree.CTree.trigger_def]
    constructor <;> apply _root_.CTree.Sim.ub <;> trivial

/-- Forget unreachable region callbacks while retaining external error/UB events. -/
def eraseRegionHandler {ctx : WfIRContext OpCode} {σ : Type} :
    (event : RunRegionEIn ctx σ ⊕ (ErrorEIn ⊕ _root_.CTree.UBEIn)) →
      Tree ((RunRegionE ctx σ ⊕ₑ (ErrorE ⊕ₑ _root_.CTree.UBE)) event)
  | .inl _ => fail
  | .inr event => _root_.CTree.CTree.trigger
      (SubE := ErrorE ⊕ₑ _root_.CTree.UBE) event

/-- Recursive region handling and simple effect erasure coincide on a finite
pure/error tree, because it contains no recursive region request. -/
theorem interp_mrec_eq_erase {ctx : WfIRContext OpCode} {σ α : Type}
    (handler : (event : RunRegionEIn ctx σ) → RegionTree ctx σ (RunRegionE ctx σ event))
    {tree : RegionTree ctx σ α} (shape : PureOrErr tree) :
    _root_.CTree.interp_mrec handler tree =
      _root_.CTree.interp (eraseRegionHandler (ctx := ctx) (σ := σ)) tree := by
  induction shape with
  | ret value =>
    simp only [_root_.CTree.interp_mrec_ret_step, interp_ret_eq]
  | tau choice next _ ih =>
    simp only [_root_.CTree.interp_mrec_tau_step, interp_tau_eq]
    congr 1
    funext x
    rw [ih x]
  | fail =>
    simp [eraseRegionHandler, _root_.CTree.interp_mrec_external_step,
      interp_vis_eq, _root_.CTree.CTree.trigger_def, Bind.bind]
    congr 1
    funext impossible
    cases impossible
  | ub =>
    simp [eraseRegionHandler, _root_.CTree.interp_mrec_external_step,
      interp_vis_eq, _root_.CTree.CTree.trigger_def, Bind.bind]
    congr 1
    funext impossible
    cases impossible

/-- Erasing an embedding preserves a finite raw computation up to silent steps. -/
theorem sim_erase_embedRaw {ctx : WfIRContext OpCode} {σ α : Type}
    {tree : Tree α} (shape : PureOrErr tree) :
    _root_.CTree.Sim Eq
        (_root_.CTree.interp (eraseRegionHandler (ctx := ctx) (σ := σ)) (embedRaw tree)) tree ∧
      _root_.CTree.Sim Eq tree
        (_root_.CTree.interp (eraseRegionHandler (ctx := ctx) (σ := σ)) (embedRaw tree)) := by
  induction shape with
  | ret value =>
    simp only [embedRaw, Pure.pure, interp_ret_eq]
    exact ⟨_root_.CTree.Sim.refl _ (fun _ => rfl) _,
      _root_.CTree.Sim.refl _ (fun _ => rfl) _⟩
  | tau choice next _ ih =>
    simp only [embedRaw, interp_tau_eq, _root_.CTree.CTree.tau1_def]
    constructor
    · apply _root_.CTree.Sim.tau_id
      intro x
      simp only [_root_.CTree.Sim.tau_l]
      intro _ _ _
      exact (ih x).1
    · apply _root_.CTree.Sim.tau_id
      intro x
      apply _root_.CTree.Sim.tau_r _ (.inl .c1) _ _ .unit
      apply _root_.CTree.Sim.tau_r _ (.inl .c1) _ _ .unit
      apply _root_.CTree.Sim.tau_r _ (.inl .c1) _ _ .unit
      exact (ih x).2
  | fail =>
    simp [embedRaw, interp_vis_eq, eraseRegionHandler, _root_.CTree.CTree.trigger_def,
      Bind.bind, _root_.CTree.CTree.bind_vis]
    constructor <;> apply _root_.CTree.Sim.ub <;> trivial
  | ub =>
    simp [embedRaw, interp_vis_eq, eraseRegionHandler, _root_.CTree.CTree.trigger_def,
      Bind.bind, _root_.CTree.CTree.bind_vis]
    constructor <;> apply _root_.CTree.Sim.ub <;> trivial

/-- The region handler used by actual operation interpretation. -/
def operationRegionHandler {ctx : WfIRContext OpCode} (state : InterpreterState ctx) :
    (event : RunRegionEIn ctx MemoryState ⊕ (ErrorEIn ⊕ _root_.CTree.UBEIn)) →
      RegionTree ctx (InterpreterState ctx)
        ((RunRegionE ctx MemoryState ⊕ₑ (ErrorE ⊕ₑ _root_.CTree.UBE)) event)
  | .inl ⟨region, values, memoryState, inBounds⟩ => do
    let (state, results) ← runRegion region values
      ({ variables := state.variables, memory := memoryState } : InterpreterState ctx) inBounds
    return (state.memory, results)
  | .inr event => _root_.CTree.CTree.trigger (SubE := ErrorE ⊕ₑ _root_.CTree.UBE) event

theorem operationRegionHandler_pureOrErr {ctx : WfIRContext OpCode} {α : Type}
    (state : InterpreterState ctx) {tree : RegionTree ctx MemoryState α}
    (shape : PureOrErr tree) :
    PureOrErr (_root_.CTree.interp (operationRegionHandler state) tree) := by
  induction shape with
  | ret value =>
    rw [interp_ret_eq]
    exact .ret _
  | tau choice next _ ih =>
    rw [interp_tau_eq]
    apply PureOrErr.tau
    intro x
    apply PureOrErr.tau
    intro _
    exact ih x
  | fail =>
    simp [interp_vis_eq, operationRegionHandler, _root_.CTree.CTree.trigger_def, Bind.bind]
    exact .fail
  | ub =>
    simp [interp_vis_eq, operationRegionHandler, _root_.CTree.CTree.trigger_def, Bind.bind]
    exact .ub

theorem sim_operationRegionHandler_embedRaw {ctx : WfIRContext OpCode} {α : Type}
    (state : InterpreterState ctx) {tree : Tree α} (shape : PureOrErr tree) :
    _root_.CTree.Sim Eq
        (_root_.CTree.interp (operationRegionHandler state)
          (embedRaw (σ := MemoryState) tree))
        (embedRaw (ctx := ctx) (σ := InterpreterState ctx) tree) ∧
      _root_.CTree.Sim Eq
        (embedRaw (ctx := ctx) (σ := InterpreterState ctx) tree)
        (_root_.CTree.interp (operationRegionHandler state)
          (embedRaw (σ := MemoryState) tree)) := by
  induction shape with
  | ret value =>
    simp only [embedRaw, Pure.pure, interp_ret_eq]
    exact ⟨_root_.CTree.Sim.refl _ (fun _ => rfl) _,
      _root_.CTree.Sim.refl _ (fun _ => rfl) _⟩
  | tau choice next _ ih =>
    simp only [embedRaw, interp_tau_eq, _root_.CTree.CTree.tau1_def]
    constructor
    · apply _root_.CTree.Sim.tau_id
      intro x
      simp only [_root_.CTree.Sim.tau_l]
      intro _ _ _
      apply _root_.CTree.Sim.tau_r _ (.inl .c1) _ _ .unit
      exact (ih x).1
    · apply _root_.CTree.Sim.tau_id
      intro x
      simp only [_root_.CTree.Sim.tau_l]
      intro _
      apply _root_.CTree.Sim.tau_r _ (.inl .c1) _ _ .unit
      apply _root_.CTree.Sim.tau_r _ (.inl .c1) _ _ .unit
      apply _root_.CTree.Sim.tau_r _ (.inl .c1) _ _ .unit
      exact (ih x).2
  | fail =>
    simp [embedRaw, interp_vis_eq, operationRegionHandler, _root_.CTree.CTree.trigger_def,
      Bind.bind, _root_.CTree.CTree.bind_vis]
    constructor <;> apply _root_.CTree.Sim.ub <;> trivial
  | ub =>
    simp [embedRaw, interp_vis_eq, operationRegionHandler, _root_.CTree.CTree.trigger_def,
      Bind.bind, _root_.CTree.CTree.bind_vis]
    constructor <;> apply _root_.CTree.Sim.ub <;> trivial

/-- Bind checked runtime results into the current SSA state. This is the final
shared-effect computation of operation interpretation, after raw effects resolve. -/
def commitOpResults {ctx : WfIRContext OpCode} (op : OperationPtr)
    (state : InterpreterState ctx) (opIn : op.InBounds ctx.raw)
    (outcome : Array RuntimeValue × MemoryState × Option ControlFlowAction) :
    Tree (InterpreterState ctx × Option ControlFlowAction) := do
  let some variables := state.variables.setResultValues? op outcome.1 opIn | fail
  return (⟨variables, outcome.2.1⟩, outcome.2.2)

/-- Checked result binding lifts a primitive result simulation to related states.
Target conformance is an explicit premise; no primitive monotonicity or unchecked
result-conformance axiom is used. -/
theorem sim_commitOpResults
    {sourceCtx targetCtx : WfIRContext OpCode} {sourceOp targetOp : OperationPtr}
    {sourceState : InterpreterState sourceCtx} {targetState : InterpreterState targetCtx}
    {mapping : ValueMapping sourceCtx targetCtx}
    (sourceIn : sourceOp.InBounds sourceCtx.raw) (targetIn : targetOp.InBounds targetCtx.raw)
    (variables : sourceState.variables.isRefinedBy targetState.variables mapping)
    (resultPointers : targetOp.getResults! targetCtx.raw =
      mapping.applyToArray (sourceOp.getResults! sourceCtx.raw))
    (reflects : mapping.ReflectsResults sourceOp targetOp)
    {sourceResult targetResult : Array RuntimeValue × MemoryState × Option ControlFlowAction}
    (related : OperationResult.isRefinedBy sourceResult targetResult)
    (conforms : RuntimeValue.ArrayConforms targetResult.1 (targetOp.getResultTypes! targetCtx.raw)) :
    _root_.CTree.Sim
      (fun t s => s.1.isRefinedBy t.1 mapping ∧
        ControlFlowAction.optionIsRefinedBy s.2 t.2)
      (commitOpResults targetOp targetState targetIn targetResult)
      (commitOpResults sourceOp sourceState sourceIn sourceResult) := by
  rcases related with ⟨values, memory, action⟩
  cases sourceSet : sourceState.variables.setResultValues? sourceOp sourceResult.1 sourceIn with
  | none =>
    simp only [commitOpResults, sourceSet]
    exact sim_fail _ _
  | some newSource =>
    obtain ⟨newTarget, targetSet, newVariables⟩ :=
      VariableState.setResultValues?_isRefinedBy variables values resultPointers reflects
        sourceSet conforms targetIn
    simp only [commitOpResults, sourceSet, targetSet, _root_.CTree.Sim.pure]
    exact ⟨⟨memory, newVariables⟩, action⟩

/-- Lift an explicit raw opcode simulation through checked result installation.
The primitive return relation includes target conformance only for related
successful outcomes, which is exactly what the setter proof needs. -/
theorem sim_bind_commitOpResults
    {sourceCtx targetCtx : WfIRContext OpCode} {sourceOp targetOp : OperationPtr}
    {sourceState : InterpreterState sourceCtx} {targetState : InterpreterState targetCtx}
    {mapping : ValueMapping sourceCtx targetCtx}
    (sourceIn : sourceOp.InBounds sourceCtx.raw) (targetIn : targetOp.InBounds targetCtx.raw)
    (variables : sourceState.variables.isRefinedBy targetState.variables mapping)
    (resultPointers : targetOp.getResults! targetCtx.raw =
      mapping.applyToArray (sourceOp.getResults! sourceCtx.raw))
    (reflects : mapping.ReflectsResults sourceOp targetOp)
    (targetRaw sourceRaw : Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction))
    (primitive : _root_.CTree.Sim
      (fun t s => OperationResult.isRefinedBy s t ∧
        RuntimeValue.ArrayConforms t.1 (targetOp.getResultTypes! targetCtx.raw))
      targetRaw sourceRaw) :
    _root_.CTree.Sim
      (fun t s => s.1.isRefinedBy t.1 mapping ∧
        ControlFlowAction.optionIsRefinedBy s.2 t.2)
      (targetRaw >>= commitOpResults targetOp targetState targetIn)
      (sourceRaw >>= commitOpResults sourceOp sourceState sourceIn) := by
  apply _root_.CTree.Sim.bind _ _ _ _ primitive
  intro targetResult sourceResult related
  exact sim_commitOpResults sourceIn targetIn variables resultPointers reflects related.1 related.2


/-- Collect SSA operands, run a shared-effect primitive, and commit its checked
results. A primitive may already have had its region effects handled. -/
def runOpWith {ctx : WfIRContext OpCode} (op : OperationPtr)
    (state : InterpreterState ctx) (opIn : op.InBounds ctx.raw)
    (raw : Array RuntimeValue → MemoryState →
      Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction)) :
    Tree (InterpreterState ctx × Option ControlFlowAction) := do
  let some operands := state.variables.getOperandValues op | fail
  let outcome ← raw operands state.memory
  commitOpResults op state opIn outcome

/-- Operand collection and checked result installation preserve an explicit
primitive simulation across contexts. Only the supplied primitive obligation
asserts semantic monotonicity; the theorem assumes no dialect-wide axiom. -/
theorem sim_runOpWith
    {sourceCtx targetCtx : WfIRContext OpCode} {sourceOp targetOp : OperationPtr}
    {sourceState : InterpreterState sourceCtx} {targetState : InterpreterState targetCtx}
    {mapping : ValueMapping sourceCtx targetCtx}
    (sourceIn : sourceOp.InBounds sourceCtx.raw) (targetIn : targetOp.InBounds targetCtx.raw)
    (states : sourceState.isRefinedBy targetState mapping)
    (operandPointers : targetOp.getOperands! targetCtx.raw =
      mapping.applyToArray (sourceOp.getOperands! sourceCtx.raw))
    (resultPointers : targetOp.getResults! targetCtx.raw =
      mapping.applyToArray (sourceOp.getResults! sourceCtx.raw))
    (reflects : mapping.ReflectsResults sourceOp targetOp)
    (targetRaw sourceRaw : Array RuntimeValue → MemoryState →
      Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction))
    (primitive : ∀ sourceValues targetValues,
      sourceState.variables.getOperandValues sourceOp = some sourceValues →
      targetState.variables.getOperandValues targetOp = some targetValues →
      RuntimeValue.arrayIsRefinedBy sourceValues targetValues →
      _root_.CTree.Sim
        (fun t s => OperationResult.isRefinedBy s t ∧
          RuntimeValue.ArrayConforms t.1 (targetOp.getResultTypes! targetCtx.raw))
        (targetRaw targetValues targetState.memory) (sourceRaw sourceValues sourceState.memory)) :
    _root_.CTree.Sim
      (fun t s => s.1.isRefinedBy t.1 mapping ∧
        ControlFlowAction.optionIsRefinedBy s.2 t.2)
      (runOpWith targetOp targetState targetIn targetRaw)
      (runOpWith sourceOp sourceState sourceIn sourceRaw) := by
  cases sourceGet : sourceState.variables.getOperandValues sourceOp with
  | none =>
    simp only [runOpWith, sourceGet]
    exact sim_fail _ _
  | some sourceValues =>
    obtain ⟨targetValues, targetGet, values⟩ :=
      VariableState.getOperandValues_isRefinedBy states.2 sourceIn operandPointers sourceGet
    simp only [runOpWith, sourceGet, targetGet]
    exact sim_bind_commitOpResults sourceIn targetIn states.2 resultPointers reflects
      _ _ (primitive sourceValues targetValues sourceGet targetGet values)


/-- Operation interpretation before injection into the unresolved region-effect
family. The current primitive opcode interpreter has no region callbacks. -/
def interpretOpCore {ctx : WfIRContext OpCode} (op : OperationPtr)
    (state : InterpreterState ctx) (opIn : op.InBounds ctx.raw) :
    Tree (InterpreterState ctx × Option ControlFlowAction) :=
  runOpWith op state opIn (OperationPtr.interpretCTree op opIn)

/-- Cross-context operation-core simulation from explicit primitive semantics and
an operation frame. This lemma has no dependency on the assumed Interp opcode
monotonicity or the assumed Interp result-conformance theorem. -/
theorem sim_interpretOpCore
    {sourceCtx targetCtx : WfIRContext OpCode} {sourceOp targetOp : OperationPtr}
    {sourceState : InterpreterState sourceCtx} {targetState : InterpreterState targetCtx}
    {mapping : ValueMapping sourceCtx targetCtx}
    (sourceIn : sourceOp.InBounds sourceCtx.raw) (targetIn : targetOp.InBounds targetCtx.raw)
    (states : sourceState.isRefinedBy targetState mapping)
    (frame : mapping.PreservesOperation sourceOp targetOp sourceIn targetIn)
    (primitive : ∀ sourceValues targetValues,
      sourceState.variables.getOperandValues sourceOp = some sourceValues →
      targetState.variables.getOperandValues targetOp = some targetValues →
      RuntimeValue.arrayIsRefinedBy sourceValues targetValues →
      _root_.CTree.Sim
        (fun t s => OperationResult.isRefinedBy s t ∧
          RuntimeValue.ArrayConforms t.1 (targetOp.getResultTypes! targetCtx.raw))
        (OperationPtr.interpretCTree targetOp targetIn targetValues targetState.memory)
        (OperationPtr.interpretCTree sourceOp sourceIn sourceValues sourceState.memory)) :
    _root_.CTree.Sim
      (fun t s => s.1.isRefinedBy t.1 mapping ∧
        ControlFlowAction.optionIsRefinedBy s.2 t.2)
      (interpretOpCore targetOp targetState targetIn)
      (interpretOpCore sourceOp sourceState sourceIn) :=
  sim_runOpWith sourceIn targetIn states frame.operands frame.results frame.reflect
    _ _ primitive


/-- The checked result continuation in the unresolved region-effect family. -/
def commitOpResultsRegion {ctx : WfIRContext OpCode} (op : OperationPtr)
    (state : InterpreterState ctx) (opIn : op.InBounds ctx.raw)
    (outcome : Array RuntimeValue × MemoryState × Option ControlFlowAction) :
    RegionTree ctx (InterpreterState ctx) (InterpreterState ctx × Option ControlFlowAction) := do
  let some variables := state.variables.setResultValues? op outcome.1 opIn | fail
  return (⟨variables, outcome.2.1⟩, outcome.2.2)

theorem sim_commitOpResults_embed {ctx : WfIRContext OpCode} (op : OperationPtr)
    (state : InterpreterState ctx) (opIn : op.InBounds ctx.raw)
    (outcome : Array RuntimeValue × MemoryState × Option ControlFlowAction) :
    _root_.CTree.Sim Eq (commitOpResultsRegion op state opIn outcome)
        (embedRaw (commitOpResults op state opIn outcome)) ∧
      _root_.CTree.Sim Eq (embedRaw (commitOpResults op state opIn outcome))
        (commitOpResultsRegion op state opIn outcome) := by
  cases setter : state.variables.setResultValues? op outcome.1 opIn with
  | none =>
    simp [commitOpResultsRegion, commitOpResults, setter, embedRaw, fail,
      _root_.CTree.CTree.trigger_def, Bind.bind, interp_vis_eq]
    constructor <;> apply _root_.CTree.Sim.ub <;> trivial
  | some variables =>
    simp only [commitOpResultsRegion, commitOpResults, setter, embedRaw, Pure.pure,
      interp_ret_eq, _root_.CTree.Sim.ret]
    trivial

/-- Operation interpretation with the unused region-callback handler removed. -/
def interpretOpEmbeddedCore {ctx : WfIRContext OpCode} (op : OperationPtr)
    (state : InterpreterState ctx) (opIn : op.InBounds ctx.raw) :
    RegionTree ctx (InterpreterState ctx) (InterpreterState ctx × Option ControlFlowAction) := do
  let some operands := state.variables.getOperandValues op | fail
  let outcome ← embedRaw (OperationPtr.interpretCTree op opIn operands state.memory)
  commitOpResultsRegion op state opIn outcome

/-- The actual operation interpreter and its single-embedding core mutually
simulate each other. The proof uses finite opcode shape, without a new axiom. -/
theorem sim_interpretOp_embeddedCore {ctx : WfIRContext OpCode} (op : OperationPtr)
    (state : InterpreterState ctx) (opIn : op.InBounds ctx.raw) :
    _root_.CTree.Sim Eq (interpretOp op state opIn) (interpretOpEmbeddedCore op state opIn) ∧
      _root_.CTree.Sim Eq (interpretOpEmbeddedCore op state opIn) (interpretOp op state opIn) := by
  cases get : state.variables.getOperandValues op with
  | none =>
    simp only [interpretOp, interpretOpEmbeddedCore, get]
    exact ⟨_root_.CTree.Sim.refl _ (fun _ => rfl) _,
      _root_.CTree.Sim.refl _ (fun _ => rfl) _⟩
  | some operands =>
    have shapes : PureOrErr (OperationPtr.interpretCTree op opIn operands state.memory) := by
      unfold OperationPtr.interpretCTree
      exact interpretOp'_pureOrErr _ _ _ _ _ _ (op.getRegions ctx.raw)
    have norm := sim_operationRegionHandler_embedRaw state shapes
    simp only [interpretOp, interpretOpEmbeddedCore, get]
    constructor
    · apply _root_.CTree.Sim.bind _ _ _ _ norm.1
      intro target source equal
      subst source
      exact _root_.CTree.Sim.refl _ (fun _ => rfl) _
    · apply _root_.CTree.Sim.bind _ _ _ _ norm.2
      intro target source equal
      subst source
      exact _root_.CTree.Sim.refl _ (fun _ => rfl) _


/-- The actual operation interpreter is an embedding of the shared-effect core,
up to finite silent steps. This links the core state-refinement theorem to the
runtime interpreter without assuming a normalization axiom. -/
theorem sim_interpretOp_embedCore {ctx : WfIRContext OpCode} (op : OperationPtr)
    (state : InterpreterState ctx) (opIn : op.InBounds ctx.raw) :
    _root_.CTree.Sim Eq (interpretOp op state opIn) (embedRaw (interpretOpCore op state opIn)) ∧
      _root_.CTree.Sim Eq (embedRaw (interpretOpCore op state opIn)) (interpretOp op state opIn) := by
  have actual := sim_interpretOp_embeddedCore op state opIn
  have core :
      _root_.CTree.Sim Eq (interpretOpEmbeddedCore op state opIn)
          (embedRaw (interpretOpCore op state opIn)) ∧
        _root_.CTree.Sim Eq (embedRaw (interpretOpCore op state opIn))
          (interpretOpEmbeddedCore op state opIn) := by
    cases get : state.variables.getOperandValues op with
    | none =>
      simp [interpretOpEmbeddedCore, interpretOpCore, runOpWith, get, embedRaw, fail,
        _root_.CTree.CTree.trigger_def, Bind.bind, interp_vis_eq]
      constructor <;> apply _root_.CTree.Sim.ub <;> trivial
    | some operands =>
      have shape : PureOrErr (OperationPtr.interpretCTree op opIn operands state.memory) := by
        unfold OperationPtr.interpretCTree
        exact interpretOp'_pureOrErr _ _ _ _ _ _ (op.getRegions ctx.raw)
      have distribute := sim_embedRaw_bind (ctx := ctx) (σ := InterpreterState ctx) shape
        (commitOpResults op state opIn)
      have rawRefl := _root_.CTree.Sim.refl Eq (fun _ => rfl)
        (embedRaw (ctx := ctx) (σ := InterpreterState ctx)
          (OperationPtr.interpretCTree op opIn operands state.memory))
      have forward := _root_.CTree.Sim.bind _ _
        (commitOpResultsRegion op state opIn)
        (fun x => embedRaw (commitOpResults op state opIn x)) rawRefl
        (by intro t s h; subst s; exact (sim_commitOpResults_embed op state opIn t).1)
      have backward := _root_.CTree.Sim.bind _ _
        (fun x => embedRaw (commitOpResults op state opIn x))
        (commitOpResultsRegion op state opIn) rawRefl
        (by intro t s h; subst s; exact (sim_commitOpResults_embed op state opIn t).2)
      simp only [interpretOpEmbeddedCore, interpretOpCore, runOpWith, get]
      exact ⟨_root_.CTree.Sim.trans forward distribute.2 (fun _ _ _ => Eq.trans),
        _root_.CTree.Sim.trans distribute.1 backward (fun _ _ _ => Eq.trans)⟩
  exact ⟨_root_.CTree.Sim.trans actual.1 core.1 (fun _ _ _ => Eq.trans),
    _root_.CTree.Sim.trans core.2 actual.2 (fun _ _ _ => Eq.trans)⟩


theorem commitOpResults_pureOrErr {ctx : WfIRContext OpCode} (op : OperationPtr)
    (state : InterpreterState ctx) (opIn : op.InBounds ctx.raw)
    (outcome : Array RuntimeValue × MemoryState × Option ControlFlowAction) :
    PureOrErr (commitOpResults op state opIn outcome) := by
  unfold commitOpResults
  split
  · exact .ret _
  · simp [fail, _root_.CTree.CTree.trigger_def, Bind.bind]
    exact .fail

theorem interpretOpCore_pureOrErr {ctx : WfIRContext OpCode} (op : OperationPtr)
    (state : InterpreterState ctx) (opIn : op.InBounds ctx.raw) :
    PureOrErr (interpretOpCore op state opIn) := by
  unfold interpretOpCore runOpWith
  split
  · apply PureOrErr.bind
    · unfold OperationPtr.interpretCTree
      exact interpretOp'_pureOrErr _ _ _ _ _ _ (op.getRegions ctx.raw)
    · exact commitOpResults_pureOrErr op state opIn
  · simp [fail, _root_.CTree.CTree.trigger_def, Bind.bind]
    exact .fail

theorem interpretOp_pureOrErr {ctx : WfIRContext OpCode} (op : OperationPtr)
    (state : InterpreterState ctx) (opIn : op.InBounds ctx.raw) :
    PureOrErr (interpretOp op state opIn) := by
  unfold interpretOp
  split
  next operands get =>
    apply PureOrErr.bind
    · apply operationRegionHandler_pureOrErr state
      apply embedRaw_pureOrErr
      exact interpretOp'_pureOrErr _ _ _ _ _ _ (op.getRegions ctx.raw)
    · intro outcome
      dsimp only
      split
      · exact .ret _
      · simp [fail, _root_.CTree.CTree.trigger_def, Bind.bind]
        exact .fail
  next missing =>
    simp [fail, _root_.CTree.CTree.trigger_def, Bind.bind]
    exact .fail

/-- Actual operation execution under recursive region interpretation normalizes
to the common-effect raw core. The recursive handler is irrelevant because the
current opcode interpreters never request a region callback. -/
theorem sim_interp_mrec_interpretOp {ctx : WfIRContext OpCode}
    (handler : (event : RunRegionEIn ctx (InterpreterState ctx)) →
      RegionTree ctx (InterpreterState ctx) (RunRegionE ctx (InterpreterState ctx) event))
    (op : OperationPtr) (state : InterpreterState ctx) (opIn : op.InBounds ctx.raw) :
    _root_.CTree.Sim Eq (_root_.CTree.interp_mrec handler (interpretOp op state opIn))
        (interpretOpCore op state opIn) ∧
      _root_.CTree.Sim Eq (interpretOpCore op state opIn)
        (_root_.CTree.interp_mrec handler (interpretOp op state opIn)) := by
  rw [interp_mrec_eq_erase handler (interpretOp_pureOrErr op state opIn)]
  have normalized := sim_interpretOp_embedCore op state opIn
  have forward := _root_.CTree.Sim.interp eraseRegionHandler _ _ normalized.1
  have backward := _root_.CTree.Sim.interp eraseRegionHandler _ _ normalized.2
  have erased := sim_erase_embedRaw (ctx := ctx) (σ := InterpreterState ctx) (interpretOpCore_pureOrErr op state opIn)
  exact ⟨_root_.CTree.Sim.trans forward erased.1 (fun _ _ _ => Eq.trans),
    _root_.CTree.Sim.trans erased.2 backward (fun _ _ _ => Eq.trans)⟩

theorem interp_mrec_fail_eq {ctx : WfIRContext OpCode} {σ α : Type}
    (handler : (event : RunRegionEIn ctx σ) → RegionTree ctx σ (RunRegionE ctx σ event)) :
    _root_.CTree.interp_mrec handler (fail : RegionTree ctx σ α) = (fail : Tree α) := by
  simp [fail, _root_.CTree.CTree.trigger_def, Bind.bind,
    _root_.CTree.interp_mrec_external_step]
  congr 1
  funext impossible
  cases impossible

/-- A CFG step executed directly in the common external effect family. -/
def interpretCFGCore.iter {ctx : WfIRContext OpCode} (location : interpretCFG.StateLocation ctx)
    (state : InterpreterState ctx) : Tree
      ((interpretCFG.StateLocation ctx × InterpreterState ctx) ⊕
        (InterpreterState ctx × Array RuntimeValue)) := do
  match location with
  | .inl (⟨block, blockInBounds⟩, values) =>
    if values.size != block.getNumArguments ctx.raw then return ← fail
    let some variables := state.variables.setArgumentValues? block values | fail
    rlet some firstOp := block.getFirstOp ctx.raw | fail
    return .inl (.inr ⟨firstOp, by grind⟩, ⟨variables, state.memory⟩)
  | .inr ⟨op, opInBounds⟩ =>
    let (state, action) ← interpretOpCore op state opInBounds
    match action with
    | some (.return results) => return .inr (state, results)
    | some (.branch args dest) =>
      if h : dest.InBounds ctx.raw then return .inl (.inl (⟨dest, h⟩, args), state)
      else fail
    | none =>
      rlet some nextOp := op.getNextOp ctx.raw | fail
      return .inl (.inr ⟨nextOp, by grind⟩, state)

/-- Region execution with callbacks absent, directly in the external effect family. -/
def interpretCFGCore {ctx : WfIRContext OpCode} (region : RegionPtr)
    (values : Array RuntimeValue) (state : InterpreterState ctx)
    (inBounds : region.InBounds ctx.raw) : Tree (InterpreterState ctx × Array RuntimeValue) := do
  rlet some firstBlock := region.getFirstBlock ctx.raw | fail
  _root_.CTree.iter (fun (next, state) => interpretCFGCore.iter next state)
    (.inl (⟨firstBlock, by grind⟩, values), state)

theorem sim_interp_mrec_CFG_iter {ctx : WfIRContext OpCode}
    (handler : (event : RunRegionEIn ctx (InterpreterState ctx)) →
      RegionTree ctx (InterpreterState ctx) (RunRegionE ctx (InterpreterState ctx) event))
    (location : interpretCFG.StateLocation ctx) (state : InterpreterState ctx) :
    _root_.CTree.Sim Eq (_root_.CTree.interp_mrec handler (interpretCFG.iter location state))
        (interpretCFGCore.iter location state) ∧
      _root_.CTree.Sim Eq (interpretCFGCore.iter location state)
        (_root_.CTree.interp_mrec handler (interpretCFG.iter location state)) := by
  have self : ∀ tree : Tree ((interpretCFG.StateLocation ctx × InterpreterState ctx) ⊕
      (InterpreterState ctx × Array RuntimeValue)), _root_.CTree.Sim Eq tree tree :=
    fun tree => _root_.CTree.Sim.refl _ (fun _ => rfl) tree
  cases location with
  | inl entry =>
    rcases entry with ⟨⟨block, blockIn⟩, values⟩
    unfold interpretCFG.iter interpretCFGCore.iter
    dsimp only
    split
    · simp only [interp_mrec_fail_eq]
      try simp_all only
      first
      | exact ⟨_root_.CTree.Sim.refl _ (fun _ => rfl) _,
          _root_.CTree.Sim.refl _ (fun _ => rfl) _⟩
      | grind
    · split
      · split
        · simp only [Pure.pure, _root_.CTree.interp_mrec_ret_step]
          try simp_all only
          first
          | exact ⟨_root_.CTree.Sim.refl _ (fun _ => rfl) _,
              _root_.CTree.Sim.refl _ (fun _ => rfl) _⟩
          | grind
        · rw [interp_mrec_fail_eq]
          try simp_all only
          first
          | exact ⟨_root_.CTree.Sim.refl _ (fun _ => rfl) _,
              _root_.CTree.Sim.refl _ (fun _ => rfl) _⟩
          | grind
      · rw [interp_mrec_fail_eq]
        try simp_all only
        first
        | exact ⟨_root_.CTree.Sim.refl _ (fun _ => rfl) _,
            _root_.CTree.Sim.refl _ (fun _ => rfl) _⟩
        | grind
  | inr op =>
    rcases op with ⟨op, opIn⟩
    unfold interpretCFG.iter interpretCFGCore.iter
    dsimp only
    rw [_root_.CTree.interp_mrec_bind]
    have primitive := sim_interp_mrec_interpretOp handler op state opIn
    constructor
    · apply _root_.CTree.Sim.bind _ _ _ _ primitive.1
      intro t s equal
      subst s
      rcases t with ⟨newState, action⟩
      dsimp only
      cases action with
      | none =>
        split <;> simp only [Pure.pure]
        all_goals try simp_all only
        all_goals first
          | exact _root_.CTree.Sim.refl _ (fun _ => rfl) _
          | grind [interp_mrec_fail_eq, _root_.CTree.interp_mrec_ret_step]
      | some action =>
        cases action with
        | «return» values =>
          simp only [Pure.pure, _root_.CTree.interp_mrec_ret_step]
          try simp_all only
          try exact _root_.CTree.Sim.refl _ (fun _ => rfl) _
        | branch args dest =>
          split <;> simp only [Pure.pure]
          all_goals try simp_all only
          all_goals first
          | exact _root_.CTree.Sim.refl _ (fun _ => rfl) _
          | grind [interp_mrec_fail_eq, _root_.CTree.interp_mrec_ret_step]
    · apply _root_.CTree.Sim.bind _ _ _ _ primitive.2
      intro t s equal
      subst s
      rcases t with ⟨newState, action⟩
      dsimp only
      cases action with
      | none =>
        split <;> simp only [Pure.pure]
        all_goals try simp_all only
        all_goals first
          | exact _root_.CTree.Sim.refl _ (fun _ => rfl) _
          | grind [interp_mrec_fail_eq, _root_.CTree.interp_mrec_ret_step]
      | some action =>
        cases action with
        | «return» values =>
          simp only [Pure.pure, _root_.CTree.interp_mrec_ret_step]
          try simp_all only
          try exact _root_.CTree.Sim.refl _ (fun _ => rfl) _
        | branch args dest =>
          split <;> simp only [Pure.pure]
          all_goals try simp_all only
          all_goals first
          | exact _root_.CTree.Sim.refl _ (fun _ => rfl) _
          | grind [interp_mrec_fail_eq, _root_.CTree.interp_mrec_ret_step]

/-- Recursive region interpretation of a CFG normalizes to a core CFG loop. -/
theorem sim_interp_mrec_CFG {ctx : WfIRContext OpCode}
    (handler : (event : RunRegionEIn ctx (InterpreterState ctx)) →
      RegionTree ctx (InterpreterState ctx) (RunRegionE ctx (InterpreterState ctx) event))
    (region : RegionPtr) (values : Array RuntimeValue) (state : InterpreterState ctx)
    (regionIn : region.InBounds ctx.raw) :
    _root_.CTree.Sim Eq (_root_.CTree.interp_mrec handler (interpretCFG region values state regionIn))
        (interpretCFGCore region values state regionIn) ∧
      _root_.CTree.Sim Eq (interpretCFGCore region values state regionIn)
        (_root_.CTree.interp_mrec handler (interpretCFG region values state regionIn)) := by
  unfold interpretCFG interpretCFGCore
  split
  next bb entry =>
    let initial : interpretCFG.StateLocation ctx × InterpreterState ctx :=
      (.inl (⟨bb, by grind⟩, values), state)
    have fusion := _root_.CTree.sim_interp_mrec_iter handler
      (fun p : interpretCFG.StateLocation ctx × InterpreterState ctx => interpretCFG.iter p.1 p.2)
      initial
    have forward : _root_.CTree.Sim Eq
        (_root_.CTree.iter (fun p : interpretCFG.StateLocation ctx × InterpreterState ctx =>
          _root_.CTree.interp_mrec handler (interpretCFG.iter p.1 p.2)) initial)
        (_root_.CTree.iter (fun p : interpretCFG.StateLocation ctx × InterpreterState ctx =>
          interpretCFGCore.iter p.1 p.2) initial) := by
      apply _root_.CTree.Sim.iter _ _ _ _ rfl
      intro x y equal
      subst y
      exact ((sim_interp_mrec_CFG_iter handler x.1 x.2).1).mono
        (fun a b equal => by subst b; cases a <;> first | exact Sum.LiftRel.inl rfl | exact Sum.LiftRel.inr rfl)
    have backward : _root_.CTree.Sim Eq
        (_root_.CTree.iter (fun p : interpretCFG.StateLocation ctx × InterpreterState ctx =>
          interpretCFGCore.iter p.1 p.2) initial)
        (_root_.CTree.iter (fun p : interpretCFG.StateLocation ctx × InterpreterState ctx =>
          _root_.CTree.interp_mrec handler (interpretCFG.iter p.1 p.2)) initial) := by
      apply _root_.CTree.Sim.iter _ _ _ _ rfl
      intro x y equal
      subst y
      exact ((sim_interp_mrec_CFG_iter handler x.1 x.2).2).mono
        (fun a b equal => by subst b; cases a <;> first | exact Sum.LiftRel.inl rfl | exact Sum.LiftRel.inr rfl)
    have result := And.intro
      (_root_.CTree.Sim.trans fusion.1 forward (fun _ _ _ => Eq.trans))
      (_root_.CTree.Sim.trans backward fusion.2 (fun _ _ _ => Eq.trans))
    dsimp only [initial] at result
    grind
  next missing =>
    rw [interp_mrec_fail_eq]
    have same := _root_.CTree.Sim.refl Eq (fun _ => rfl)
      (fail : Tree (InterpreterState ctx × Array RuntimeValue))
    grind

/-- The actual recursive region interpreter and the common-effect core CFG
mutually simulate each other, including possibly nonterminating CFG execution. -/
theorem sim_interpretRegion_core {ctx : WfIRContext OpCode}
    (region : RegionPtr) (values : Array RuntimeValue) (state : InterpreterState ctx)
    (regionIn : region.InBounds ctx.raw) :
    _root_.CTree.Sim Eq (interpretRegion region values state regionIn)
        (interpretCFGCore region values state regionIn) ∧
      _root_.CTree.Sim Eq (interpretCFGCore region values state regionIn)
        (interpretRegion region values state regionIn) := by
  unfold interpretRegion _root_.CTree.mrec
  exact sim_interp_mrec_CFG _ region values state regionIn

/-- Same-context simulation of the actual operation interpreter. The mapping may
rename SSA values; primitive refinement and conformance remain explicit premises. -/
theorem sim_interpretOp
    {ctx : WfIRContext OpCode} {sourceOp targetOp : OperationPtr}
    {sourceState targetState : InterpreterState ctx} {mapping : ValueMapping ctx ctx}
    (sourceIn : sourceOp.InBounds ctx.raw) (targetIn : targetOp.InBounds ctx.raw)
    (states : sourceState.isRefinedBy targetState mapping)
    (frame : mapping.PreservesOperation sourceOp targetOp sourceIn targetIn)
    (primitive : ∀ sourceValues targetValues,
      sourceState.variables.getOperandValues sourceOp = some sourceValues →
      targetState.variables.getOperandValues targetOp = some targetValues →
      RuntimeValue.arrayIsRefinedBy sourceValues targetValues →
      _root_.CTree.Sim
        (fun t s => OperationResult.isRefinedBy s t ∧
          RuntimeValue.ArrayConforms t.1 (targetOp.getResultTypes! ctx.raw))
        (OperationPtr.interpretCTree targetOp targetIn targetValues targetState.memory)
        (OperationPtr.interpretCTree sourceOp sourceIn sourceValues sourceState.memory)) :
    _root_.CTree.Sim
      (fun t s => s.1.isRefinedBy t.1 mapping ∧
        ControlFlowAction.optionIsRefinedBy s.2 t.2)
      (interpretOp targetOp targetState targetIn)
      (interpretOp sourceOp sourceState sourceIn) := by
  have core := sim_interpretOpCore sourceIn targetIn states frame primitive
  have lifted := _root_.CTree.Sim.interp
    (_root_.CTree.CTree.trigger (E := RunRegionE ctx (InterpreterState ctx) ⊕ₑ
      (ErrorE ⊕ₑ _root_.CTree.UBE))) _ _ core
  have targetNorm := (sim_interpretOp_embedCore targetOp targetState targetIn).1
  have sourceNorm := (sim_interpretOp_embedCore sourceOp sourceState sourceIn).2
  exact _root_.CTree.Sim.trans (_root_.CTree.Sim.trans targetNorm lifted
    (fun _ _ _ equal related => equal ▸ related)) sourceNorm
    (fun _ _ _ related equal => equal ▸ related)

end CTree
end Veir
