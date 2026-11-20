module

public import Veir.Interpreter.CTreeControlFlow
import all Veir.Interpreter.CTree
public import Veir.Interpreter.CTreePrimitiveRefinement
public import Veir.PatternRewriter.Puddle.CTreeExecutionSoundness
public import Veir.PatternRewriter.Puddle.CreationOperationSemantics
public import Veir.PatternRewriter.Puddle.ScopeEdges
public import Veir.PatternRewriter.Puddle.CreationHistoryFrame
public import Veir.PatternRewriter.Puddle.CreationCheckedSemantics
import all CTree.Defs
import all CTree.IterSim
import all Veir.PatternRewriter.Puddle.CreationCheckedSemantics
public import Veir.PatternRewriter.Puddle.DriverScope
import all Veir.PatternRewriter.Puddle.CreationOperationSemantics
public import Veir.Interpreter.CTreeEquationLemma
import all Veir.Interpreter.Refinement.Basic
import all Veir.Interpreter.CTreeStateRefinement
import all Veir.Interpreter.CTreeInterpreter
import all Veir.IR.OpCode

public section

namespace Veir.Puddle.CTree

theorem interpretCTree_eq_bang {ctx : WfIRContext OpCode} (op : OperationPtr)
    (opIn : op.InBounds ctx.raw) (values : Array RuntimeValue) (memory : MemoryState) :
    Veir.OperationPtr.interpretCTree op opIn values memory =
      Veir.CTree.interpretOp' (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw)) (op.getResultTypes! ctx.raw)
        values (op.getSuccessors! ctx.raw) memory := by
  unfold Veir.OperationPtr.interpretCTree
  have codeEq := OperationPtr.getOpType!_eq_getOpType opIn
  have propertyEq := OperationPtr.getProperties!_eq_getProperties opIn
    (opCode := op.getOpType ctx.raw opIn)
    (by simpa only [ofDialect_hasDialectRefl] using codeEq)
  simp only [← propertyEq, ← OperationPtr.getResultTypes!_eq_getResultTypes opIn,
    ← OperationPtr.getSuccessors!_eq_getSuccessors opIn]
  rw [← codeEq]
  rfl

/-- A target computation may retain extra execution metadata without changing a
simulation proved after projecting it away. This is derived from graph simulation
and composition, rather than inversion of the abstract simulation relation. -/
theorem sim_of_projected_target {α β γ : Type} (project : α → β)
    (target : Tree α) (source : Tree γ) (relation : β → γ → Prop)
    (simulation : _root_.CTree.Sim relation (target >>= fun value => pure (project value)) source) :
    _root_.CTree.Sim (fun target source => relation (project target) source) target source := by
  have graph := _root_.CTree.Sim.bind target target Pure.pure (fun value => pure (project value))
    (_root_.CTree.Sim.refl Eq (fun _ => rfl) target)
    (fun a b equal => by subst b; exact (_root_.CTree.Sim.pure _ _ _).mpr rfl)
  change _root_.CTree.Sim (fun a b => project a = b) (target >>= Pure.pure)
    (target >>= fun value => pure (project value)) at graph
  have graph' : _root_.CTree.Sim (fun a b => project a = b)
      target (target >>= fun value => pure (project value)) := by
    simpa only [_root_.bind_pure] using graph
  exact _root_.CTree.Sim.trans graph' simulation
    (fun _ _ _ equal related => equal ▸ related)

/-- Observe an optional projection, reporting interpreter failure if absent. -/
def projectToTree {α β : Type} (project : α → Option β) (value : α) : Tree β :=
  (project value).elim fail Pure.pure

/-- Projecting away execution metadata may itself fail. On related successful
returns, composition recovers both a successful projection witness and the
original return relation. This is useful for replacement-pointer lookup. -/
theorem sim_of_partial_projected_target {α β γ : Type} (project : α → Option β)
    (target : Tree α) (source : Tree γ) (relation : β → γ → Prop)
    (simulation : _root_.CTree.Sim relation
      (target >>= projectToTree project) source) :
    _root_.CTree.Sim (fun target source => ∃ result,
      project target = some result ∧ relation result source) target source := by
  have graph := _root_.CTree.Sim.bind (RR' := fun a b => project a = some b) target target Pure.pure
    (projectToTree project)
    (_root_.CTree.Sim.refl Eq (fun _ => rfl) target)
    (by
      intro a b equal
      subst b
      unfold projectToTree
      cases projected : project a with
      | none =>
        simp only [Option.elim]
        exact sim_fail _ _
      | some result =>
        simp only [Option.elim]
        exact (_root_.CTree.Sim.pure (fun a b => project a = some b) _ _).mpr projected)
  change _root_.CTree.Sim (fun a b => project a = some b) (target >>= Pure.pure) _ at graph
  have graph' : _root_.CTree.Sim (fun a b => project a = some b) target
      (target >>= projectToTree project) := by
    rw [_root_.bind_pure] at graph
    exact graph
  exact _root_.CTree.Sim.trans_rel graph' simulation

/-- The concrete creation interpreter respects a continuation appended after its
final result. This permits retaining its final resolver before observing values. -/
theorem interpretCreatedOps_bind {α β : Type} (ctx : IRContext OpCode)
    (ops : List OperationPtr) (resolve : ValueResolver) (memory : MemoryState)
    (next : ValueResolver → MemoryState → Tree α) (after : α → Tree β) :
    (interpretCreatedOps ctx ops resolve memory next >>= after) =
      interpretCreatedOps ctx ops resolve memory (fun r m => next r m >>= after) := by
  induction ops generalizing resolve memory with
  | nil => rfl
  | cons op ops ih =>
    simp only [interpretCreatedOps, interpretCreatedOp]
    split
    · exact bind_fail after
    · rw [_root_.CTree.bind_assoc]
      congr 1
      funext outcome
      rcases outcome with ⟨values, memory, action⟩
      exact ih _ _

/-- The actual raw created list with its final SSA resolver and memory retained. -/
def interpretCreatedOpsFinal (ctx : IRContext OpCode) (ops : List OperationPtr)
    (resolve : ValueResolver) (memory : MemoryState) : Tree (ValueResolver × MemoryState) :=
  interpretCreatedOps ctx ops resolve memory (fun r m => pure (r, m))

theorem interpretCreatedOpsFinal_bind {α : Type} (ctx : IRContext OpCode)
    (ops : List OperationPtr) (resolve : ValueResolver) (memory : MemoryState)
    (next : ValueResolver → MemoryState → Tree α) :
    (interpretCreatedOpsFinal ctx ops resolve memory >>= fun (r, m) => next r m) =
      interpretCreatedOps ctx ops resolve memory next := by
  unfold interpretCreatedOpsFinal
  rw [interpretCreatedOps_bind]
  congr 1
  funext r m
  simp only [Bind.bind, Pure.pure, _root_.CTree.CTree.bind_ret]

/-- Recover a successful replacement lookup and its simulation relation while
retaining the final resolver of the actual raw created-operation list. -/
theorem sim_createdOpsFinal_of_replacements
    {γ : Type} (ctx : IRContext OpCode) (ops : List OperationPtr)
    (resolve : ValueResolver) (memory : MemoryState) (replacements : Array ValuePtr)
    (source : Tree γ)
    (relation : (Array RuntimeValue × MemoryState × Option ControlFlowAction) → γ → Prop)
    (localSimulation : _root_.CTree.Sim relation
      (interpretCreatedOps ctx ops resolve memory (fun r m =>
        match replacements.toList.mapM r with
        | some values => pure (values.toArray, m, none)
        | none => fail)) source) :
    _root_.CTree.Sim (fun target source => ∃ values,
      replacements.toList.mapM target.1 = some values ∧ relation (values.toArray, target.2, none) source)
      (interpretCreatedOpsFinal ctx ops resolve memory) source := by
  let project (final : ValueResolver × MemoryState) :
      Option (Array RuntimeValue × MemoryState × Option ControlFlowAction) :=
    (replacements.toList.mapM final.1).map (fun values => (values.toArray, final.2, none))
  have projected : _root_.CTree.Sim relation
      (interpretCreatedOpsFinal ctx ops resolve memory >>= projectToTree project) source := by
    change _root_.CTree.Sim relation
      (interpretCreatedOpsFinal ctx ops resolve memory >>= fun (r, m) =>
        projectToTree project (r, m)) source
    rw [interpretCreatedOpsFinal_bind ctx ops resolve memory (fun r m =>
      projectToTree project (r, m))]
    have continuation : (fun r m => projectToTree project (r, m)) = (fun r m => match replacements.toList.mapM r with
        | some values => pure (values.toArray, m, none)
        | none => fail) := by
      funext r m
      unfold projectToTree project
      cases replacements.toList.mapM r <;> rfl
    rw [continuation]
    exact localSimulation
  apply (sim_of_partial_projected_target project _ source relation projected).mono
  rintro final source ⟨result, observed, related⟩
  unfold project at observed
  cases hvalues : replacements.toList.mapM final.1 with
  | none => simp [hvalues] at observed
  | some resultValues =>
    simp only [hvalues, Option.map_some, Option.some.injEq] at observed
    subst result
    exact ⟨resultValues, rfl, related⟩

/-- The concrete local compiler run refines the original root while retaining the
final created-list resolver. This is the local root transition consumed by the
scoped CFG invariant, rather than a function/module simulation hypothesis. -/
theorem Pattern.Valid.interpret_createdOpsFinal_sim_refiningInputs
    {rule : Veir.Puddle.Pattern OpCode} (valid : Pattern.Valid rule)
    {ctx newCtx : WfIRContext OpCode} {root : OperationPtr}
    {newOps : Array OperationPtr} {replacementPointers : Array ValuePtr}
    (resolve : ValueResolver) (sourceMemory targetMemory : MemoryState)
    (localRun : rule.interpret ctx root = some (newCtx, some (newOps, replacementPointers)))
    (rootIn : root.InBounds ctx.raw) (rootVerified : root.Verified ctx rootIn)
    (executionFacts : ∀ matched, rule.matcher.run ctx.raw root = some matched →
      ∀ decl ∈ rule.matcher.decls,
        MatchDecl.RuntimeEquations ctx.raw rule.matcher.rootHandle resolve matched decl)
    {targetValues : List RuntimeValue}
    (resolved : (root.getOperands! ctx.raw).toList.mapM resolve = some targetValues)
    (sourceValues : Array RuntimeValue)
    (conforms : RuntimeValue.ArrayConforms sourceValues (root.getOperandTypes! ctx.raw))
    (values : RuntimeValue.arrayIsRefinedBy sourceValues targetValues.toArray)
    (memory : sourceMemory.isRefinedBy targetMemory) :
    _root_.CTree.Sim (fun final source => ∃ results,
      replacementPointers.toList.mapM final.1 = some results ∧
      OperationResult.isRefinedBy source (results.toArray, final.2, none))
      (interpretCreatedOpsFinal newCtx.raw newOps.toList resolve targetMemory)
      (Veir.OperationPtr.interpretCTree root rootIn sourceValues sourceMemory) :=
  sim_createdOpsFinal_of_replacements newCtx.raw newOps.toList resolve targetMemory replacementPointers
    _ _ (valid.interpret_createdOps_sim_refiningInputs resolve sourceMemory targetMemory localRun
      rootIn rootVerified executionFacts resolved sourceValues conforms values memory)

/-- Raw created-list interpretation depends only on the concrete semantic fields
of its listed operations. Insertion links and erased-root bookkeeping are irrelevant. -/
theorem interpretCreatedOpsFinal_fields_congr (before after : IRContext OpCode)
    (ops : List OperationPtr)
    (fields : ∀ op ∈ ops,
      op.getOpType! after = op.getOpType! before ∧
      op.getResultTypes! after = op.getResultTypes! before ∧
      op.getOperands! after = op.getOperands! before ∧
      (∀ code : OpCode, op.getProperties! after code = op.getProperties! before code))
    (resolve : ValueResolver) (memory : MemoryState) :
    interpretCreatedOpsEnriched after ops resolve memory =
      interpretCreatedOpsFinal before ops resolve memory := by
  unfold interpretCreatedOpsEnriched interpretCreatedOpsFinal
  induction ops generalizing resolve memory with
  | nil => rfl
  | cons op ops ih =>
    obtain ⟨code, types, operands, properties⟩ := fields op (by simp)
    simp only [interpretCreatedOps, interpretCreatedOp]
    rw [code, types, operands, properties]
    split
    · rfl
    · congr 1
      funext outcome
      rcases outcome with ⟨values, memory, action⟩
      exact ih (fun x hx => fields x (by simp [hx])) _ _

private theorem list_lookup_eq (pointers : List ValuePtr) (left right : ValueResolver)
    (same : ∀ pointer ∈ pointers, left pointer = right pointer) :
    pointers.mapM left = pointers.mapM right := by
  induction pointers with
  | nil => rfl
  | cons pointer pointers ih =>
    simp only [List.mapM_cons, same pointer (by simp)]
    rw [ih (by intro p hp; exact same p (by simp [hp]))]

/-- A checked created-operation batch refines the original root after transporting
the exact driver semantic fields. The relation retains the final checked state,
replacement lookups, and memory refinement for the CFG splice. -/
theorem sim_checked_createdOps_of_local
    {sourceCtx created targetCtx : WfIRContext OpCode} {root : OperationPtr}
    {newOps : Array OperationPtr} (replacements : Array ValuePtr)
    (sourceIn : root.InBounds sourceCtx.raw)
    (targetState : InterpreterState targetCtx) (resolve : ValueResolver) (memory : MemoryState)
    (realizes : ResolverRealizes targetCtx targetState (resolve, memory))
    (bounds : ∀ op ∈ newOps.toList, op.InBounds targetCtx.raw)
    (nonterm : ∀ op ∈ newOps.toList, (op.getOpType! targetCtx.raw).isTerminator = false)
    (conforms : CreatedResultsConform targetCtx newOps.toList)
    (replacementBounds : ∀ pointer ∈ replacements.toList, pointer.InBounds targetCtx.raw)
    (fields : ∀ op ∈ newOps.toList,
      op.getOpType! targetCtx.raw = op.getOpType! created.raw ∧
      op.getResultTypes! targetCtx.raw = op.getResultTypes! created.raw ∧
      op.getOperands! targetCtx.raw = op.getOperands! created.raw ∧
      (∀ code : OpCode, op.getProperties! targetCtx.raw code = op.getProperties! created.raw code))
    (sourceValues : Array RuntimeValue) (sourceMemory : MemoryState)
    (localSimulation : _root_.CTree.Sim (fun final source => ∃ results,
      replacements.toList.mapM final.1 = some results ∧
      OperationResult.isRefinedBy source (results.toArray, final.2, none))
      (interpretCreatedOpsFinal created.raw newOps.toList resolve memory)
      (Veir.OperationPtr.interpretCTree root sourceIn sourceValues sourceMemory)) :
    _root_.CTree.Sim (fun target source => ∃ results,
      replacements.toList.mapM target.variables.getVar? = some results ∧
      OperationResult.isRefinedBy source (results.toArray, target.memory, none))
      (interpretCreatedOpsChecked targetCtx newOps.toList targetState)
      (Veir.OperationPtr.interpretCTree root sourceIn sourceValues sourceMemory) := by
  have checked := sim_interpretCreatedOpsChecked newOps.toList bounds nonterm conforms
    targetState resolve memory realizes
  rw [interpretCreatedOpsFinal_fields_congr created.raw targetCtx.raw newOps.toList fields] at checked
  apply _root_.CTree.Sim.trans checked localSimulation
  rintro target raw source hchecked ⟨results, lookup, refined⟩
  have lookups : replacements.toList.mapM target.variables.getVar? =
      replacements.toList.mapM raw.1 :=
    list_lookup_eq _ _ _ (fun p hp => hchecked.2 p (replacementBounds p hp))
  exact ⟨results, lookups.trans lookup, by simpa only [hchecked.1] using refined⟩

/-- A finite pure/error prefix may use different continuations when they agree
on every successful outcome that prefix can actually produce. -/
theorem bind_eq_on_outcomes {α β : Type} {tree : Tree α} (shape : PureOrErr tree)
    (left right : α → Tree β)
    (same : ∀ value, PureOrErr.CanInterpretTo tree (.ok value) → left value = right value) :
    (tree >>= left) = (tree >>= right) := by
  induction shape with
  | ret value =>
    simpa only [Bind.bind, Pure.pure, _root_.CTree.CTree.bind_ret] using same value (.ret value)
  | tau choice branches shapes ih =>
    simp only [Bind.bind, _root_.CTree.CTree.bind_tau]
    congr 1
    funext x
    exact ih x (fun value outcome => same value (.tau choice branches x _ outcome))
  | fail =>
    simp only [Bind.bind, _root_.CTree.CTree.bind_vis]
    congr 1
    funext impossible
    cases impossible
  | ub =>
    simp only [Bind.bind, _root_.CTree.CTree.bind_vis]
    congr 1
    funext impossible
    cases impossible

/-- A non-control-flow operation with a known successor implements exactly one
ordinary CFG transition; no return or branch case is hidden by list execution. -/
theorem CFGCore_step_eq_checked {ctx : WfIRContext OpCode} (op next : OperationPtr)
    (opIn : op.InBounds ctx.raw) (nextIn : next.InBounds ctx.raw)
    (nextEq : op.getNextOp! ctx.raw = some next)
    (noAction : ∀ (state : InterpreterState ctx) (result : InterpreterState ctx × Option ControlFlowAction),
      PureOrErr.CanInterpretTo (Veir.CTree.interpretOpCore op state opIn) (.ok result) → result.2 = none)
    (state : InterpreterState ctx) :
    Veir.CTree.interpretCFGCore.iter (.inr ⟨op, opIn⟩) state =
      (Veir.CTree.interpretOpCore op state opIn >>= fun result =>
        pure (.inl (.inr ⟨next, nextIn⟩, result.1))) := by
  unfold Veir.CTree.interpretCFGCore.iter
  dsimp only
  apply bind_eq_on_outcomes (Veir.CTree.interpretOpCore_pureOrErr op state opIn)
  intro result outcome
  rcases result with ⟨newState, action⟩
  have actionEq := noAction state (newState, action) outcome
  dsimp only at actionEq ⊢
  rw [actionEq]
  grind

/-- Canonical scoped state refinement relates only values live at the two current
program points. Stale SSA values outside those scopes impose no obligation. -/
abbrev ScopedStateRefines {sourceCtx targetCtx : WfIRContext OpCode}
    (mapping : ValueMapping sourceCtx targetCtx)
    (sourcePoint targetPoint : RefinementPoint)
    (sourceIn : sourcePoint.InBounds sourceCtx.raw)
    (targetIn : targetPoint.InBounds targetCtx.raw)
    (source : InterpreterState sourceCtx) (target : InterpreterState targetCtx) : Prop :=
  source.isRefinedByAt target mapping sourcePoint targetPoint sourceIn targetIn

/-- Scoped variable refinement suffices for operand refinement when both operand
arrays have been collected. The mapping and scope obligations are purely IR facts. -/
theorem scoped_operandValues_refined
    {sourceCtx targetCtx : WfIRContext OpCode} {sourceOp targetOp : OperationPtr}
    {mapping : ValueMapping sourceCtx targetCtx}
    {sourceState : InterpreterState sourceCtx} {targetState : InterpreterState targetCtx}
    {sourcePoint targetPoint : RefinementPoint}
    {sourcePointIn : sourcePoint.InBounds sourceCtx.raw}
    {targetPointIn : targetPoint.InBounds targetCtx.raw}
    (sourceIn : sourceOp.InBounds sourceCtx.raw)
    (related : sourceState.variables.isRefinedByAt targetState.variables mapping
      sourcePoint targetPoint sourcePointIn targetPointIn)
    (operandPointers : targetOp.getOperands! targetCtx.raw =
      mapping.applyToArray (sourceOp.getOperands! sourceCtx.raw))
    (sourceScopes : ∀ value ∈ sourceOp.getOperands! sourceCtx.raw,
      value.InScopeAt sourcePoint sourceCtx)
    (targetScopes : ∀ (value : ValuePtr) (valueIn : value.InBounds sourceCtx.raw),
      value ∈ sourceOp.getOperands! sourceCtx.raw →
      (mapping ⟨value, valueIn⟩).val.InScopeAt targetPoint targetCtx)
    {sourceValues targetValues : Array RuntimeValue}
    (sourceGet : sourceState.variables.getOperandValues sourceOp = some sourceValues)
    (targetGet : targetState.variables.getOperandValues targetOp = some targetValues) :
    RuntimeValue.arrayIsRefinedBy sourceValues targetValues := by
  have each : ∀ (value : ValuePtr) (member : value ∈ sourceOp.getOperands! sourceCtx.raw)
      (sourceValue targetValue : RuntimeValue),
      sourceState.variables.getVar? value = some sourceValue →
      targetState.variables.getVar? (mapping ⟨value, by grind⟩) = some targetValue →
      RuntimeValue.isRefinedBy sourceValue targetValue := by
    intro value member sourceValue targetValue sourceLookup targetLookup
    exact related value (by grind) (sourceScopes value member)
      (targetScopes value (by grind) member) sourceValue sourceLookup targetValue targetLookup
  simp only [VariableState.getOperandValues] at sourceGet targetGet
  constructor
  · grind [ValueMapping.applyToArray]
  · intro i hi
    have sourceLookup := Array.mapM_option_eq_some_implies sourceGet i (by grind)
    have targetLookup := Array.mapM_option_eq_some_implies targetGet i (by grind [ValueMapping.applyToArray])
    grind [ValueMapping.applyToArray]


/-- Checked result installation preserves scoped refinement when the successor
scope introduces only the freshly computed results. This avoids imposing any
relation on stale values outside the current execution scopes. -/
theorem scoped_setResultValues_refined
    {sourceCtx targetCtx : WfIRContext OpCode} {sourceOp targetOp : OperationPtr}
    {mapping : ValueMapping sourceCtx targetCtx}
    {source newSource : VariableState sourceCtx}
    {targetVars newTargetVars : VariableState targetCtx}
    {sourcePoint targetPoint nextSourcePoint nextTargetPoint : RefinementPoint}
    {sourcePointIn : sourcePoint.InBounds sourceCtx.raw}
    {targetPointIn : targetPoint.InBounds targetCtx.raw}
    {nextSourceIn : nextSourcePoint.InBounds sourceCtx.raw}
    {nextTargetIn : nextTargetPoint.InBounds targetCtx.raw}
    (sourceIn : sourceOp.InBounds sourceCtx.raw) (targetIn : targetOp.InBounds targetCtx.raw)
    (related : source.isRefinedByAt targetVars mapping sourcePoint targetPoint sourcePointIn targetPointIn)
    (resultPointers : targetOp.getResults! targetCtx.raw =
      mapping.applyToArray (sourceOp.getResults! sourceCtx.raw))
    (noAlias : ∀ (value : ValuePtr) (valueIn : value.InBounds sourceCtx.raw),
      value.InScopeAt nextSourcePoint sourceCtx →
      (mapping ⟨value, valueIn⟩).val.InScopeAt nextTargetPoint targetCtx →
      value ∉ sourceOp.getResults! sourceCtx.raw →
      (mapping ⟨value, valueIn⟩).val ∉ targetOp.getResults! targetCtx.raw)
    (sourceFrame : ∀ value, value.InBounds sourceCtx.raw →
      value ∉ sourceOp.getResults! sourceCtx.raw →
      value.InScopeAt nextSourcePoint sourceCtx → value.InScopeAt sourcePoint sourceCtx)
    (targetFrame : ∀ (value : ValuePtr) (valueIn : value.InBounds sourceCtx.raw),
      value ∉ sourceOp.getResults! sourceCtx.raw →
      value.InScopeAt nextSourcePoint sourceCtx →
      (mapping ⟨value, valueIn⟩).val.InScopeAt nextTargetPoint targetCtx →
      (mapping ⟨value, valueIn⟩).val.InScopeAt targetPoint targetCtx)
    {sourceValues targetValues : Array RuntimeValue}
    (values : RuntimeValue.arrayIsRefinedBy sourceValues targetValues)
    (sourceSet : source.setResultValues? sourceOp sourceValues sourceIn = some newSource)
    (targetSet : targetVars.setResultValues? targetOp targetValues targetIn = some newTargetVars) :
    newSource.isRefinedByAt newTargetVars mapping nextSourcePoint nextTargetPoint
      nextSourceIn nextTargetIn := by
  intro value valueIn sourceScope targetScope sourceValue sourceLookup targetValue targetLookup
  by_cases member : value ∈ sourceOp.getResults! sourceCtx.raw
  · obtain ⟨index, indexIn, resultEq⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp member
    have mapped := ValueMapping.applyToArray_getResults!_ext sourceIn resultPointers.symm
    have sourceSize := VariableState.setResultValues?.getNumRseults!_eq_size sourceSet
    have targetSize := VariableState.setResultValues?.getNumRseults!_eq_size targetSet
    have sourceResult := VariableState.getVar?_getResult_of_setResultValues? indexIn sourceSet
    have targetIndex : index < targetOp.getNumResults! targetCtx.raw := by
      have sizes := congrArg Array.size resultPointers
      grind [ValueMapping.applyToArray, RuntimeValue.arrayIsRefinedBy]
    have targetResult := VariableState.getVar?_getResult_of_setResultValues? targetIndex targetSet
    grind [RuntimeValue.arrayIsRefinedBy]
  · have targetNotResult := noAlias value valueIn sourceScope targetScope member
    have sourceOld := VariableState.getVar?_setResultValues?_of_notMem_getResults! member sourceSet
    have targetOld := VariableState.getVar?_setResultValues?_of_notMem_getResults! targetNotResult targetSet
    rw [sourceOld] at sourceLookup
    rw [targetOld] at targetLookup
    exact related value valueIn (sourceFrame value valueIn member sourceScope)
      (targetFrame value valueIn member sourceScope targetScope) sourceValue sourceLookup targetValue targetLookup


/-- IR-only obligations for one aligned step of a scoped simulation. Aliasing is
excluded only for values live at the successor points, allowing forwarded root
results to share a pointer with an earlier dominating producer. -/
structure ScopedStepFrame {sourceCtx targetCtx : WfIRContext OpCode}
    (mapping : ValueMapping sourceCtx targetCtx) (sourceOp targetOp : OperationPtr)
    (sourceIn : sourceOp.InBounds sourceCtx.raw) (targetIn : targetOp.InBounds targetCtx.raw)
    (sourcePoint targetPoint nextSourcePoint nextTargetPoint : RefinementPoint) : Prop where
  operands : targetOp.getOperands! targetCtx.raw = mapping.applyToArray (sourceOp.getOperands! sourceCtx.raw)
  results : targetOp.getResults! targetCtx.raw = mapping.applyToArray (sourceOp.getResults! sourceCtx.raw)
  sourceOperands : ∀ value ∈ sourceOp.getOperands! sourceCtx.raw, value.InScopeAt sourcePoint sourceCtx
  targetOperands : ∀ (value : ValuePtr) (valueIn : value.InBounds sourceCtx.raw),
    value ∈ sourceOp.getOperands! sourceCtx.raw → (mapping ⟨value, valueIn⟩).val.InScopeAt targetPoint targetCtx
  sourceBack : ∀ value, value.InBounds sourceCtx.raw → value ∉ sourceOp.getResults! sourceCtx.raw →
    value.InScopeAt nextSourcePoint sourceCtx → value.InScopeAt sourcePoint sourceCtx
  targetBack : ∀ (value : ValuePtr) (valueIn : value.InBounds sourceCtx.raw),
    value ∉ sourceOp.getResults! sourceCtx.raw →
    value.InScopeAt nextSourcePoint sourceCtx →
    (mapping ⟨value, valueIn⟩).val.InScopeAt nextTargetPoint targetCtx →
    (mapping ⟨value, valueIn⟩).val.InScopeAt targetPoint targetCtx
  noAlias : ∀ (value : ValuePtr) (valueIn : value.InBounds sourceCtx.raw),
    value.InScopeAt nextSourcePoint sourceCtx →
    (mapping ⟨value, valueIn⟩).val.InScopeAt nextTargetPoint targetCtx →
    value ∉ sourceOp.getResults! sourceCtx.raw →
    (mapping ⟨value, valueIn⟩).val ∉ targetOp.getResults! targetCtx.raw

/-- Installing raw results preserves the scoped state invariant using only a
local scope frame and the target result-conformance obligation. -/
theorem sim_commitOpResults_scoped
    {sourceCtx targetCtx : WfIRContext OpCode} {sourceOp targetOp : OperationPtr}
    {mapping : ValueMapping sourceCtx targetCtx}
    {sourceState : InterpreterState sourceCtx} {targetState : InterpreterState targetCtx}
    {sourcePoint targetPoint nextSourcePoint nextTargetPoint : RefinementPoint}
    {sourcePointIn : sourcePoint.InBounds sourceCtx.raw} {targetPointIn : targetPoint.InBounds targetCtx.raw}
    {nextSourceIn : nextSourcePoint.InBounds sourceCtx.raw} {nextTargetIn : nextTargetPoint.InBounds targetCtx.raw}
    (sourceIn : sourceOp.InBounds sourceCtx.raw) (targetIn : targetOp.InBounds targetCtx.raw)
    (frame : ScopedStepFrame mapping sourceOp targetOp sourceIn targetIn
      sourcePoint targetPoint nextSourcePoint nextTargetPoint)
    (related : ScopedStateRefines mapping sourcePoint targetPoint sourcePointIn targetPointIn sourceState targetState)
    {sourceResult targetResult : Array RuntimeValue × MemoryState × Option ControlFlowAction}
    (outcomes : OperationResult.isRefinedBy sourceResult targetResult)
    (conforms : RuntimeValue.ArrayConforms targetResult.1 (targetOp.getResultTypes! targetCtx.raw)) :
    _root_.CTree.Sim
      (fun t s => ScopedStateRefines mapping nextSourcePoint nextTargetPoint nextSourceIn nextTargetIn s.1 t.1 ∧
        ControlFlowAction.optionIsRefinedBy s.2 t.2)
      (Veir.CTree.commitOpResults targetOp targetState targetIn targetResult)
      (Veir.CTree.commitOpResults sourceOp sourceState sourceIn sourceResult) := by
  cases sourceSet : sourceState.variables.setResultValues? sourceOp sourceResult.1 sourceIn with
  | none =>
    simp only [Veir.CTree.commitOpResults, sourceSet]
    exact sim_fail _ _
  | some newSource =>
    obtain ⟨newTarget, targetSet⟩ :=
      (VariableState.setResultValues?_isSome_iff_conforms targetState.variables targetIn).mp conforms
    have variables := scoped_setResultValues_refined (nextSourceIn := nextSourceIn)
      (nextTargetIn := nextTargetIn) sourceIn targetIn related.2 frame.results
      frame.noAlias frame.sourceBack frame.targetBack outcomes.1 sourceSet targetSet
    simp only [Veir.CTree.commitOpResults, sourceSet, targetSet, _root_.CTree.Sim.pure]
    exact ⟨⟨outcomes.2.1, variables⟩, outcomes.2.2⟩

/-- A shared-effect opcode simulation lifts through scoped SSA operand lookup and
result installation. Unlike full-state lifting this permits stale aliased values
outside the two live scopes, as required by actual replacement mappings. -/
theorem sim_runOpWith_scoped
    {sourceCtx targetCtx : WfIRContext OpCode} {sourceOp targetOp : OperationPtr}
    {mapping : ValueMapping sourceCtx targetCtx}
    {sourceState : InterpreterState sourceCtx} {targetState : InterpreterState targetCtx}
    {sourcePoint targetPoint nextSourcePoint nextTargetPoint : RefinementPoint}
    {sourcePointIn : sourcePoint.InBounds sourceCtx.raw} {targetPointIn : targetPoint.InBounds targetCtx.raw}
    {nextSourceIn : nextSourcePoint.InBounds sourceCtx.raw} {nextTargetIn : nextTargetPoint.InBounds targetCtx.raw}
    (sourceIn : sourceOp.InBounds sourceCtx.raw) (targetIn : targetOp.InBounds targetCtx.raw)
    (frame : ScopedStepFrame mapping sourceOp targetOp sourceIn targetIn
      sourcePoint targetPoint nextSourcePoint nextTargetPoint)
    (related : ScopedStateRefines mapping sourcePoint targetPoint sourcePointIn targetPointIn sourceState targetState)
    {targetValues : Array RuntimeValue}
    (targetGet : targetState.variables.getOperandValues targetOp = some targetValues)
    (targetRaw sourceRaw : Array RuntimeValue → MemoryState →
      Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction))
    (primitive : ∀ sourceValues,
      sourceState.variables.getOperandValues sourceOp = some sourceValues →
      RuntimeValue.arrayIsRefinedBy sourceValues targetValues →
      _root_.CTree.Sim
        (fun t s => OperationResult.isRefinedBy s t ∧
          RuntimeValue.ArrayConforms t.1 (targetOp.getResultTypes! targetCtx.raw))
        (targetRaw targetValues targetState.memory) (sourceRaw sourceValues sourceState.memory)) :
    _root_.CTree.Sim
      (fun t s => ScopedStateRefines mapping nextSourcePoint nextTargetPoint nextSourceIn nextTargetIn s.1 t.1 ∧
        ControlFlowAction.optionIsRefinedBy s.2 t.2)
      (Veir.CTree.runOpWith targetOp targetState targetIn targetRaw)
      (Veir.CTree.runOpWith sourceOp sourceState sourceIn sourceRaw) := by
  cases sourceGet : sourceState.variables.getOperandValues sourceOp with
  | none =>
    simp only [Veir.CTree.runOpWith, sourceGet]
    exact sim_fail _ _
  | some sourceValues =>
    have values := scoped_operandValues_refined sourceIn related.2 frame.operands
      frame.sourceOperands frame.targetOperands sourceGet targetGet
    simp only [Veir.CTree.runOpWith, sourceGet, targetGet]
    apply _root_.CTree.Sim.bind _ _ _ _ (primitive sourceValues sourceGet values)
    intro t s outcomes
    exact sim_commitOpResults_scoped sourceIn targetIn frame related outcomes.1 outcomes.2


/-- Crossing the rewritten root relates its checked source results to the actual
replacement-pointer values in the target state. Replacement pointers may alias
older target values; no global result-reflection condition is imposed. -/
theorem scoped_rootResults_refined
    {sourceCtx targetCtx : WfIRContext OpCode} {root : OperationPtr}
    {mapping : ValueMapping sourceCtx targetCtx}
    {source newSource : VariableState sourceCtx} {target : VariableState targetCtx}
    {sourcePoint targetPoint : RefinementPoint}
    {sourcePointIn : sourcePoint.InBounds sourceCtx.raw}
    {targetPointIn : targetPoint.InBounds targetCtx.raw}
    (rootIn : root.InBounds sourceCtx.raw)
    (replacements : Array ValuePtr)
    (resultMapping : replacements = mapping.applyToArray (root.getResults! sourceCtx.raw))
    (oldValues : ∀ (value : ValuePtr) (valueIn : value.InBounds sourceCtx.raw),
      value ∉ root.getResults! sourceCtx.raw →
      value.InScopeAt sourcePoint sourceCtx →
      (mapping ⟨value, valueIn⟩).val.InScopeAt targetPoint targetCtx →
      ∀ sourceValue targetValue,
      source.getVar? value = some sourceValue →
      target.getVar? (mapping ⟨value, valueIn⟩) = some targetValue →
      RuntimeValue.isRefinedBy sourceValue targetValue)
    {sourceValues targetValues : Array RuntimeValue}
    (values : RuntimeValue.arrayIsRefinedBy sourceValues targetValues)
    (sourceSet : source.setResultValues? root sourceValues rootIn = some newSource)
    (targetGet : replacements.mapM target.getVar? = some targetValues) :
    newSource.isRefinedByAt target mapping sourcePoint targetPoint sourcePointIn targetPointIn := by
  intro value valueIn sourceScope targetScope sourceValue sourceLookup targetValue targetLookup
  by_cases member : value ∈ root.getResults! sourceCtx.raw
  · obtain ⟨index, indexIn, resultEq⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp member
    have sourceResult := VariableState.getVar?_getResult_of_setResultValues? indexIn sourceSet
    have sourceSize := VariableState.setResultValues?.getNumRseults!_eq_size sourceSet
    have replacementSize : index < replacements.size := by
      have sizes := congrArg Array.size resultMapping
      grind [ValueMapping.applyToArray]
    have targetResult := Array.mapM_option_eq_some_implies targetGet index (by grind)
    grind [ValueMapping.applyToArray, RuntimeValue.arrayIsRefinedBy]
  · have unchanged := VariableState.getVar?_setResultValues?_of_notMem_getResults! member sourceSet
    rw [unchanged] at sourceLookup
    exact oldValues value valueIn member sourceScope targetScope sourceValue targetValue sourceLookup targetLookup

/-- The actual successful driver replacement executes a checked created batch
that refines the original root primitive. Output verification is explicit. -/
theorem Pattern.Valid.checked_createdOps_sim_refiningInputs
    {rule : Veir.Puddle.Pattern OpCode} (valid : Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (ctxDom : rewriter.ctx.Dom irRoot) (rootRooted : root.RootedAt irRoot rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (rootSSA : region.hasSSADominance rewriter.ctx)
    (rootReachable : root.HierarchicallyReachable rewriter.ctx)
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (rootVerified : root.Verified rewriter.ctx rootIn)
    (outputVerified : ∀ op ∈ newOps, ∀ hop : op.InBounds result.ctx.raw, op.Verified result.ctx hop)
    (targetState : InterpreterState result.ctx) (sourceMemory : MemoryState)
    (executionFacts : ∀ matched, rule.matcher.run rewriter.ctx.raw root = some matched →
      ∀ decl ∈ rule.matcher.decls,
        MatchDecl.RuntimeEquations rewriter.ctx.raw rule.matcher.rootHandle
          targetState.variables.getVar? matched decl)
    {targetValues : List RuntimeValue}
    (resolved : (root.getOperands! rewriter.ctx.raw).toList.mapM
      targetState.variables.getVar? = some targetValues)
    (sourceValues : Array RuntimeValue)
    (conforms : RuntimeValue.ArrayConforms sourceValues (root.getOperandTypes! rewriter.ctx.raw))
    (values : RuntimeValue.arrayIsRefinedBy sourceValues targetValues.toArray)
    (memory : sourceMemory.isRefinedBy targetState.memory) :
    _root_.CTree.Sim (fun target source => ∃ results,
      replacements.toList.mapM target.variables.getVar? = some results ∧
      OperationResult.isRefinedBy source (results.toArray, target.memory, none))
      (interpretCreatedOpsChecked result.ctx newOps.toList targetState)
      (Veir.OperationPtr.interpretCTree root rootIn sourceValues sourceMemory) := by
  have fields := valid.fromLocalRewrite_created_fields ctxDom rootRooted rootRegion rootSSA
    rootReachable localRun run attached regions
  have bounds : ∀ op ∈ newOps.toList, op.InBounds result.ctx.raw := by
    intro op member
    exact (fields op (by simpa using member)).1
  have nonterm : ∀ op ∈ newOps.toList, (op.getOpType! result.ctx.raw).isTerminator = false := by
    intro op member
    exact valid.fromLocalRewrite_created_nonterminator ctxDom rootRooted rootRegion rootSSA
      rootReachable localRun run attached regions op (by simpa using member)
  apply sim_checked_createdOps_of_local replacements rootIn targetState
    targetState.variables.getVar? targetState.memory ⟨rfl, fun _ _ => rfl⟩ bounds nonterm
    (CreatedResultsConform.of_verified bounds
      (fun op member => outputVerified op (by simpa using member) _) nonterm)
  · intro pointer member
    exact valid.fromLocalRewrite_replacementsInBounds ctxDom rootRooted rootRegion rootSSA
      rootReachable localRun run attached regions pointer (by simpa using member)
  · intro op member
    exact (fields op (by simpa using member)).2
  · exact valid.interpret_createdOpsFinal_sim_refiningInputs targetState.variables.getVar?
      sourceMemory targetState.memory localRun rootIn rootVerified executionFacts resolved
      sourceValues conforms values memory

/-- A linked non-control-flow instruction list is exactly a finite CFG batch. -/
theorem cfgSteps_eq_checkedList {ctx : WfIRContext OpCode}
    (ops : List OperationPtr) (first next : OperationPtr)
    (firstIn : first.InBounds ctx.raw) (nextIn : next.InBounds ctx.raw)
    (starts : ops.head? = some first)
    (bounds : ∀ op ∈ ops, op.InBounds ctx.raw)
    (chain : ForwardChain ctx.raw ops (some next))
    (noAction : ∀ op (member : op ∈ ops) (state : InterpreterState ctx) result,
      PureOrErr.CanInterpretTo (Veir.CTree.interpretOpCore op state (bounds op member))
        (.ok result) → result.2 = none)
    (state : InterpreterState ctx) :
    _root_.CTree.iterSteps (fun (location, state) => Veir.CTree.interpretCFGCore.iter location state)
      ops.length (.inr ⟨first, firstIn⟩, state) =
      (interpretCreatedOpsChecked ctx ops state >>= fun final =>
        pure (.inl (.inr ⟨next, nextIn⟩, final))) := by
  induction ops generalizing first state with
  | nil => simp at starts
  | cons op ops ih =>
    have firstEq : op = first := by simpa using starts
    subst first
    have opIn := bounds op (by simp)
    cases ops with
    | nil =>
      have nextEq : op.getNextOp! ctx.raw = some next := chain
      rw [List.length_cons, List.length_nil, _root_.CTree.iterSteps_one]
      dsimp only
      rw [CFGCore_step_eq_checked op next firstIn nextIn nextEq (noAction op (by simp))]
      simp only [interpretCreatedOpsChecked, firstIn, dite_true]
      simp only [_root_.CTree.bind_assoc, _root_.LawfulMonad.pure_bind]
    | cons second rest =>
      have secondIn := bounds second (by simp)
      have nextEq : op.getNextOp! ctx.raw = some second := chain.1
      simp only [List.length_cons]
      unfold _root_.CTree.iterSteps
      dsimp only
      rw [CFGCore_step_eq_checked op second firstIn secondIn nextEq (noAction op (by simp))]
      simp only [_root_.CTree.bind_assoc, _root_.LawfulMonad.pure_bind]
      simp only [interpretCreatedOpsChecked, firstIn, dite_true]
      rw [_root_.CTree.bind_assoc]
      congr 1
      funext outcome
      simpa only [List.length_cons, interpretCreatedOpsChecked, secondIn, dite_true] using
        ih second secondIn rfl (fun x hx => bounds x (by simp [hx])) chain.2
        (fun x hx => noAction x (by simp [hx])) outcome.1

/-- Replacement lookup and the frame on older slots suffice to commit the
source root, including replacements that forward an existing SSA value. -/
theorem sim_commitRoot_scoped
    {sourceCtx targetCtx : WfIRContext OpCode} {root : OperationPtr}
    {mapping : ValueMapping sourceCtx targetCtx}
    (sourceState : InterpreterState sourceCtx) (targetState : InterpreterState targetCtx)
    {sourcePoint targetPoint : RefinementPoint}
    {sourcePointIn : sourcePoint.InBounds sourceCtx.raw}
    {targetPointIn : targetPoint.InBounds targetCtx.raw}
    (rootIn : root.InBounds sourceCtx.raw) (replacements : Array ValuePtr)
    (resultMapping : replacements = mapping.applyToArray (root.getResults! sourceCtx.raw))
    (oldValues : ∀ (value : ValuePtr) (valueIn : value.InBounds sourceCtx.raw),
      value ∉ root.getResults! sourceCtx.raw →
      value.InScopeAt sourcePoint sourceCtx →
      (mapping ⟨value, valueIn⟩).val.InScopeAt targetPoint targetCtx →
      ∀ sourceValue targetValue,
      sourceState.variables.getVar? value = some sourceValue →
      targetState.variables.getVar? (mapping ⟨value, valueIn⟩) = some targetValue →
      RuntimeValue.isRefinedBy sourceValue targetValue)
    (sourceResult : Array RuntimeValue × MemoryState × Option ControlFlowAction)
    (replacementValues : Array RuntimeValue)
    (lookup : replacements.mapM targetState.variables.getVar? = some replacementValues)
    (outcomes : OperationResult.isRefinedBy sourceResult
      (replacementValues, targetState.memory, none)) :
    _root_.CTree.Sim
      (fun target source => ScopedStateRefines mapping sourcePoint targetPoint
        sourcePointIn targetPointIn source.1 target ∧ source.2 = none)
      (pure targetState : Tree (InterpreterState targetCtx))
      (Veir.CTree.commitOpResults root sourceState rootIn sourceResult) := by
  cases sourceSet : sourceState.variables.setResultValues? root sourceResult.1 rootIn with
  | none =>
    simp only [Veir.CTree.commitOpResults, sourceSet]
    exact sim_fail _ _
  | some newSource =>
    have variables := scoped_rootResults_refined (sourcePointIn := sourcePointIn)
      (targetPointIn := targetPointIn) rootIn replacements resultMapping oldValues
      outcomes.1 sourceSet lookup
    have action : sourceResult.2.2 = none := by
      have related := outcomes.2.2
      cases actionEq : sourceResult.2.2 <;> simp_all [ControlFlowAction.optionIsRefinedBy]
    simp only [Veir.CTree.commitOpResults, sourceSet, _root_.CTree.Sim.pure]
    exact ⟨⟨outcomes.2.1, variables⟩, action⟩

theorem interpretOpCore_no_action_of_nonterm {ctx : WfIRContext OpCode}
    (op : OperationPtr) (opIn : op.InBounds ctx.raw)
    (nonterm : (op.getOpType! ctx.raw).isTerminator = false)
    (state : InterpreterState ctx) (result : InterpreterState ctx × Option ControlFlowAction)
    (outcome : PureOrErr.CanInterpretTo (Veir.CTree.interpretOpCore op state opIn) (.ok result)) :
    result.2 = none := by
  unfold Veir.CTree.interpretOpCore Veir.CTree.runOpWith at outcome
  cases collected : state.variables.getOperandValues op with
  | none => simp [collected, fail, _root_.CTree.CTree.trigger_def, PureOrErr.CanInterpretTo.vis_iff] at outcome
  | some operands =>
    simp only [collected] at outcome
    obtain ⟨raw, rawOutcome, committed⟩ :=
      (PureOrErr.CanInterpretTo.bind_iff _ _ _).mp outcome |>.resolve_right (by simp)
    rw [interpretCTree_eq_bang op opIn] at rawOutcome
    have action := Veir.CTree.interpretOp'_no_action_of_nonterm
      (op.getOpType! ctx.raw) (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
      (op.getResultTypes! ctx.raw) operands (op.getSuccessors! ctx.raw)
      state.memory raw.2.1 raw.1 raw.2.2 #[] nonterm rawOutcome
    unfold Veir.CTree.commitOpResults at committed
    cases installed : state.variables.setResultValues? op raw.1 opIn with
    | none => simp [installed, fail, _root_.CTree.CTree.trigger_def, PureOrErr.CanInterpretTo.vis_iff] at committed
    | some variables =>
      simp only [installed, PureOrErr.CanInterpretTo.pure_iff] at committed
      cases committed
      exact action

/-- The fresh-list frame closes checked root replacement under the scoped
invariant. Older values are compared at the successor scopes. -/
theorem sim_checked_createdOps_rootCore
    {rule : Veir.Puddle.Pattern OpCode} {sourceCtx created targetCtx : WfIRContext OpCode}
    {root : OperationPtr} {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret sourceCtx root = some (created, some (newOps, replacements)))
    (rootIn : root.InBounds sourceCtx.raw)
    (sourceState : InterpreterState sourceCtx) (targetState : InterpreterState targetCtx)
    (sourceValues : Array RuntimeValue)
    (sourceGet : sourceState.variables.getOperandValues root = some sourceValues)
    {mapping : ValueMapping sourceCtx targetCtx}
    {sourcePoint targetPoint : RefinementPoint}
    {sourcePointIn : sourcePoint.InBounds sourceCtx.raw}
    {targetPointIn : targetPoint.InBounds targetCtx.raw}
    (resultMapping : replacements = mapping.applyToArray (root.getResults! sourceCtx.raw))
    (fixedOther : ∀ value (valueIn : value.InBounds sourceCtx.raw),
      value ∉ root.getResults! sourceCtx.raw → (mapping ⟨value, valueIn⟩).val = value)
    (oldValues : ∀ (value : ValuePtr) (valueIn : value.InBounds sourceCtx.raw),
      value ∉ root.getResults! sourceCtx.raw →
      value.InScopeAt sourcePoint sourceCtx →
      (mapping ⟨value, valueIn⟩).val.InScopeAt targetPoint targetCtx →
      ∀ sourceValue targetValue,
      sourceState.variables.getVar? value = some sourceValue →
      targetState.variables.getVar? (mapping ⟨value, valueIn⟩) = some targetValue →
      RuntimeValue.isRefinedBy sourceValue targetValue)
    (localSimulation : _root_.CTree.Sim (fun target source => ∃ results,
      replacements.toList.mapM target.variables.getVar? = some results ∧
      OperationResult.isRefinedBy source (results.toArray, target.memory, none))
      (interpretCreatedOpsChecked targetCtx newOps.toList targetState)
      (Veir.OperationPtr.interpretCTree root rootIn sourceValues sourceState.memory)) :
    _root_.CTree.Sim
      (fun target source => ScopedStateRefines mapping sourcePoint targetPoint
        sourcePointIn targetPointIn source.1 target ∧ source.2 = none)
      (interpretCreatedOpsChecked targetCtx newOps.toList targetState)
      (Veir.CTree.interpretOpCore root sourceState rootIn) := by
  have enriched : _root_.CTree.Sim (fun target source =>
      (∀ value, value.InBounds sourceCtx.raw →
        target.variables.getVar? value = targetState.variables.getVar? value) ∧
      ∃ results, replacements.toList.mapM target.variables.getVar? = some results ∧
        OperationResult.isRefinedBy source (results.toArray, target.memory, none))
      (interpretCreatedOpsChecked targetCtx newOps.toList targetState)
      (Veir.OperationPtr.interpretCTree root rootIn sourceValues sourceState.memory) := by
    apply _root_.CTree.Sim.trans
      (Pattern.interpret_checked_sim_preserves_source_lookups rule localRun targetState) localSimulation
    rintro target intermediate source ⟨equal, frame⟩ observed
    subst intermediate
    exact ⟨frame, observed⟩
  have committed := _root_.CTree.Sim.bind
    (RR' := fun target source => ScopedStateRefines mapping sourcePoint targetPoint
      sourcePointIn targetPointIn source.1 target ∧ source.2 = none) _ _
    (fun final => (pure final : Tree (InterpreterState targetCtx)))
    (Veir.CTree.commitOpResults root sourceState rootIn) enriched
    (fun target source related => ?_)
  · change _root_.CTree.Sim _
      (interpretCreatedOpsChecked targetCtx newOps.toList targetState >>= pure) _ at committed
    rw [_root_.bind_pure] at committed
    simpa only [Veir.CTree.interpretOpCore, Veir.CTree.runOpWith, sourceGet, Bind.bind] using committed
  · obtain ⟨frame, results, lookup, outcomes⟩ := related
    apply sim_commitRoot_scoped sourceState target rootIn replacements resultMapping
      (replacementValues := results.toArray) (sourceResult := source)
    · intro value valueIn notResult sourceScope targetScope sourceValue targetValue sourceLookup targetLookup
      apply oldValues value valueIn notResult sourceScope targetScope sourceValue targetValue sourceLookup
      have same := frame value valueIn
      rw [fixedOther value valueIn notResult] at targetLookup ⊢
      exact same.symm.trans targetLookup
    · rw [Array.mapM_eq_mapM_toList, lookup]
      rfl
    · exact outcomes

/-- A checked replacement-list simulation gives the corresponding concrete CFG
batch simulation, with both machines positioned at their actual successors. -/
theorem sim_cfgBatch_of_checkedRoot
    {sourceCtx targetCtx : WfIRContext OpCode}
    (ops : List OperationPtr) (first targetNext root sourceNext : OperationPtr)
    (firstIn : first.InBounds targetCtx.raw) (targetNextIn : targetNext.InBounds targetCtx.raw)
    (rootIn : root.InBounds sourceCtx.raw) (sourceNextIn : sourceNext.InBounds sourceCtx.raw)
    (starts : ops.head? = some first)
    (bounds : ∀ op ∈ ops, op.InBounds targetCtx.raw)
    (chain : ForwardChain targetCtx.raw ops (some targetNext))
    (targetNonterm : ∀ op ∈ ops, (op.getOpType! targetCtx.raw).isTerminator = false)
    (rootNonterm : (root.getOpType! sourceCtx.raw).isTerminator = false)
    (sourceNextEq : root.getNextOp! sourceCtx.raw = some sourceNext)
    (sourceState : InterpreterState sourceCtx) (targetState : InterpreterState targetCtx)
    (related : InterpreterState targetCtx → InterpreterState sourceCtx → Prop)
    (batch : _root_.CTree.Sim (fun target source => related target source.1)
      (interpretCreatedOpsChecked targetCtx ops targetState)
      (Veir.CTree.interpretOpCore root sourceState rootIn))
    {reachable : (Veir.CTree.interpretCFG.StateLocation targetCtx ×
      InterpreterState targetCtx) →
      (Veir.CTree.interpretCFG.StateLocation sourceCtx ×
      InterpreterState sourceCtx) → Prop}
    (successors : ∀ target source, related target source →
      reachable (.inr ⟨targetNext, targetNextIn⟩, target) (.inr ⟨sourceNext, sourceNextIn⟩, source)) :
    _root_.CTree.Sim (Sum.LiftRel reachable (fun _ _ => False))
      (_root_.CTree.iterSteps (fun (location, state) => Veir.CTree.interpretCFGCore.iter location state)
        ops.length (.inr ⟨first, firstIn⟩, targetState))
      (Veir.CTree.interpretCFGCore.iter (.inr ⟨root, rootIn⟩) sourceState) := by
  rw [cfgSteps_eq_checkedList ops first targetNext firstIn targetNextIn starts bounds chain
    (fun op member => interpretOpCore_no_action_of_nonterm op _ (targetNonterm op member))]
  rw [CFGCore_step_eq_checked root sourceNext rootIn sourceNextIn sourceNextEq
    (interpretOpCore_no_action_of_nonterm root rootIn rootNonterm)]
  apply _root_.CTree.Sim.bind _ _ _ _ batch
  intro target source h
  simp only [_root_.CTree.Sim.pure]
  exact .inl (successors target source.1 h)

/-- Deleting a root uses a positive source batch of two steps: execute the
removed root and then its successor, against one target successor step. -/
theorem sim_cfgDeletedRoot
    {sourceCtx targetCtx : WfIRContext OpCode} (root next : OperationPtr)
    (rootIn : root.InBounds sourceCtx.raw) (nextIn : next.InBounds sourceCtx.raw)
    (nextEq : root.getNextOp! sourceCtx.raw = some next)
    (nonterm : (root.getOpType! sourceCtx.raw).isTerminator = false)
    (sourceState : InterpreterState sourceCtx) (targetState : InterpreterState targetCtx)
    (targetStep : InterpreterState targetCtx → Tree α)
    (relation : α → (Veir.CTree.interpretCFG.StateLocation sourceCtx × InterpreterState sourceCtx ⊕
      InterpreterState sourceCtx × Array RuntimeValue) → Prop)
    (related : InterpreterState targetCtx → InterpreterState sourceCtx → Prop)
    (deleted : _root_.CTree.Sim (fun target source => related target source.1)
      (pure targetState : Tree (InterpreterState targetCtx))
      (Veir.CTree.interpretOpCore root sourceState rootIn))
    (successorStep : ∀ target (source : InterpreterState sourceCtx × Option ControlFlowAction), related target source.1 →
      _root_.CTree.Sim relation (targetStep target)
        (Veir.CTree.interpretCFGCore.iter (.inr ⟨next, nextIn⟩) source.1)) :
    _root_.CTree.Sim relation (targetStep targetState)
      (_root_.CTree.iterSteps (fun (location, state) => Veir.CTree.interpretCFGCore.iter location state)
        2 (.inr ⟨root, rootIn⟩, sourceState)) := by
  have sourceBatch :
      _root_.CTree.iterSteps (fun (location, state) => Veir.CTree.interpretCFGCore.iter location state)
        2 (.inr ⟨root, rootIn⟩, sourceState) =
      (Veir.CTree.interpretOpCore root sourceState rootIn >>= fun outcome =>
        Veir.CTree.interpretCFGCore.iter (.inr ⟨next, nextIn⟩) outcome.1) := by
    unfold _root_.CTree.iterSteps
    dsimp only
    rw [CFGCore_step_eq_checked root next rootIn nextIn nextEq
      (interpretOpCore_no_action_of_nonterm root rootIn nonterm)]
    simp only [_root_.CTree.bind_assoc, _root_.LawfulMonad.pure_bind]
    congr 1
    funext outcome
    exact _root_.CTree.iterSteps_one _ _
  rw [sourceBatch]
  have simulation := _root_.CTree.Sim.bind _ _ targetStep
    (fun source => Veir.CTree.interpretCFGCore.iter (.inr ⟨next, nextIn⟩) source.1)
    deleted successorStep
  simpa only [Bind.bind, _root_.CTree.bind_pure] using simulation

/-- Preserved primitive metadata gives an identical shared-effect procedure;
SSA operands and CFG locations are handled separately by scoped refinement. -/
theorem interpretCTree_fields_congr
    {sourceCtx targetCtx : WfIRContext OpCode} (sourceOp targetOp : OperationPtr)
    (sourceIn : sourceOp.InBounds sourceCtx.raw) (targetIn : targetOp.InBounds targetCtx.raw)
    (code : targetOp.getOpType! targetCtx.raw = sourceOp.getOpType! sourceCtx.raw)
    (properties : ∀ code : OpCode, targetOp.getProperties! targetCtx.raw code = sourceOp.getProperties! sourceCtx.raw code)
    (types : targetOp.getResultTypes! targetCtx.raw = sourceOp.getResultTypes! sourceCtx.raw)
    (successors : targetOp.getSuccessors! targetCtx.raw = sourceOp.getSuccessors! sourceCtx.raw)
    (values : Array RuntimeValue) (memory : MemoryState) :
    Veir.OperationPtr.interpretCTree targetOp targetIn values memory =
      Veir.OperationPtr.interpretCTree sourceOp sourceIn values memory := by
  rw [interpretCTree_eq_bang targetOp targetIn, interpretCTree_eq_bang sourceOp sourceIn]
  rw [code, properties, types, successors]

/-- Actual surviving instructions preserve scoped states using only the approved
verified primitive contract and concrete IR metadata/scope obligations. -/
theorem sim_interpretOpCore_scoped_of_verified
    (primitive : ∀ opType, Veir.OpCode.interpretCTree_monotone opType)
    {sourceCtx targetCtx : WfIRContext OpCode} {sourceOp targetOp : OperationPtr}
    {sourceState : InterpreterState sourceCtx} {targetState : InterpreterState targetCtx}
    {mapping : ValueMapping sourceCtx targetCtx}
    {sourcePoint targetPoint nextSourcePoint nextTargetPoint : RefinementPoint}
    {sourcePointIn : sourcePoint.InBounds sourceCtx.raw} {targetPointIn : targetPoint.InBounds targetCtx.raw}
    {nextSourceIn : nextSourcePoint.InBounds sourceCtx.raw} {nextTargetIn : nextTargetPoint.InBounds targetCtx.raw}
    (sourceIn : sourceOp.InBounds sourceCtx.raw) (targetIn : targetOp.InBounds targetCtx.raw)
    (verified : sourceOp.Verified sourceCtx sourceIn)
    (frame : ScopedStepFrame mapping sourceOp targetOp sourceIn targetIn
      sourcePoint targetPoint nextSourcePoint nextTargetPoint)
    (states : ScopedStateRefines mapping sourcePoint targetPoint sourcePointIn targetPointIn sourceState targetState)
    (code : targetOp.getOpType! targetCtx.raw = sourceOp.getOpType! sourceCtx.raw)
    (properties : ∀ code : OpCode, targetOp.getProperties! targetCtx.raw code = sourceOp.getProperties! sourceCtx.raw code)
    (types : targetOp.getResultTypes! targetCtx.raw = sourceOp.getResultTypes! sourceCtx.raw)
    (successors : targetOp.getSuccessors! targetCtx.raw = sourceOp.getSuccessors! sourceCtx.raw)
    {targetValues : Array RuntimeValue}
    (targetGet : targetState.variables.getOperandValues targetOp = some targetValues) :
    _root_.CTree.Sim
      (fun t s => ScopedStateRefines mapping nextSourcePoint nextTargetPoint nextSourceIn nextTargetIn s.1 t.1 ∧
        ControlFlowAction.optionIsRefinedBy s.2 t.2)
      (Veir.CTree.interpretOpCore targetOp targetState targetIn)
      (Veir.CTree.interpretOpCore sourceOp sourceState sourceIn) := by
  apply sim_runOpWith_scoped sourceIn targetIn frame states targetGet
    (Veir.OperationPtr.interpretCTree targetOp targetIn) (Veir.OperationPtr.interpretCTree sourceOp sourceIn)
  intro sourceValues sourceGet values
  rw [interpretCTree_fields_congr sourceOp targetOp sourceIn targetIn code properties types successors]
  rw [types]
  exact primitive (sourceOp.getOpType sourceCtx.raw sourceIn) sourceCtx sourceOp sourceIn rfl
    verified sourceValues targetValues sourceState.memory targetState.memory
    (VariableState.getOperandValues_conforms sourceGet) values states.1

/-- Checked root replacement for an actual successful compiler/driver run.
All remaining premises concern verified IR, scoped old slots, or runtime matcher
history; no operation, CFG, function, or module simulation is assumed. -/
theorem Pattern.Valid.checked_createdOps_rootCore
    {rule : Veir.Puddle.Pattern OpCode} (valid : Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (ctxDom : rewriter.ctx.Dom irRoot) (rootRooted : root.RootedAt irRoot rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (rootSSA : region.hasSSADominance rewriter.ctx)
    (rootReachable : root.HierarchicallyReachable rewriter.ctx)
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (rootVerified : root.Verified rewriter.ctx rootIn)
    (outputVerified : ∀ op ∈ newOps, ∀ hop : op.InBounds result.ctx.raw, op.Verified result.ctx hop)
    (sourceState : InterpreterState rewriter.ctx) (targetState : InterpreterState result.ctx)
    (executionFacts : ∀ matched, rule.matcher.run rewriter.ctx.raw root = some matched →
      ∀ decl ∈ rule.matcher.decls,
        MatchDecl.RuntimeEquations rewriter.ctx.raw rule.matcher.rootHandle
          targetState.variables.getVar? matched decl)
    {targetValues : List RuntimeValue}
    (resolved : (root.getOperands! rewriter.ctx.raw).toList.mapM
      targetState.variables.getVar? = some targetValues)
    (sourceValues : Array RuntimeValue)
    (sourceGet : sourceState.variables.getOperandValues root = some sourceValues)
    (values : RuntimeValue.arrayIsRefinedBy sourceValues targetValues.toArray)
    (memory : sourceState.memory.isRefinedBy targetState.memory)
    {mapping : ValueMapping rewriter.ctx result.ctx}
    {sourcePoint targetPoint : RefinementPoint}
    {sourcePointIn : sourcePoint.InBounds rewriter.ctx.raw}
    {targetPointIn : targetPoint.InBounds result.ctx.raw}
    (resultMapping : replacements = mapping.applyToArray (root.getResults! rewriter.ctx.raw))
    (fixedOther : ∀ value (valueIn : value.InBounds rewriter.ctx.raw),
      value ∉ root.getResults! rewriter.ctx.raw → (mapping ⟨value, valueIn⟩).val = value)
    (oldValues : ∀ (value : ValuePtr) (valueIn : value.InBounds rewriter.ctx.raw),
      value ∉ root.getResults! rewriter.ctx.raw →
      value.InScopeAt sourcePoint rewriter.ctx →
      (mapping ⟨value, valueIn⟩).val.InScopeAt targetPoint result.ctx →
      ∀ sourceValue targetValue,
      sourceState.variables.getVar? value = some sourceValue →
      targetState.variables.getVar? (mapping ⟨value, valueIn⟩) = some targetValue →
      RuntimeValue.isRefinedBy sourceValue targetValue) :
    _root_.CTree.Sim
      (fun target source => ScopedStateRefines mapping sourcePoint targetPoint
        sourcePointIn targetPointIn source.1 target ∧ source.2 = none)
      (interpretCreatedOpsChecked result.ctx newOps.toList targetState)
      (Veir.CTree.interpretOpCore root sourceState rootIn) := by
  apply sim_checked_createdOps_rootCore localRun rootIn sourceState targetState sourceValues
    sourceGet resultMapping fixedOther oldValues
  exact valid.checked_createdOps_sim_refiningInputs ctxDom rootRooted rootRegion rootSSA
    rootReachable localRun run attached regions rootVerified outputVerified targetState sourceState.memory
    executionFacts resolved sourceValues (VariableState.getOperandValues_conforms sourceGet) values memory

/-- Older SSA values live after a linked inserted batch were already live
before its first operation. Fresh intermediate result slots are excluded. -/
theorem scope_back_through_chain {ctx : WfIRContext OpCode}
    (ops : List OperationPtr) (first next : OperationPtr) (block : BlockPtr)
    (starts : ops.head? = some first)
    (bounds : ∀ op ∈ ops, op.InBounds ctx.raw)
    (parents : ∀ op ∈ ops, op.getParent! ctx.raw = some block)
    (blockParent : block.getParent! ctx.raw = some region)
    (chain : ForwardChain ctx.raw ops (some next))
    (value : ValuePtr) (fresh : ∀ op ∈ ops, value ∉ op.getResults! ctx.raw)
    (live : value.InScopeAt (.at (.before next)) ctx) :
    value.InScopeAt (.at (.before first)) ctx := by
  induction ops generalizing first with
  | nil => simp at starts
  | cons op ops ih =>
    have firstEq : op = first := by simpa using starts
    subst first
    cases ops with
    | nil =>
      exact ValuePtr.inScopeAt_before_of_before_next (parents op (by simp))
        (bounds op (by simp)) blockParent chain live (fresh op (by simp))
    | cons second rest =>
      have secondLive := ih second rfl (fun x hx => bounds x (by simp [hx]))
        (fun x hx => parents x (by simp [hx])) chain.2 (fun x hx => fresh x (by simp [hx]))
      exact ValuePtr.inScopeAt_before_of_before_next (parents op (by simp))
        (bounds op (by simp)) blockParent chain.1 secondLive (fresh op (by simp))

/-- The older-slot premise of checked root replacement follows from the entry
scoped invariant and concrete source/target linked-list scope frames. -/
theorem root_oldValues_of_scoped
    {sourceCtx targetCtx : WfIRContext OpCode} {mapping : ValueMapping sourceCtx targetCtx}
    {sourceState : InterpreterState sourceCtx} {targetState : InterpreterState targetCtx}
    (root sourceNext targetFirst targetNext : OperationPtr) (ops : List OperationPtr)
    (sourceBlock targetBlock : BlockPtr)
    (rootIn : root.InBounds sourceCtx.raw)
    (sourceParent : root.getParent! sourceCtx.raw = some sourceBlock)
    (sourceBlockParent : sourceBlock.getParent! sourceCtx.raw = some sourceRegion)
    (sourceNextEq : root.getNextOp! sourceCtx.raw = some sourceNext)
    (starts : ops.head? = some targetFirst)
    (bounds : ∀ op ∈ ops, op.InBounds targetCtx.raw)
    (parents : ∀ op ∈ ops, op.getParent! targetCtx.raw = some targetBlock)
    (targetBlockParent : targetBlock.getParent! targetCtx.raw = some targetRegion)
    (chain : ForwardChain targetCtx.raw ops (some targetNext))
    (fresh : ∀ value, value.InBounds sourceCtx.raw → ∀ op ∈ ops, value ∉ op.getResults! targetCtx.raw)
    (fixedOther : ∀ value (valueIn : value.InBounds sourceCtx.raw),
      value ∉ root.getResults! sourceCtx.raw → (mapping ⟨value, valueIn⟩).val = value)
    {sourcePointIn : (RefinementPoint.at (.before root)).InBounds sourceCtx.raw}
    {targetPointIn : (RefinementPoint.at (.before targetFirst)).InBounds targetCtx.raw}
    (states : ScopedStateRefines mapping (.at (.before root)) (.at (.before targetFirst))
      sourcePointIn targetPointIn sourceState targetState) :
    ∀ (value : ValuePtr) (valueIn : value.InBounds sourceCtx.raw),
      value ∉ root.getResults! sourceCtx.raw →
      value.InScopeAt (.at (.before sourceNext)) sourceCtx →
      (mapping ⟨value, valueIn⟩).val.InScopeAt (.at (.before targetNext)) targetCtx →
      ∀ sourceValue targetValue,
      sourceState.variables.getVar? value = some sourceValue →
      targetState.variables.getVar? (mapping ⟨value, valueIn⟩) = some targetValue →
      RuntimeValue.isRefinedBy sourceValue targetValue := by
  intro value valueIn notResult sourceScope targetScope sourceValue targetValue sourceGet targetGet
  have sourceBefore := ValuePtr.inScopeAt_before_of_before_next sourceParent rootIn
    sourceBlockParent sourceNextEq sourceScope notResult
  have targetFresh : ∀ op ∈ ops, (mapping ⟨value, valueIn⟩).val ∉ op.getResults! targetCtx.raw := by
    simpa only [fixedOther value valueIn notResult] using fresh value valueIn
  have targetBefore := scope_back_through_chain ops targetFirst targetNext targetBlock starts
    bounds parents targetBlockParent chain _ targetFresh targetScope
  exact states.2 value valueIn sourceBefore targetBefore sourceValue sourceGet targetValue targetGet

/-- Straight-line scope frames require only linked successors and source-scoped
alias exclusion; target scope propagation follows from the same linked edge. -/
theorem ScopedStepFrame.of_straightLine
    {sourceCtx targetCtx : WfIRContext OpCode} {mapping : ValueMapping sourceCtx targetCtx}
    (sourceOp targetOp sourceNext targetNext : OperationPtr) (sourceBlock targetBlock : BlockPtr)
    (sourceIn : sourceOp.InBounds sourceCtx.raw) (targetIn : targetOp.InBounds targetCtx.raw)
    (sourceParent : sourceOp.getParent! sourceCtx.raw = some sourceBlock)
    (targetParent : targetOp.getParent! targetCtx.raw = some targetBlock)
    (sourceBlockParent : sourceBlock.getParent! sourceCtx.raw = some sourceRegion)
    (targetBlockParent : targetBlock.getParent! targetCtx.raw = some targetRegion)
    (sourceNextEq : sourceOp.getNextOp! sourceCtx.raw = some sourceNext)
    (targetNextEq : targetOp.getNextOp! targetCtx.raw = some targetNext)
    (operands : targetOp.getOperands! targetCtx.raw = mapping.applyToArray (sourceOp.getOperands! sourceCtx.raw))
    (results : targetOp.getResults! targetCtx.raw = mapping.applyToArray (sourceOp.getResults! sourceCtx.raw))
    (sourceOperands : ∀ value ∈ sourceOp.getOperands! sourceCtx.raw,
      value.InScopeAt (.at (.before sourceOp)) sourceCtx)
    (targetOperands : ∀ value (valueIn : value.InBounds sourceCtx.raw),
      value ∈ sourceOp.getOperands! sourceCtx.raw →
      (mapping ⟨value, valueIn⟩).val.InScopeAt (.at (.before targetOp)) targetCtx)
    (noAlias : ∀ value (valueIn : value.InBounds sourceCtx.raw),
      value.InScopeAt (.at (.before sourceNext)) sourceCtx →
      value ∉ sourceOp.getResults! sourceCtx.raw →
      (mapping ⟨value, valueIn⟩).val ∉ targetOp.getResults! targetCtx.raw) :
    ScopedStepFrame mapping sourceOp targetOp sourceIn targetIn
      (.at (.before sourceOp)) (.at (.before targetOp))
      (.at (.before sourceNext)) (.at (.before targetNext)) := by
  refine ⟨operands, results, sourceOperands, targetOperands, ?_, ?_, ?_⟩
  · intro value valueIn notResult live
    exact ValuePtr.inScopeAt_before_of_before_next sourceParent sourceIn sourceBlockParent
      sourceNextEq live notResult
  · intro value valueIn notResult sourceLive live
    exact ValuePtr.inScopeAt_before_of_before_next targetParent targetIn targetBlockParent
      targetNextEq live (noAlias value valueIn sourceLive notResult)
  · intro value valueIn sourceLive _ notResult
    exact noAlias value valueIn sourceLive notResult

/-- Finite primitive simulations can retain successful outcome witnesses for
both concrete trees, allowing historical SSA invariants to be updated. -/
theorem sim_with_outcomes {α β : Type} {target : Tree α} {source : Tree β}
    (targetShape : PureOrErr target) (sourceShape : PureOrErr source)
    (relation : α → β → Prop) (simulation : _root_.CTree.Sim relation target source) :
    _root_.CTree.Sim (fun t s => relation t s ∧
      PureOrErr.CanInterpretTo target (.ok t) ∧ PureOrErr.CanInterpretTo source (.ok s))
      target source := by
  have targetWitness : _root_.CTree.Sim (fun t s => relation t s ∧
      PureOrErr.CanInterpretTo target (.ok t)) target source := by
    apply _root_.CTree.Sim.trans (PureOrErr.sim_with_outcome targetShape) simulation
    rintro t intermediate s ⟨equal, outcome⟩ related
    subst intermediate
    exact ⟨related, outcome⟩
  apply _root_.CTree.Sim.trans targetWitness (PureOrErr.sim_with_outcome sourceShape)
  rintro t intermediate s ⟨related, targetOutcome⟩ ⟨equal, sourceOutcome⟩
  subst intermediate
  exact ⟨related, targetOutcome, sourceOutcome⟩

/-- A checked instruction return exposes its actual primitive event and exact
SSA result installation, for updating definedness and historical equations. -/
theorem interpretOpCore_outcome {ctx : WfIRContext OpCode}
    (op : OperationPtr) (opIn : op.InBounds ctx.raw)
    (state : InterpreterState ctx) (result : InterpreterState ctx × Option ControlFlowAction)
    (outcome : PureOrErr.CanInterpretTo (Veir.CTree.interpretOpCore op state opIn) (.ok result)) :
    ∃ operands raw,
      state.variables.getOperandValues op = some operands ∧
      PureOrErr.CanInterpretTo (Veir.OperationPtr.interpretCTree op opIn operands state.memory) (.ok raw) ∧
      state.variables.setResultValues? op raw.1 opIn = some result.1.variables ∧
      result.1.memory = raw.2.1 ∧ result.2 = raw.2.2 := by
  unfold Veir.CTree.interpretOpCore Veir.CTree.runOpWith at outcome
  cases collected : state.variables.getOperandValues op with
  | none =>
    simp [collected, fail, _root_.CTree.CTree.trigger_def, PureOrErr.CanInterpretTo.vis_iff] at outcome
  | some operands =>
    simp only [collected] at outcome
    obtain ⟨raw, rawOutcome, committed⟩ :=
      (PureOrErr.CanInterpretTo.bind_iff _ _ _).mp outcome |>.resolve_right (by simp)
    unfold Veir.CTree.commitOpResults at committed
    cases installed : state.variables.setResultValues? op raw.1 opIn with
    | none =>
      simp [installed, fail, _root_.CTree.CTree.trigger_def, PureOrErr.CanInterpretTo.vis_iff] at committed
    | some variables =>
      simp only [installed, PureOrErr.CanInterpretTo.pure_iff] at committed
      cases committed
      exact ⟨operands, raw, rfl, rawOutcome, installed, rfl, rfl⟩

theorem interpretCFGCore_eq_of_firstBlock {ctx : WfIRContext OpCode}
    (region : RegionPtr) (regionIn : region.InBounds ctx.raw) (first : BlockPtr)
    (firstIn : first.InBounds ctx.raw)
    (firstGet : region.getFirstBlock ctx.raw regionIn = some first)
    (values : Array RuntimeValue) (state : InterpreterState ctx) :
    Veir.CTree.interpretCFGCore region values state regionIn =
      _root_.CTree.iter (fun (location, state) => Veir.CTree.interpretCFGCore.iter location state)
        (.inl (⟨first, firstIn⟩, values), state) := by
  unfold Veir.CTree.interpretCFGCore
  split <;> simp_all

theorem interpretCFGCore_eq_fail_of_no_firstBlock {ctx : WfIRContext OpCode}
    (region : RegionPtr) (regionIn : region.InBounds ctx.raw)
    (firstGet : region.getFirstBlock ctx.raw regionIn = none)
    (values : Array RuntimeValue) (state : InterpreterState ctx) :
    Veir.CTree.interpretCFGCore region values state regionIn = fail := by
  unfold Veir.CTree.interpretCFGCore
  split <;> simp_all

end Veir.Puddle.CTree
