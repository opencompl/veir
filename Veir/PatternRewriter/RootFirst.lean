module

public import Veir.Interpreter.Purity
public import Veir.PatternRewriter.Semantics

import all Veir.IR.Basic
import all Veir.Interpreter.EquationLemma
import all Veir.Rewriter.WfRewriter.Basic
import Veir.Rewriter.WfRewriter.GetSet

public section

namespace Veir
namespace RootFirst

/-!
# Root-first pure rewrite patterns

This module provides the first, deliberately small, root-first rewrite DSL.
The public API consists of typed handles and builder combinators.  The
matcher program used by the implementation is private so its representation
can later be replaced by a merged decision DAG without changing patterns.

Source operations are discovered from the candidate root through operands
and defining operations.  Target operations are then created in builder
order, so both sides naturally describe DAGs and target order is
topological.
-/

/-- A typed handle for a source or target operation. -/
structure OpHandle (opCode : OpCode) where
  private mk ::
  id : Nat
deriving Repr, DecidableEq

/-- A handle for an SSA value bound by the pattern. -/
structure ValueHandle where
  private mk ::
  id : Nat
deriving Repr, DecidableEq

/-- A handle for an MLIR type bound by the pattern. -/
structure TypeHandle where
  private mk ::
  id : Nat
deriving Repr, DecidableEq

/-- A typed view of an operation's dependent properties binding. -/
structure PropertiesHandle (opCode : OpCode) where
  op : OpHandle opCode
deriving Repr, DecidableEq

/-- Obtain the dependent-properties handle associated with an operation. -/
def OpHandle.properties (op : OpHandle opCode) : PropertiesHandle opCode :=
  ⟨op⟩

/--
A decidable type constraint.  Keeping the proposition together with its
Boolean implementation lets the matcher execute while `PurePattern.Semantics`
retains a small proposition.
-/
structure TypePattern where
  test : TypeAttr → Bool
  Holds : TypeAttr → Prop
  test_iff : ∀ type, test type = true ↔ Holds type

/-- Match any integer type. -/
def integerType : TypePattern where
  test
    | ⟨.integerType _, _⟩ => true
    | _ => false
  Holds type := ∃ integer, type.val = .integerType integer
  test_iff type := by
    rcases type with ⟨type, isType⟩
    cases type <;> simp

/-- Match one particular type. -/
def exactType (expected : TypeAttr) : TypePattern where
  test type := decide (type = expected)
  Holds type := type = expected
  test_iff type := by simp

namespace Experimental

/-!
The following declarations are the current unmerged matcher representation.
They are explicitly experimental; patterns should be authored with the
builder combinators below.
-/

structure SourceOpSpec where
  opCode : OpCode
  id : Nat

structure PropertyConstraint where
  opCode : OpCode
  opId : Nat
  test : propertiesOf opCode → Bool
  Holds : propertiesOf opCode → Prop
  test_iff : ∀ properties, test properties = true ↔ Holds properties

inductive MatchStep where
  | operand (opId index valueId : Nat)
  | result (opId index valueId : Nat)
  | resultType (opId index typeId : Nat)
  | valueType (valueId typeId : Nat)
  | definingOp (valueId opId : Nat) (opCode : OpCode)
  | typeConstraint (typeId : Nat) (pattern : TypePattern)
  | propertyConstraint (constraint : PropertyConstraint)
  | sameValue (lhs rhs : Nat)

structure TargetOpSpec where
  opCode : OpCode
  properties : propertiesOf opCode
  resultTypes : Array TypeHandle
  operands : Array ValueHandle
  resultIds : Array ValueHandle

structure Blueprint where
  root : Option SourceOpSpec := none
  sourceOps : Array SourceOpSpec := #[]
  steps : Array MatchStep := #[]
  targetOps : Array TargetOpSpec := #[]
  replacement : Option (Array ValueHandle) := none
  valueCount : Nat := 0
  typeCount : Nat := 0
  targetStarted : Bool := false

end Experimental

open Experimental

/--
The pattern builder.  Ill-formed patterns are rejected with a diagnostic when
`build` is called; matching itself remains an ordinary `Option`-valued local
rewrite.  Its state is part of the explicitly experimental representation.
-/
abbrev Builder (α : Type) := StateT Blueprint (Except String) α

private abbrev Builder.get : Builder Blueprint :=
  fun state => .ok (state, state)

private abbrev Builder.set (state : Blueprint) : Builder Unit :=
  fun _ => .ok ((), state)

private abbrev Builder.modify (f : Blueprint → Blueprint) : Builder Unit :=
  fun state => .ok ((), f state)

private abbrev Builder.throw {α : Type} (message : String) : Builder α :=
  fun _ => .error message

private abbrev ensureSourcePhase : Builder Unit := do
  if (← Builder.get).targetStarted then
    Builder.throw "source bindings must be declared before target operations"

/-- Bind the candidate root and require it to have `opCode`. -/
def matchRoot (opCode : OpCode) : Builder (OpHandle opCode) := do
  ensureSourcePhase
  let state ← Builder.get
  if state.root.isSome then
    Builder.throw "a root-first pattern has exactly one root"
  let spec : SourceOpSpec := { opCode, id := state.sourceOps.size }
  Builder.set { state with root := some spec, sourceOps := state.sourceOps.push spec }
  pure ⟨spec.id⟩

/-- Bind operand `index` of a matched source operation. -/
def OpHandle.operand (op : OpHandle opCode) (index : Nat) : Builder ValueHandle := do
  ensureSourcePhase
  let state ← Builder.get
  let value : ValueHandle := ⟨state.valueCount⟩
  Builder.set { state with
    steps := state.steps.push (.operand op.id index value.id)
    valueCount := state.valueCount + 1 }
  pure value

/-- Bind result `index` of a matched source operation. -/
def OpHandle.result (op : OpHandle opCode) (index : Nat) : Builder ValueHandle := do
  ensureSourcePhase
  let state ← Builder.get
  let value : ValueHandle := ⟨state.valueCount⟩
  Builder.set { state with
    steps := state.steps.push (.result op.id index value.id)
    valueCount := state.valueCount + 1 }
  pure value

/-- Bind result type `index` of a matched source operation. -/
def OpHandle.resultType (op : OpHandle opCode) (index : Nat) : Builder TypeHandle := do
  ensureSourcePhase
  let state ← Builder.get
  let type : TypeHandle := ⟨state.typeCount⟩
  Builder.set { state with
    steps := state.steps.push (.resultType op.id index type.id)
    typeCount := state.typeCount + 1 }
  pure type

/-- Apply a decidable constraint to a bound type. -/
def matchType (type : TypeHandle) (pattern : TypePattern) : Builder TypeHandle := do
  ensureSourcePhase
  Builder.modify fun state =>
    { state with steps := state.steps.push (.typeConstraint type.id pattern) }
  pure type

/-- Require a matched SSA value to have a bound type. -/
def checkType (value : ValueHandle) (type : TypeHandle) : Builder Unit := do
  ensureSourcePhase
  Builder.modify fun state =>
    { state with steps := state.steps.push (.valueType value.id type.id) }

/-- Discover and bind the defining operation of a matched value. -/
def matchDefiningOp (value : ValueHandle) (opCode : OpCode) :
    Builder (OpHandle opCode) := do
  ensureSourcePhase
  let state ← Builder.get
  let spec : SourceOpSpec := { opCode, id := state.sourceOps.size }
  Builder.set { state with
    sourceOps := state.sourceOps.push spec
    steps := state.steps.push (.definingOp value.id spec.id opCode) }
  pure ⟨spec.id⟩

/-- Require two handles to denote the same SSA value. -/
def checkSameValue (lhs rhs : ValueHandle) : Builder Unit := do
  ensureSourcePhase
  Builder.modify fun state =>
    { state with steps := state.steps.push (.sameValue lhs.id rhs.id) }

/-- Apply a reflected predicate to the dependent properties of an operation. -/
def checkPropertiesWhere (op : OpHandle opCode)
    (test : propertiesOf opCode → Bool)
    (Holds : propertiesOf opCode → Prop)
    (test_iff : ∀ properties, test properties = true ↔ Holds properties) :
    Builder Unit := do
  ensureSourcePhase
  let constraint : PropertyConstraint := {
    opCode, opId := op.id, test, Holds, test_iff
  }
  Builder.modify fun state =>
    { state with steps := state.steps.push (.propertyConstraint constraint) }

/-- Require the dependent properties of an operation to equal `expected`. -/
def checkProperties [DecidableEq (propertiesOf opCode)]
    (op : OpHandle opCode) (expected : propertiesOf opCode) : Builder Unit :=
  checkPropertiesWhere op
    (fun properties => decide (properties = expected))
    (fun properties => properties = expected)
    (by intro; simp)

/-- `checkProperties` through an explicit dependent-properties handle. -/
def PropertiesHandle.check [DecidableEq (propertiesOf opCode)]
    (properties : PropertiesHandle opCode) (expected : propertiesOf opCode) :
    Builder Unit :=
  checkProperties properties.op expected

private def handlesInBounds (state : Blueprint)
    (resultTypes : Array TypeHandle) (operands : Array ValueHandle) : Bool :=
  resultTypes.all (·.id < state.typeCount) &&
    operands.all (·.id < state.valueCount)

private def replaySourceAvailability :
    List MatchStep → Nat → Array Bool → Option (Nat × Array Bool)
  | [], opCount, available => some (opCount, available)
  | step :: rest, opCount, available =>
      match step with
      | .operand opId _ valueId =>
          if opId < opCount && valueId = available.size then
            replaySourceAvailability rest opCount (available.push true)
          else none
      | .result opId _ valueId =>
          if opId < opCount && opId != 0 &&
              valueId = available.size then
            replaySourceAvailability rest opCount (available.push true)
          else none
      | .definingOp valueId opId _ =>
          if valueId < available.size && opId = opCount then
            replaySourceAvailability rest (opCount + 1) available
          else none
      | .resultType opId _ _
      | .propertyConstraint { opId, .. } =>
          if opId < opCount then
            replaySourceAvailability rest opCount available
          else none
      | .valueType valueId _ =>
          if valueId < available.size then
            replaySourceAvailability rest opCount available
          else none
      | .typeConstraint _ _ =>
          replaySourceAvailability rest opCount available
      | .sameValue lhs rhs =>
          if lhs < available.size && rhs < available.size then
            replaySourceAvailability rest opCount available
          else none

private def handlesAvailable (available : Array Bool)
    (handles : Array ValueHandle) : Bool :=
  handles.all fun handle => available[handle.id]? == some true

private def resultIdsFollow (available : Array Bool)
    (resultIds : Array ValueHandle) : Bool :=
  decide (resultIds =
    (Array.range resultIds.size).map
      (fun index => ValueHandle.mk (available.size + index)))

private def replayTargetAvailability :
    List TargetOpSpec → Array Bool → Option (Array Bool)
  | [], available => some available
  | spec :: rest, available =>
      if isFoldEvaluationCandidate spec.opCode spec.properties &&
          handlesAvailable available spec.operands &&
          resultIdsFollow available spec.resultIds &&
          spec.resultIds.size = spec.resultTypes.size then
        replayTargetAvailability rest
          (available ++ Array.replicate spec.resultIds.size true)
      else none

/--
Checks the structural invariant needed by semantic soundness.  In particular,
root results are not available before the root executes, whereas root
operands, producer values, and target results are available to target
operations and as replacement values.

The check is repeated by `build`, so even a computation written directly
against the experimental builder representation cannot forge the invariant.
-/
private def blueprintSafe (blueprint : Blueprint) : Bool :=
  match blueprint.root with
  | none =>
      blueprint.sourceOps.isEmpty && blueprint.steps.isEmpty &&
        blueprint.targetOps.isEmpty && blueprint.replacement.isNone
  | some root =>
      root.id = 0 &&
      match replaySourceAvailability blueprint.steps.toList 1 #[] with
      | none => false
      | some (opCount, sourceAvailable) =>
          opCount = blueprint.sourceOps.size &&
          sourceAvailable.size ≤ blueprint.valueCount &&
          match replayTargetAvailability blueprint.targetOps.toList sourceAvailable with
          | none => false
          | some available =>
              available.size = blueprint.valueCount &&
              blueprint.replacement.any (handlesAvailable available)

/--
Create a pure, successorless, regionless target operation.  Its result handles
are allocated together and can be used by later target operations.
-/
def createOp (opCode : OpCode) (properties : propertiesOf opCode)
    (resultTypes : Array TypeHandle) (operands : Array ValueHandle) :
    Builder (OpHandle opCode × Array ValueHandle) := do
  let state ← Builder.get
  if !isFoldEvaluationCandidate opCode properties then
    Builder.throw "target operation is not a pure fold-evaluation candidate"
  if !handlesInBounds state resultTypes operands then
    Builder.throw "target operation refers to an unbound type or value"
  let results := Array.range resultTypes.size |>.map fun index =>
    ValueHandle.mk (state.valueCount + index)
  let op : OpHandle opCode := ⟨state.sourceOps.size + state.targetOps.size⟩
  let spec : TargetOpSpec := { opCode, properties, resultTypes, operands, resultIds := results }
  Builder.set { state with
    targetOps := state.targetOps.push spec
    valueCount := state.valueCount + results.size
    targetStarted := true }
  pure (op, results)

/-- Convenience wrapper for a target operation with exactly one result. -/
def createOp1 (opCode : OpCode) (properties : propertiesOf opCode)
    (resultType : TypeHandle) (operands : Array ValueHandle) :
    Builder (OpHandle opCode × ValueHandle) := do
  let (op, results) ← createOp opCode properties #[resultType] operands
  pure (op, results[0]?.getD ⟨0⟩)

/-- Select the values that replace the root results. -/
def replace (root : OpHandle opCode) (values : Array ValueHandle) : Builder Unit := do
  let state ← Builder.get
  let some rootSpec := state.root
    | Builder.throw "replace requires a matched root"
  if root.id != rootSpec.id then
    Builder.throw "replace must name the matched root"
  if values.any (fun value => state.valueCount ≤ value.id) then
    Builder.throw "replacement refers to an unbound value"
  if state.replacement.isSome then
    Builder.throw "a pattern has exactly one replacement"
  Builder.set { state with replacement := some values }

private structure MatchEnv where
  ops : Array OperationPtr
  values : Array ValuePtr
  types : Array TypeAttr

private def MatchEnv.InBounds (env : MatchEnv)
    (ctx : IRContext OpCode) : Prop :=
  (∀ op ∈ env.ops, op.InBounds ctx) ∧
  ∀ value ∈ env.values, value.InBounds ctx

private def pureShape (ctx : IRContext OpCode) (op : OperationPtr)
    (opCode : OpCode) : Bool :=
  op.getOpType! ctx = opCode &&
  op.getNumSuccessors! ctx = 0 &&
  op.getNumRegions! ctx = 0 &&
  isFoldEvaluationCandidate opCode (op.getProperties! ctx opCode)

private structure MatchResult (ctx : IRContext OpCode) where
  env : MatchEnv
  inBounds : env.InBounds ctx

private def matchEnvExtends (before after : MatchEnv) : Prop :=
  (∀ (index : Nat) (op : OperationPtr), before.ops[index]? = some op →
    after.ops[index]? = some op) ∧
  (∀ (index : Nat) (value : ValuePtr), before.values[index]? = some value →
    after.values[index]? = some value) ∧
  ∀ (index : Nat) (type : TypeAttr), before.types[index]? = some type →
    after.types[index]? = some type

private def runMatchStep (step : MatchStep) (ctx : IRContext OpCode)
    (env : MatchEnv) (henv : env.InBounds ctx) : Option (MatchResult ctx) := do
  match step with
  | .operand opId index valueId =>
      rlet hop : op ← env.ops[opId]?
      if hvalueId : valueId = env.values.size then
        if hindex : index < op.getNumOperands! ctx then
          let operand := op.getOperand! ctx index
          if hoperandIn : operand.InBounds ctx then
            let nextEnv := { env with values := env.values.push operand }
            pure {
              env := nextEnv
              inBounds := by
                constructor
                · simpa [nextEnv] using henv.1
                · intro value hvalue
                  simp only [nextEnv, Array.mem_push] at hvalue
                  rcases hvalue with hvalue | rfl
                  · exact henv.2 value hvalue
                  · exact hoperandIn
            }
          else none
        else none
      else none
  | .result opId index valueId =>
      rlet hop : op ← env.ops[opId]?
      if hopId : opId != 0 then
        if hvalueId : valueId = env.values.size then
          if hindex : index < op.getNumResults! ctx then
            let result : ValuePtr := op.getResult index
            if hresultIn : result.InBounds ctx then
              let nextEnv := { env with values := env.values.push result }
              pure {
                env := nextEnv
                inBounds := by
                  constructor
                  · simpa [nextEnv] using henv.1
                  · intro value hvalue
                    simp only [nextEnv, Array.mem_push] at hvalue
                    rcases hvalue with hvalue | rfl
                    · exact henv.2 value hvalue
                    · exact hresultIn
              }
            else none
          else none
        else none
      else none
  | .resultType opId index typeId =>
      let op ← env.ops[opId]?
      guard (typeId = env.types.size)
      let type ← (op.getResultTypes! ctx)[index]?
      pure {
        env := { env with types := env.types.push type }
        inBounds := by simpa [MatchEnv.InBounds] using henv
      }
  | .valueType valueId typeId =>
      let value ← env.values[valueId]?
      let type ← env.types[typeId]?
      guard (value.getType! ctx = type)
      pure ⟨env, henv⟩
  | .definingOp valueId opId opCode =>
      let value ← env.values[valueId]?
      let op ← value.getDefiningOp! ctx
      if hopIn : op.InBounds ctx then
        guard (opId = env.ops.size)
        guard (pureShape ctx op opCode)
        let nextEnv := { env with ops := env.ops.push op }
        pure {
          env := nextEnv
          inBounds := by
            constructor
            · intro operation hoperation
              simp only [nextEnv, Array.mem_push] at hoperation
              rcases hoperation with hoperation | rfl
              · exact henv.1 operation hoperation
              · exact hopIn
            · simpa [nextEnv] using henv.2
        }
      else none
  | .typeConstraint typeId pattern =>
      let type ← env.types[typeId]?
      guard (pattern.test type)
      pure ⟨env, henv⟩
  | .propertyConstraint constraint =>
      let op ← env.ops[constraint.opId]?
      guard (op.getOpType! ctx = constraint.opCode)
      guard (constraint.test (op.getProperties! ctx constraint.opCode))
      pure ⟨env, henv⟩
  | .sameValue lhs rhs =>
      let lhs ← env.values[lhs]?
      let rhs ← env.values[rhs]?
      guard (lhs = rhs)
      pure ⟨env, henv⟩

private theorem runMatchStep_extends
    (step : MatchStep) (ctx : IRContext OpCode)
    (env : MatchEnv) (henv : env.InBounds ctx)
    (result : MatchResult ctx)
    (hrun : runMatchStep step ctx env henv = some result) :
    matchEnvExtends env result.env := by
  cases step with
  | operand =>
      simp only [runMatchStep] at hrun
      repeat' split at hrun
      all_goals try contradiction
      all_goals cases hrun
      all_goals simp_all [matchEnvExtends, Array.getElem?_push]
      all_goals grind
  | result =>
      simp only [runMatchStep] at hrun
      repeat' split at hrun
      all_goals try contradiction
      all_goals cases hrun
      all_goals simp_all [matchEnvExtends, Array.getElem?_push]
      all_goals grind
  | resultType =>
      simp only [runMatchStep, bind, pure, guard] at hrun
      simp [Option.bind_eq_some_iff] at hrun
      rcases hrun with ⟨_, _, _, _, _, hresult⟩
      have henvEq := congrArg MatchResult.env hresult
      rw [← henvEq]
      simp [matchEnvExtends, Array.getElem?_push]
      grind
  | definingOp =>
      simp only [runMatchStep, bind, pure, guard] at hrun
      simp [Option.bind_eq_some_iff] at hrun
      rcases hrun with ⟨_, _, _, _, _, _, _, hresult⟩
      have henvEq := congrArg MatchResult.env hresult
      rw [← henvEq]
      simp [matchEnvExtends, Array.getElem?_push]
      grind
  | valueType =>
      simp only [runMatchStep, bind, pure, guard] at hrun
      simp [Option.bind_eq_some_iff] at hrun
      rcases hrun with ⟨_, _, _, _, _, hresult⟩
      have henvEq := congrArg MatchResult.env hresult
      rw [← henvEq]
      simp [matchEnvExtends]
  | typeConstraint =>
      simp only [runMatchStep, bind, pure, guard] at hrun
      simp [Option.bind_eq_some_iff] at hrun
      rcases hrun with ⟨_, _, _, hresult⟩
      have henvEq := congrArg MatchResult.env hresult
      rw [← henvEq]
      simp [matchEnvExtends]
  | propertyConstraint =>
      simp only [runMatchStep, bind, pure, guard] at hrun
      simp [Option.bind_eq_some_iff] at hrun
      rcases hrun with ⟨_, _, _, _, hresult⟩
      have henvEq := congrArg MatchResult.env hresult
      rw [← henvEq]
      simp [matchEnvExtends]
  | sameValue =>
      simp only [runMatchStep, bind, pure, guard] at hrun
      simp [Option.bind_eq_some_iff] at hrun
      rcases hrun with ⟨_, _, _, _, _, hresult⟩
      have henvEq := congrArg MatchResult.env hresult
      rw [← henvEq]
      simp [matchEnvExtends]

private def runMatchSteps (steps : List MatchStep) (ctx : IRContext OpCode)
    (env : MatchEnv) (henv : env.InBounds ctx) : Option (MatchResult ctx) :=
  match steps with
  | [] => some ⟨env, henv⟩
  | step :: rest => do
      let result ← runMatchStep step ctx env henv
      runMatchSteps rest ctx result.env result.inBounds

private theorem matchEnvExtends_trans
    {first middle last : MatchEnv}
    (h₁ : matchEnvExtends first middle)
    (h₂ : matchEnvExtends middle last) :
    matchEnvExtends first last := by
  simp only [matchEnvExtends] at h₁ h₂ ⊢
  grind

private theorem matchEnvExtends_values_mem
    {before after : MatchEnv}
    (hextends : matchEnvExtends before after)
    {value : ValuePtr} (hvalue : value ∈ before.values) :
    value ∈ after.values := by
  obtain ⟨index, hindex, heq⟩ := Array.getElem_of_mem hvalue
  have hget : before.values[index]? = some value := by
    rw [Array.getElem?_eq_getElem hindex, heq]
  have := hextends.2.1 index value hget
  grind [Array.getElem?_eq_some_iff]

private theorem runMatchSteps_extends
    (steps : List MatchStep) (ctx : IRContext OpCode)
    (env : MatchEnv) (henv : env.InBounds ctx)
    (result : MatchResult ctx)
    (hrun : runMatchSteps steps ctx env henv = some result) :
    matchEnvExtends env result.env := by
  induction steps generalizing env with
  | nil =>
      simp [runMatchSteps] at hrun
      subst result
      simp [matchEnvExtends]
  | cons step rest ih =>
      simp only [runMatchSteps, bind, Option.bind_eq_some_iff] at hrun
      rcases hrun with ⟨stepResult, hstep, hrest⟩
      exact matchEnvExtends_trans
        (runMatchStep_extends step ctx env henv stepResult hstep)
        (ih stepResult.env stepResult.inBounds hrest)

private def matchSource (blueprint : Blueprint) (ctx : WfIRContext OpCode)
    (root : OperationPtr) : Option (MatchResult ctx.raw) := do
  let rootSpec ← blueprint.root
  if hroot : root.InBounds ctx.raw then
    guard (rootSpec.id = 0)
    guard (pureShape ctx.raw root rootSpec.opCode)
    let env : MatchEnv := { ops := #[root], values := #[], types := #[] }
    runMatchSteps blueprint.steps.toList ctx.raw env (by
      simp [MatchEnv.InBounds, env, hroot])
  else
    none

private def resolveTypes (types : Array TypeAttr)
    (handles : Array TypeHandle) : Option (Array TypeAttr) :=
  handles.mapM fun handle => types[handle.id]?

private def resolveValues (values : Array ValuePtr)
    (handles : Array ValueHandle) : Option (Array ValuePtr) :=
  handles.mapM fun handle => values[handle.id]?

private theorem createdOpsTrans
    {ctx₁ ctx₂ ctx₃ : WfIRContext OpCode}
    (h₁₂ : WfIRContext.WithCreatedOps ctx₁ ctx₂)
    (h₂₃ : WfIRContext.WithCreatedOps ctx₂ ctx₃) :
    WfIRContext.WithCreatedOps ctx₁ ctx₃ := by
  induction h₂₃ with
  | Nil => exact h₁₂
  | CreatedOp ctx₂ ctx₃ ctx₄ _ hcreate ih =>
      exact .CreatedOp ctx₁ ctx₃ ctx₄ (ih h₁₂) hcreate

private theorem WfIRContext.WithCreatedOps.getOpType_eq
    {ctx₁ ctx₂ : WfIRContext OpCode}
    (h : WfIRContext.WithCreatedOps ctx₁ ctx₂)
    (op : OperationPtr) (opIn : op.InBounds ctx₁.raw) :
    op.getOpType! ctx₂.raw = op.getOpType! ctx₁.raw := by
  induction h with
  | Nil => rfl
  | @CreatedOp freshOp ctx₁ middle ctx₂ hcreated hcreate ih =>
      rcases hcreate with
        ⟨opType, resultTypes, operands, successors, regions, properties,
          hoper, hsucc, hregions, hins, hcreate⟩
      have opInMiddle : op.InBounds middle.raw :=
        hcreated.inBounds_mono (.operation op) opIn
      have hopNe : op ≠ freshOp := by
        intro hop
        subst freshOp
        grind
      rw [OperationPtr.getOpType!_WfRewriter_createOp hcreate, if_neg hopNe,
        ih opIn]

private theorem getProperties_createOp_of_ne
    {ctx newCtx : WfIRContext OpCode}
    {createdCode queryCode : OpCode}
    {resultTypes : Array TypeAttr} {operands : Array ValuePtr}
    {successors : Array BlockPtr} {regions : Array RegionPtr}
    {properties : propertiesOf createdCode}
    {freshOp op : OperationPtr}
    {hoper hsucc hregions hins}
    (hcreate :
      WfRewriter.createOp ctx createdCode resultTypes operands successors
        regions properties none hoper hsucc hregions hins =
        some (newCtx, freshOp))
    (hne : op ≠ freshOp) :
    op.getProperties! newCtx.raw queryCode =
      op.getProperties! ctx.raw queryCode := by
  simp only [WfRewriter.createOp] at hcreate
  grind (gen := 20)

private theorem WfIRContext.WithCreatedOps.getProperties_eq
    {ctx₁ ctx₂ : WfIRContext OpCode}
    (h : WfIRContext.WithCreatedOps ctx₁ ctx₂)
    (op : OperationPtr) (opIn : op.InBounds ctx₁.raw)
    (opCode : OpCode) :
    op.getProperties! ctx₂.raw opCode =
      op.getProperties! ctx₁.raw opCode := by
  induction h with
  | Nil => rfl
  | @CreatedOp freshOp ctx₁ middle ctx₂ hcreated hcreate ih =>
      rcases hcreate with
        ⟨createdCode, resultTypes, operands, successors, regions, properties,
          hoper, hsucc, hregions, hins, hcreate⟩
      have opInMiddle : op.InBounds middle.raw :=
        hcreated.inBounds_mono (.operation op) opIn
      have hopNe : op ≠ freshOp := by
        intro hop
        subst freshOp
        grind
      rw [getProperties_createOp_of_ne hcreate hopNe, ih opIn]

private theorem WfIRContext.WithCreatedOps.getResultTypes_eq
    {ctx₁ ctx₂ : WfIRContext OpCode}
    (h : WfIRContext.WithCreatedOps ctx₁ ctx₂)
    (op : OperationPtr) (opIn : op.InBounds ctx₁.raw) :
    op.getResultTypes! ctx₂.raw = op.getResultTypes! ctx₁.raw := by
  induction h with
  | Nil => rfl
  | @CreatedOp freshOp ctx₁ middle ctx₂ hcreated hcreate ih =>
      rcases hcreate with
        ⟨createdCode, resultTypes, operands, successors, regions, properties,
          hoper, hsucc, hregions, hins, hcreate⟩
      have opInMiddle : op.InBounds middle.raw :=
        hcreated.inBounds_mono (.operation op) opIn
      have hopNe : op ≠ freshOp := by
        intro hop
        subst freshOp
        grind
      rw [OperationPtr.getResultTypes!_WfRewriter_createOp hcreate,
        if_neg hopNe, ih opIn]

private theorem WfIRContext.WithCreatedOps.getOperands_eq
    {ctx₁ ctx₂ : WfIRContext OpCode}
    (h : WfIRContext.WithCreatedOps ctx₁ ctx₂)
    (op : OperationPtr) (opIn : op.InBounds ctx₁.raw) :
    op.getOperands! ctx₂.raw = op.getOperands! ctx₁.raw := by
  induction h with
  | Nil => rfl
  | @CreatedOp freshOp ctx₁ middle ctx₂ hcreated hcreate ih =>
      rcases hcreate with
        ⟨createdCode, resultTypes, operands, successors, regions, properties,
          hoper, hsucc, hregions, hins, hcreate⟩
      have opInMiddle : op.InBounds middle.raw :=
        hcreated.inBounds_mono (.operation op) opIn
      have hopNe : op ≠ freshOp := by
        intro hop
        subst freshOp
        grind
      rw [OperationPtr.getOperands!_WfRewriter_createOp hcreate,
        if_neg hopNe, ih opIn]

private theorem WfIRContext.WithCreatedOps.getSuccessors_eq
    {ctx₁ ctx₂ : WfIRContext OpCode}
    (h : WfIRContext.WithCreatedOps ctx₁ ctx₂)
    (op : OperationPtr) (opIn : op.InBounds ctx₁.raw) :
    op.getSuccessors! ctx₂.raw = op.getSuccessors! ctx₁.raw := by
  induction h with
  | Nil => rfl
  | @CreatedOp freshOp ctx₁ middle ctx₂ hcreated hcreate ih =>
      rcases hcreate with
        ⟨createdCode, resultTypes, operands, successors, regions, properties,
          hoper, hsucc, hregions, hins, hcreate⟩
      have opInMiddle : op.InBounds middle.raw :=
        hcreated.inBounds_mono (.operation op) opIn
      have hopNe : op ≠ freshOp := by
        intro hop
        subst freshOp
        grind
      rw [OperationPtr.getSuccessors!_WfRewriter_createOp hcreate,
        if_neg hopNe, ih opIn]

private structure TargetStepResult (spec : TargetOpSpec)
    (initialCtx : WfIRContext OpCode) (initialEnv : MatchEnv) where
  ctx : WfIRContext OpCode
  env : MatchEnv
  op : OperationPtr
  resultTypes : Array TypeAttr
  operands : Array ValuePtr
  resolvedResultTypes :
    resolveTypes initialEnv.types spec.resultTypes = some resultTypes
  resolvedOperands :
    resolveValues initialEnv.values spec.operands = some operands
  operandsInBounds :
    ∀ operand, operand ∈ operands → operand.InBounds initialCtx.raw
  createEq :
    WfRewriter.createOp initialCtx spec.opCode resultTypes operands #[] #[]
      spec.properties none operandsInBounds (by simp) (by simp)
      (by simp [Option.maybe_def]) = some (ctx, op)
  results : Array ValuePtr
  resultsEq :
    results = (Array.range spec.resultIds.size).map
      (fun index => ValuePtr.opResult (OperationPtr.getResult op index))
  envEq : env = {
    ops := initialEnv.ops.push op
    values := initialEnv.values ++ results
    types := initialEnv.types
  }
  created : WfIRContext.WithCreatedOps initialCtx ctx
  operationInBounds :
    ∀ operation, operation.InBounds ctx.raw ↔
      operation.InBounds initialCtx.raw ∨ operation = op
  opNotInBounds : ¬op.InBounds initialCtx.raw
  envInBounds : env.InBounds ctx.raw

private def runTargetOpSpec (spec : TargetOpSpec)
    (ctx : WfIRContext OpCode) (env : MatchEnv)
    (henv : env.InBounds ctx.raw) :
    Option (TargetStepResult spec ctx env) := do
  match hresultTypes : resolveTypes env.types spec.resultTypes with
  | none => none
  | some resultTypes =>
      match hoperands : resolveValues env.values spec.operands with
      | none => none
      | some operands =>
          if hoper : ∀ operand, operand ∈ operands → operand.InBounds ctx.raw then
            match hcreate :
              WfRewriter.createOp ctx spec.opCode resultTypes operands #[] #[]
                spec.properties none hoper (by simp) (by simp)
                (by simp [Option.maybe_def]) with
            | none => none
            | some (newCtx, op) =>
              if hsize : op.getNumResults! newCtx.raw = spec.resultIds.size then
                let newResults : Array ValuePtr :=
                  (Array.range spec.resultIds.size).map
                    (fun index => ValuePtr.opResult (OperationPtr.getResult op index))
                let newValues := env.values ++ newResults
                let newEnv : MatchEnv := {
                  ops := env.ops.push op
                  values := newValues
                  types := env.types
                }
                have hcreated : WfIRContext.WithCreatedOps ctx newCtx :=
                  .CreatedOp ctx ctx newCtx (.Nil ctx)
                    ⟨spec.opCode, resultTypes, operands, #[], #[], spec.properties,
                      hoper, by simp, by simp, by simp [Option.maybe_def], hcreate⟩
                have hnewEnv : newEnv.InBounds newCtx.raw := by
                  constructor
                  · intro operation hoperation
                    simp only [newEnv, Array.mem_push] at hoperation
                    rcases hoperation with hoperation | rfl
                    · exact (WfRewriter.createOp_operation_inBounds_iff
                        (operation := operation) hcreate).mpr
                        (.inl (henv.1 operation hoperation))
                    · exact (WfRewriter.createOp_operation_inBounds_iff
                        (operation := operation) hcreate).mpr (.inr rfl)
                  · intro value hvalue
                    simp only [newEnv, newValues] at hvalue
                    rw [Array.mem_append] at hvalue
                    rcases hvalue with hvalue | hvalue
                    · exact hcreated.inBounds_mono (.value value) (by
                        simpa using henv.2 value hvalue)
                    · obtain ⟨index, hindex, heq⟩ := Array.mem_map.mp hvalue
                      rw [← heq]
                      have : index < spec.resultIds.size := by
                        simpa using hindex
                      grind
                pure {
                  ctx := newCtx
                  env := newEnv
                  op
                  resultTypes
                  operands
                  resolvedResultTypes := hresultTypes
                  resolvedOperands := hoperands
                  operandsInBounds := hoper
                  createEq := hcreate
                  results := newResults
                  resultsEq := rfl
                  envEq := rfl
                  created := hcreated
                  operationInBounds := fun operation => by
                    simpa using WfRewriter.createOp_operation_inBounds_iff
                      (operation := operation) hcreate
                  opNotInBounds := by
                    grind
                  envInBounds := hnewEnv
                }
              else
                none
          else
            none

private structure TargetRunResult (initialCtx : WfIRContext OpCode) where
  ctx : WfIRContext OpCode
  env : MatchEnv
  newOps : Array OperationPtr
  created : WfIRContext.WithCreatedOps initialCtx ctx
  returnOps :
    ∀ operation, operation ∈ newOps ↔
      operation.InBounds ctx.raw ∧ ¬operation.InBounds initialCtx.raw
  envInBounds : env.InBounds ctx.raw

private def runTargetList (specs : List TargetOpSpec)
    (ctx : WfIRContext OpCode) (env : MatchEnv)
    (henv : env.InBounds ctx.raw) : Option (TargetRunResult ctx) := do
  match specs with
  | [] =>
      pure {
        ctx
        env
        newOps := #[]
        created := .Nil ctx
        returnOps := by simp
        envInBounds := henv
      }
  | spec :: rest =>
      let step ← runTargetOpSpec spec ctx env henv
      let tail ← runTargetList rest step.ctx step.env step.envInBounds
      pure {
        ctx := tail.ctx
        env := tail.env
        newOps := #[step.op] ++ tail.newOps
        created := createdOpsTrans step.created tail.created
        returnOps := by
          intro operation
          rw [Array.mem_append, tail.returnOps, step.operationInBounds]
          simp only [Array.mem_singleton]
          constructor
          · rintro (rfl | ⟨hfinal, hnot⟩)
            · constructor
              · exact tail.created.inBounds_mono (.operation step.op)
                  (step.operationInBounds step.op |>.mpr (.inr rfl))
              · exact step.opNotInBounds
            · exact ⟨hfinal, fun hold => hnot (.inl hold)⟩
          · rintro ⟨hfinal, hold⟩
            by_cases hstep : operation = step.op
            · exact .inl hstep
            · exact .inr ⟨hfinal, by
                rintro (hold' | hstep')
                · exact hold hold'
                · exact hstep hstep'⟩
        envInBounds := tail.envInBounds
      }

private def runTarget (blueprint : Blueprint) (ctx : WfIRContext OpCode)
    (env : MatchEnv) (henv : env.InBounds ctx.raw) : Option (TargetRunResult ctx) :=
  runTargetList blueprint.targetOps.toList ctx env henv

/--
An operation assignment used by the generated value-level semantic
proposition.  The dependent properties stay paired with their opcode.
-/
structure SemanticOp where
  opCode : OpCode
  properties : propertiesOf opCode
  resultTypes : Array TypeAttr
  operands : Array RuntimeValue
  results : Array RuntimeValue

def SemanticOp.Valid (op : SemanticOp) : Prop :=
  foldEvaluate op.opCode op.properties op.resultTypes op.operands =
    some (.ok op.results)

/-- Universal source values, types, properties, and successful evaluations. -/
structure SourceAssignment where
  ops : Array SemanticOp
  values : Array RuntimeValue
  types : Array TypeAttr

private def semanticOpOf (ctx : IRContext OpCode)
    (runtimeValue : ValuePtr → RuntimeValue) (op : OperationPtr) : SemanticOp := {
  opCode := op.getOpType! ctx
  properties := op.getProperties! ctx (op.getOpType! ctx)
  resultTypes := op.getResultTypes! ctx
  operands := (op.getOperands! ctx).map runtimeValue
  results := (op.getResults! ctx).map runtimeValue
}

private def semanticAssignmentOf (ctx : IRContext OpCode)
    (env : MatchEnv) (runtimeValue : ValuePtr → RuntimeValue) :
    SourceAssignment := {
  ops := env.ops.map (semanticOpOf ctx runtimeValue)
  values := env.values.map runtimeValue
  types := env.types
}

private theorem semanticAssignmentOf_op_get
    {ctx : IRContext OpCode} {env : MatchEnv}
    {runtimeValue : ValuePtr → RuntimeValue}
    {index : Nat} {op : OperationPtr}
    (h : env.ops[index]? = some op) :
    (semanticAssignmentOf ctx env runtimeValue).ops[index]? =
      some (semanticOpOf ctx runtimeValue op) := by
  simp [semanticAssignmentOf, h]

private theorem semanticAssignmentOf_value_get
    {ctx : IRContext OpCode} {env : MatchEnv}
    {runtimeValue : ValuePtr → RuntimeValue}
    {index : Nat} {value : ValuePtr}
    (h : env.values[index]? = some value) :
    (semanticAssignmentOf ctx env runtimeValue).values[index]? =
      some (runtimeValue value) := by
  simp [semanticAssignmentOf, h]

private def SemanticOp.propertiesAs (op : SemanticOp) (opCode : OpCode) :
    Option (propertiesOf opCode) :=
  if h : op.opCode = opCode then
    some (h ▸ op.properties)
  else
    none

private theorem getProperties_transport (op : OperationPtr)
    (ctx : IRContext OpCode) {lhs rhs : OpCode} (h : lhs = rhs) :
    h ▸ op.getProperties! ctx lhs = op.getProperties! ctx rhs := by
  cases h
  rfl

private def matchStepSemantics (step : MatchStep)
    (assignment : SourceAssignment) : Prop :=
  match step with
  | .operand opId index valueId =>
      ∃ op value,
        assignment.ops[opId]? = some op ∧
        assignment.values[valueId]? = some value ∧
        op.operands[index]? = some value
  | .result opId index valueId =>
      ∃ op value,
        assignment.ops[opId]? = some op ∧
        assignment.values[valueId]? = some value ∧
        op.results[index]? = some value
  | .resultType opId index typeId =>
      ∃ op type,
        assignment.ops[opId]? = some op ∧
        assignment.types[typeId]? = some type ∧
        op.resultTypes[index]? = some type
  | .valueType valueId typeId =>
      ∃ value type,
        assignment.values[valueId]? = some value ∧
        assignment.types[typeId]? = some type ∧
        value.Conforms type
  | .definingOp valueId opId opCode =>
      ∃ value op,
        assignment.values[valueId]? = some value ∧
        assignment.ops[opId]? = some op ∧
        op.opCode = opCode ∧
        value ∈ op.results
  | .typeConstraint typeId pattern =>
      ∃ type, assignment.types[typeId]? = some type ∧ pattern.Holds type
  | .propertyConstraint constraint =>
      ∃ op properties,
        assignment.ops[constraint.opId]? = some op ∧
        op.propertiesAs constraint.opCode = some properties ∧
        constraint.Holds properties
  | .sameValue lhs rhs =>
      ∃ value,
        assignment.values[lhs]? = some value ∧
        assignment.values[rhs]? = some value

private theorem matchStepSemantics_mono
    (step : MatchStep) (ctx : IRContext OpCode)
    (before after : MatchEnv) (runtimeValue : ValuePtr → RuntimeValue)
    (hextends : matchEnvExtends before after)
    (hsem :
      matchStepSemantics step
        (semanticAssignmentOf ctx before runtimeValue)) :
    matchStepSemantics step
      (semanticAssignmentOf ctx after runtimeValue) := by
  rcases hextends with ⟨hops, hvalues, htypes⟩
  cases step with
  | operand opId index valueId =>
      rcases hsem with ⟨op, value, hop, hvalue, hoperand⟩
      simp only [semanticAssignmentOf] at hop hvalue
      rw [Array.getElem?_map] at hop hvalue
      rcases Option.map_eq_some_iff.mp hop with
        ⟨sourceOp, hsourceOp, rfl⟩
      rcases Option.map_eq_some_iff.mp hvalue with
        ⟨sourceValue, hsourceValue, rfl⟩
      exact ⟨semanticOpOf ctx runtimeValue sourceOp, runtimeValue sourceValue,
        semanticAssignmentOf_op_get (hops _ _ hsourceOp),
        semanticAssignmentOf_value_get (hvalues _ _ hsourceValue),
        hoperand⟩
  | result opId index valueId =>
      rcases hsem with ⟨op, value, hop, hvalue, hresult⟩
      simp only [semanticAssignmentOf] at hop hvalue
      rw [Array.getElem?_map] at hop hvalue
      rcases Option.map_eq_some_iff.mp hop with
        ⟨sourceOp, hsourceOp, rfl⟩
      rcases Option.map_eq_some_iff.mp hvalue with
        ⟨sourceValue, hsourceValue, rfl⟩
      exact ⟨semanticOpOf ctx runtimeValue sourceOp, runtimeValue sourceValue,
        semanticAssignmentOf_op_get (hops _ _ hsourceOp),
        semanticAssignmentOf_value_get (hvalues _ _ hsourceValue),
        hresult⟩
  | resultType opId index typeId =>
      rcases hsem with ⟨op, type, hop, htype, hresultType⟩
      simp only [semanticAssignmentOf] at hop
      rw [Array.getElem?_map] at hop
      rcases Option.map_eq_some_iff.mp hop with
        ⟨sourceOp, hsourceOp, rfl⟩
      exact ⟨semanticOpOf ctx runtimeValue sourceOp, type,
        semanticAssignmentOf_op_get (hops _ _ hsourceOp),
        htypes _ _ htype, hresultType⟩
  | valueType valueId typeId =>
      rcases hsem with ⟨value, type, hvalue, htype, hconforms⟩
      simp only [semanticAssignmentOf] at hvalue
      rw [Array.getElem?_map] at hvalue
      rcases Option.map_eq_some_iff.mp hvalue with
        ⟨sourceValue, hsourceValue, rfl⟩
      exact ⟨runtimeValue sourceValue, type,
        semanticAssignmentOf_value_get (hvalues _ _ hsourceValue),
        htypes _ _ htype, hconforms⟩
  | definingOp valueId opId opCode =>
      rcases hsem with
        ⟨value, op, hvalue, hop, hopCode, hmember⟩
      simp only [semanticAssignmentOf] at hvalue hop
      rw [Array.getElem?_map] at hvalue hop
      rcases Option.map_eq_some_iff.mp hvalue with
        ⟨sourceValue, hsourceValue, rfl⟩
      rcases Option.map_eq_some_iff.mp hop with
        ⟨sourceOp, hsourceOp, rfl⟩
      exact ⟨runtimeValue sourceValue, semanticOpOf ctx runtimeValue sourceOp,
        semanticAssignmentOf_value_get (hvalues _ _ hsourceValue),
        semanticAssignmentOf_op_get (hops _ _ hsourceOp),
        hopCode, hmember⟩
  | typeConstraint typeId pattern =>
      rcases hsem with ⟨type, htype, hholds⟩
      exact ⟨type, htypes _ _ htype, hholds⟩
  | propertyConstraint constraint =>
      rcases hsem with ⟨op, properties, hop, hproperties, hholds⟩
      simp only [semanticAssignmentOf] at hop
      rw [Array.getElem?_map] at hop
      rcases Option.map_eq_some_iff.mp hop with
        ⟨sourceOp, hsourceOp, rfl⟩
      exact ⟨semanticOpOf ctx runtimeValue sourceOp, properties,
        semanticAssignmentOf_op_get (hops _ _ hsourceOp),
        hproperties, hholds⟩
  | sameValue lhs rhs =>
      rcases hsem with ⟨value, hlhs, hrhs⟩
      simp only [semanticAssignmentOf] at hlhs hrhs
      rw [Array.getElem?_map] at hlhs hrhs
      rcases Option.map_eq_some_iff.mp hlhs with
        ⟨lhsValue, hlhsValue, rfl⟩
      rcases Option.map_eq_some_iff.mp hrhs with
        ⟨rhsValue, hrhsValue, heq⟩
      exact ⟨runtimeValue lhsValue,
        semanticAssignmentOf_value_get (hvalues _ _ hlhsValue),
        by
          rw [← heq]
          exact semanticAssignmentOf_value_get
            (hvalues _ _ hrhsValue)⟩

private theorem runMatchStep_semantics
    (step : MatchStep) (ctx : IRContext OpCode)
    (ctxWf : ctx.WellFormed)
    (env : MatchEnv) (henv : env.InBounds ctx)
    (result : MatchResult ctx)
    (hrun : runMatchStep step ctx env henv = some result)
    (runtimeValue : ValuePtr → RuntimeValue)
    (hconforms : ∀ value ∈ result.env.values,
      (runtimeValue value).Conforms (value.getType! ctx)) :
    matchStepSemantics step
      (semanticAssignmentOf ctx result.env runtimeValue) := by
  cases step with
  | operand =>
      simp only [runMatchStep] at hrun
      repeat' split at hrun
      all_goals try contradiction
      all_goals cases hrun
      all_goals simp_all [matchStepSemantics, semanticAssignmentOf,
        semanticOpOf, Array.getElem_push]
  | result =>
      simp only [runMatchStep] at hrun
      repeat' split at hrun
      all_goals try contradiction
      all_goals cases hrun
      all_goals simp_all [matchStepSemantics, semanticAssignmentOf,
        semanticOpOf, Array.getElem_push]
  | resultType =>
      simp only [runMatchStep, bind, pure, guard] at hrun
      simp only [Option.bind_eq_some_iff] at hrun
      simp at hrun
      rcases hrun with ⟨op, hop, htypeId, type, htype, hresult⟩
      have henvEq := congrArg MatchResult.env hresult
      rw [← henvEq]
      simp_all [matchStepSemantics, semanticAssignmentOf, semanticOpOf]
  | valueType =>
      simp only [runMatchStep, bind, pure, guard] at hrun
      simp only [Option.bind_eq_some_iff] at hrun
      simp at hrun
      rcases hrun with ⟨value, hvalue, type, htype, hvalueType, hresult⟩
      have henvEq := congrArg MatchResult.env hresult
      rw [← henvEq] at hconforms ⊢
      refine ⟨runtimeValue value, type, ?_, ?_, ?_⟩
      · simp [semanticAssignmentOf, hvalue]
      · simpa [semanticAssignmentOf] using htype
      · exact hvalueType ▸ hconforms value (by grind)
  | definingOp =>
      simp only [runMatchStep, bind, pure, guard] at hrun
      simp only [Option.bind_eq_some_iff] at hrun
      simp [Option.bind_eq_some_iff] at hrun
      rcases hrun with
        ⟨value, hvalue, op, hop, hopId, hshape, _, hresult⟩
      have henvEq := congrArg MatchResult.env hresult
      rw [← henvEq]
      simp [pureShape] at hshape
      simp only [matchStepSemantics]
      refine ⟨runtimeValue value, semanticOpOf ctx runtimeValue op, ?_, ?_,
        hshape.1.1.1, ?_⟩
      · simp [semanticAssignmentOf, hvalue]
      · simp [semanticAssignmentOf, Array.getElem_push, hopId]
      · apply Array.mem_map.mpr
        refine ⟨value, ?_, rfl⟩
        rw [OperationPtr.getResults!.mem_iff_exists_index]
        rcases ValuePtr.getDefiningOp!_eq_some_iff.mp hop with
          ⟨opResult, rfl, howner⟩
        have hresultIn : opResult.InBounds ctx :=
          (ValuePtr.inBounds_opResult opResult ctx).mp
            (henv.2 (.opResult opResult) (by grind))
        have hownerSelf :
            (opResult.get! ctx).owner = opResult.op :=
          (ctxWf.operations opResult.op (by grind)).result_owner
            opResult.index
            (OpResultPtr.inBounds_OperationPtr_getNumResults!
              opResult ctx hresultIn)
        have hopEq : opResult.op = op := hownerSelf.symm.trans howner
        refine ⟨opResult.index, ?_, ?_⟩
        · rw [← hopEq]
          exact OpResultPtr.inBounds_OperationPtr_getNumResults!
            opResult ctx hresultIn
        · cases opResult
          simpa [OperationPtr.getResult] using hopEq.symm
  | typeConstraint typeId pattern =>
      simp only [runMatchStep, bind, pure, guard] at hrun
      simp only [Option.bind_eq_some_iff] at hrun
      simp at hrun
      rcases hrun with ⟨type, htype, hholds, hresult⟩
      have henvEq := congrArg MatchResult.env hresult
      rw [← henvEq]
      exact ⟨type, by simpa [semanticAssignmentOf] using htype,
        (pattern.test_iff type).mp hholds⟩
  | propertyConstraint constraint =>
      simp only [runMatchStep, bind, pure, guard] at hrun
      simp only [Option.bind_eq_some_iff] at hrun
      simp at hrun
      rcases hrun with ⟨op, hop, hopCode, hholds, hresult⟩
      have henvEq := congrArg MatchResult.env hresult
      rw [← henvEq]
      simp only [matchStepSemantics]
      refine ⟨semanticOpOf ctx runtimeValue op,
        op.getProperties! ctx constraint.opCode, ?_, ?_, ?_⟩
      · simp [semanticAssignmentOf, hop]
      · simp [SemanticOp.propertiesAs, semanticOpOf, hopCode,
          getProperties_transport]
      · exact (constraint.test_iff _).mp hholds
  | sameValue =>
      simp only [runMatchStep, bind, pure, guard] at hrun
      simp only [Option.bind_eq_some_iff] at hrun
      simp at hrun
      rcases hrun with ⟨lhs, hlhs, rhs, hrhs, heq, hresult⟩
      have henvEq := congrArg MatchResult.env hresult
      rw [← henvEq]
      subst rhs
      simp_all [matchStepSemantics, semanticAssignmentOf]

private theorem runMatchSteps_semantics
    (steps : List MatchStep) (ctx : IRContext OpCode)
    (ctxWf : ctx.WellFormed)
    (env : MatchEnv) (henv : env.InBounds ctx)
    (result : MatchResult ctx)
    (hrun : runMatchSteps steps ctx env henv = some result)
    (runtimeValue : ValuePtr → RuntimeValue)
    (hconforms : ∀ value ∈ result.env.values,
      (runtimeValue value).Conforms (value.getType! ctx)) :
    ∀ step ∈ steps,
      matchStepSemantics step
        (semanticAssignmentOf ctx result.env runtimeValue) := by
  induction steps generalizing env with
  | nil => simp
  | cons step rest ih =>
      simp only [runMatchSteps, bind, Option.bind_eq_some_iff] at hrun
      rcases hrun with ⟨stepResult, hstep, hrest⟩
      have htailExtends :=
        runMatchSteps_extends rest ctx stepResult.env
          stepResult.inBounds result hrest
      intro current hcurrent
      simp only [List.mem_cons] at hcurrent
      rcases hcurrent with rfl | hcurrent
      · apply matchStepSemantics_mono current ctx stepResult.env result.env
          runtimeValue htailExtends
        apply runMatchStep_semantics current ctx ctxWf env henv
          stepResult hstep runtimeValue
        intro value hvalue
        exact hconforms value
          (matchEnvExtends_values_mem htailExtends hvalue)
      · exact ih stepResult.env stepResult.inBounds hrest current hcurrent

private structure MatchFacts (env : MatchEnv)
    (ctx : WfIRContext OpCode) (root : OperationPtr) : Prop where
  rootAtZero : env.ops[0]? = some root
  opDominates :
    ∀ (index : Nat) (op : OperationPtr), env.ops[index]? = some op →
      (index = 0 ∧ op = root) ∨
        (0 < index ∧ op.strictlyDominates root ctx)
  valueDominates :
    ∀ value ∈ env.values, value.dominatesIp (.before root) ctx
  valueOrigin :
    ∀ value ∈ env.values,
      (∃ (index : Nat) (op : OperationPtr),
        env.ops[index]? = some op ∧
        value ∈ op.getOperands! ctx.raw) ∨
      (∃ (index : Nat) (op : OperationPtr),
        env.ops[index]? = some op ∧
        index ≠ 0 ∧
        value ∈ op.getResults! ctx.raw)
  pure :
    ∀ op ∈ env.ops,
      pureShape ctx.raw op (op.getOpType! ctx.raw)

private theorem runMatchStep_facts
    (ctx : WfIRContext OpCode) (ctxDom : ctx.Dom)
    (root : OperationPtr) (step : MatchStep)
    (env : MatchEnv) (henv : env.InBounds ctx.raw)
    (facts : MatchFacts env ctx root)
    (result : MatchResult ctx.raw)
    (hrun : runMatchStep step ctx.raw env henv = some result) :
    MatchFacts result.env ctx root := by
  cases step with
  | operand opId index valueId =>
      simp only [runMatchStep] at hrun
      repeat' split at hrun
      all_goals try contradiction
      all_goals cases hrun
      rename_i matchedOp hlookup hvalueId hindex hin
      constructor
      · simpa using facts.rootAtZero
      · simpa using facts.opDominates
      · intro value hvalue
        simp only [Array.mem_push] at hvalue
        rcases hvalue with hvalue | rfl
        · exact facts.valueDominates value hvalue
        · have hopIn : matchedOp.InBounds ctx.raw :=
            henv.1 matchedOp (by grind [Array.getElem?_eq_some_iff])
          have hoperand :
              matchedOp.getOperand! ctx.raw index ∈
                matchedOp.getOperands! ctx.raw := by
            exact OperationPtr.getOperands!.mem_getOperand hindex
          have hdom := ctxDom.operand_dominates_op hopIn hoperand
          rcases facts.opDominates opId matchedOp hlookup with
            ⟨_, rfl⟩ | ⟨_, hopDom⟩
          · exact hdom
          · exact ValuePtr.dominatesIp_before_of_strictlyDominates
              hdom hopDom
      · intro value hvalue
        simp only [Array.mem_push] at hvalue
        rcases hvalue with hvalue | rfl
        · exact facts.valueOrigin value hvalue
        · left
          exact ⟨opId, matchedOp, hlookup, by
            exact OperationPtr.getOperands!.mem_getOperand hindex⟩
      · simpa using facts.pure
  | result opId index valueId =>
      simp only [runMatchStep] at hrun
      repeat' split at hrun
      all_goals try contradiction
      all_goals cases hrun
      rename_i matchedOp hlookup hopId hvalueId hindex hin
      constructor
      · simpa using facts.rootAtZero
      · simpa using facts.opDominates
      · intro value hvalue
        simp only [Array.mem_push] at hvalue
        rcases hvalue with hvalue | rfl
        · exact facts.valueDominates value hvalue
        · have hmember :
              (matchedOp.getResult index : ValuePtr) ∈
                matchedOp.getResults! ctx.raw := by
            rw [OperationPtr.getResults!.mem_iff_exists_index]
            exact ⟨index, hindex, rfl⟩
          rcases facts.opDominates opId matchedOp hlookup with
            ⟨hopIdZero, _⟩ | ⟨_, hopDom⟩
          · exact False.elim (by grind)
          · exact
              ValuePtr.result_dominatesIp_before_of_strictlyDominates
                hmember hopDom
      · intro value hvalue
        simp only [Array.mem_push] at hvalue
        rcases hvalue with hvalue | rfl
        · exact facts.valueOrigin value hvalue
        · right
          exact ⟨opId, matchedOp, hlookup, by grind, by
            rw [OperationPtr.getResults!.mem_iff_exists_index]
            exact ⟨index, hindex, rfl⟩⟩
      · simpa using facts.pure
  | resultType opId index typeId =>
      simp only [runMatchStep, bind, pure, guard] at hrun
      simp [Option.bind_eq_some_iff] at hrun
      rcases hrun with ⟨_, _, _, _, _, hresult⟩
      have henvEq := congrArg MatchResult.env hresult
      rw [← henvEq]
      exact {
        rootAtZero := facts.rootAtZero
        opDominates := facts.opDominates
        valueDominates := facts.valueDominates
        valueOrigin := facts.valueOrigin
        pure := facts.pure
      }
  | valueType valueId typeId =>
      simp only [runMatchStep, bind, pure, guard] at hrun
      simp [Option.bind_eq_some_iff] at hrun
      rcases hrun with ⟨_, _, _, _, _, hresult⟩
      have henvEq := congrArg MatchResult.env hresult
      rw [← henvEq]
      exact facts
  | definingOp valueId opId opCode =>
      simp only [runMatchStep, bind, pure, guard] at hrun
      simp [Option.bind_eq_some_iff] at hrun
      rcases hrun with
        ⟨value, hvalue, op, hop, hopId, hshape, _, hresult⟩
      have henvEq := congrArg MatchResult.env hresult
      rw [← henvEq]
      have hvalueMem : value ∈ env.values := by
        grind [Array.getElem?_eq_some_iff]
      have hopDom : op.strictlyDominates root ctx :=
        OperationPtr.strictlyDominates_of_getDefiningOp!_of_value_dominatesIp
          hop (facts.valueDominates value hvalueMem)
      have hsize : 0 < env.ops.size := by
        grind [Array.getElem?_eq_some_iff, facts.rootAtZero]
      have liftLookup :
          ∀ {index : Nat} {current : OperationPtr},
            env.ops[index]? = some current →
            (env.ops.push op)[index]? = some current := by
        intro index current hcurrent
        have hlt : index < env.ops.size := by
          grind [Array.getElem?_eq_some_iff]
        simp [Array.getElem?_push, Nat.ne_of_lt hlt, hcurrent]
      constructor
      · exact liftLookup facts.rootAtZero
      · intro currentId currentOp hcurrent
        by_cases hlt : currentId < env.ops.size
        · have hold : env.ops[currentId]? = some currentOp := by
            simpa [Array.getElem?_push, Nat.ne_of_lt hlt] using hcurrent
          exact facts.opDominates currentId currentOp hold
        · have hnew : currentId = env.ops.size := by
            grind [Array.getElem?_eq_some_iff]
          subst currentId
          have hopEq : op = currentOp := by
            simpa [Array.getElem?_push] using hcurrent
          subst currentOp
          right
          exact ⟨hsize, hopDom⟩
      · simpa using facts.valueDominates
      · intro current hcurrent
        rcases facts.valueOrigin current hcurrent with
          ⟨index, origin, horigin, hoperand⟩ |
          ⟨index, origin, horigin, hindex, hresult⟩
        · exact .inl
            ⟨index, origin, liftLookup horigin, hoperand⟩
        · exact .inr
            ⟨index, origin, liftLookup horigin, hindex, hresult⟩
      · intro current hcurrent
        simp only [Array.mem_push] at hcurrent
        rcases hcurrent with hcurrent | rfl
        · exact facts.pure current hcurrent
        · simp [pureShape] at hshape
          have hopCode := hshape.1.1.1
          subst opCode
          simpa [pureShape] using hshape
  | typeConstraint typeId pattern =>
      simp only [runMatchStep, bind, pure, guard] at hrun
      simp [Option.bind_eq_some_iff] at hrun
      rcases hrun with ⟨_, _, _, hresult⟩
      have henvEq := congrArg MatchResult.env hresult
      rw [← henvEq]
      exact facts
  | propertyConstraint constraint =>
      simp only [runMatchStep, bind, pure, guard] at hrun
      simp [Option.bind_eq_some_iff] at hrun
      rcases hrun with ⟨_, _, _, _, hresult⟩
      have henvEq := congrArg MatchResult.env hresult
      rw [← henvEq]
      exact facts
  | sameValue lhs rhs =>
      simp only [runMatchStep, bind, pure, guard] at hrun
      simp [Option.bind_eq_some_iff] at hrun
      rcases hrun with ⟨_, _, _, _, _, hresult⟩
      have henvEq := congrArg MatchResult.env hresult
      rw [← henvEq]
      exact facts

private theorem runMatchSteps_facts
    (ctx : WfIRContext OpCode) (ctxDom : ctx.Dom)
    (root : OperationPtr) (steps : List MatchStep)
    (env : MatchEnv) (henv : env.InBounds ctx.raw)
    (facts : MatchFacts env ctx root)
    (result : MatchResult ctx.raw)
    (hrun : runMatchSteps steps ctx.raw env henv = some result) :
    MatchFacts result.env ctx root := by
  induction steps generalizing env with
  | nil =>
      simp [runMatchSteps] at hrun
      subst result
      exact facts
  | cons step rest ih =>
      simp only [runMatchSteps, bind, Option.bind_eq_some_iff] at hrun
      rcases hrun with ⟨stepResult, hstep, hrest⟩
      exact ih stepResult.env stepResult.inBounds
        (runMatchStep_facts ctx ctxDom root step env henv facts
          stepResult hstep)
        hrest

private theorem pureShape_self_of_pureShape
    (ctx : IRContext OpCode) (op : OperationPtr) (opCode : OpCode)
    (hshape : pureShape ctx op opCode) :
    pureShape ctx op (op.getOpType! ctx) := by
  simp [pureShape] at hshape
  have hopCode := hshape.1.1.1
  subst opCode
  simpa [pureShape] using hshape

private structure SourceMatchFacts (blueprint : Blueprint)
    (ctx : WfIRContext OpCode) (root : OperationPtr)
    (result : MatchResult ctx.raw) : Prop where
  rootInfo :
    ∃ rootSpec,
      blueprint.root = some rootSpec ∧
      rootSpec.id = 0 ∧
      pureShape ctx.raw root rootSpec.opCode
  rootInBounds : root.InBounds ctx.raw
  matchFacts : MatchFacts result.env ctx root

private theorem matchSource_facts
    (blueprint : Blueprint) (ctx : WfIRContext OpCode)
    (ctxDom : ctx.Dom) (root : OperationPtr)
    (result : MatchResult ctx.raw)
    (hmatch : matchSource blueprint ctx root = some result) :
    SourceMatchFacts blueprint ctx root result := by
  simp only [matchSource, bind, pure, guard] at hmatch
  simp [Option.bind_eq_some_iff] at hmatch
  rcases hmatch with
    ⟨rootSpec, hrootSpec, hrootId, hrootShape, hrootIn, hsteps⟩
  let initialEnv : MatchEnv := {
    ops := #[root]
    values := #[]
    types := #[]
  }
  have hinitial : initialEnv.InBounds ctx.raw := by
    simp [initialEnv, MatchEnv.InBounds, hrootIn]
  have hinitialFacts : MatchFacts initialEnv ctx root := by
    constructor
    · simp [initialEnv]
    · intro index op hop
      simp [initialEnv] at hop
      exact .inl (by grind)
    · simp [initialEnv]
    · simp [initialEnv]
    · intro op hop
      simp [initialEnv] at hop
      subst op
      exact pureShape_self_of_pureShape ctx.raw root
        rootSpec.opCode hrootShape
  exact {
    rootInfo := ⟨rootSpec, hrootSpec, hrootId, hrootShape⟩
    rootInBounds := hrootIn
    matchFacts :=
      runMatchSteps_facts ctx ctxDom root blueprint.steps.toList
        initialEnv hinitial hinitialFacts result hsteps
  }

private theorem definingOp_eq_of_mem_results
    (ctx : WfIRContext OpCode) (op : OperationPtr)
    (opIn : op.InBounds ctx.raw) (value : ValuePtr)
    (hvalue : value ∈ op.getResults! ctx.raw) :
    value.getDefiningOp! ctx.raw = some op := by
  rw [OperationPtr.getResults!.mem_iff_exists_index] at hvalue
  rcases hvalue with ⟨index, hindex, rfl⟩
  simp only [ValuePtr.getDefiningOp!_opResult]
  rw [(ctx.wellFormed.operations op opIn).result_owner index hindex]

private theorem MatchFacts.value_not_mem_root_results
    {env : MatchEnv} {ctx : WfIRContext OpCode}
    {root : OperationPtr}
    (facts : MatchFacts env ctx root)
    (envIn : env.InBounds ctx.raw)
    (ctxDom : ctx.Dom)
    (rootIn : root.InBounds ctx.raw)
    {value : ValuePtr} (hvalue : value ∈ env.values) :
    value ∉ root.getResults! ctx.raw := by
  rcases facts.valueOrigin value hvalue with
    ⟨index, op, hop, hoperand⟩ |
    ⟨index, op, hop, hindex, hresult⟩
  · have opIn : op.InBounds ctx.raw :=
      envIn.1 op (by grind [Array.getElem?_eq_some_iff])
    have hopDom : op.dominates root ctx := by
      rcases facts.opDominates index op hop with
        ⟨_, rfl⟩ | ⟨_, hstrict⟩
      · exact OperationPtr.dominates_refl
      · exact OperationPtr.dominates_of_strictlyDominates hstrict
    exact
      IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates
        ctxDom hopDom value hoperand
  · intro hrootResult
    have opIn : op.InBounds ctx.raw :=
      envIn.1 op (by grind [Array.getElem?_eq_some_iff])
    have hopDef :=
      definingOp_eq_of_mem_results ctx op opIn value hresult
    have hrootDef :=
      definingOp_eq_of_mem_results ctx root rootIn value hrootResult
    have hopEq : op = root := by grind
    subst op
    rcases facts.opDominates index root hop with
      ⟨hzero, _⟩ | ⟨_, hstrict⟩
    · exact hindex hzero
    · exact (OperationPtr.strictlyDominates_def.mp hstrict).2 rfl

private theorem InterpreterState.EquationHolds.exists_getVar_of_mem_operands
    {ctx : WfIRContext OpCode} {state : InterpreterState ctx}
    {op : OperationPtr} {opIn : op.InBounds ctx.raw}
    (hequation : state.EquationHolds op opIn)
    {value : ValuePtr} (hvalue : value ∈ op.getOperands! ctx.raw) :
    ∃ runtimeValue, state.variables.getVar? value = some runtimeValue := by
  simp only [InterpreterState.EquationHolds] at hequation
  rcases hequation with ⟨controlFlow, hinterpret⟩
  rcases interpretOp_some_iff.mp hinterpret with
    ⟨operandValues, resultValues, memory, variables, hoperands,
      hoperation, hresults, hstate⟩
  rw [OperationPtr.getOperands!.mem_iff_exists_index] at hvalue
  rcases hvalue with ⟨index, hindex, hvalue⟩
  subst value
  exact ⟨operandValues[index]!,
    (VariableState.getOperandValues_eq_some_iff.mp hoperands).2
      index hindex⟩

private theorem InterpreterState.EquationHolds.exists_getVar_of_mem_results
    {ctx : WfIRContext OpCode} {state : InterpreterState ctx}
    {op : OperationPtr} {opIn : op.InBounds ctx.raw}
    (hequation : state.EquationHolds op opIn)
    {value : ValuePtr} (hvalue : value ∈ op.getResults! ctx.raw) :
    ∃ runtimeValue, state.variables.getVar? value = some runtimeValue := by
  simp only [InterpreterState.EquationHolds] at hequation
  rcases hequation with ⟨controlFlow, hinterpret⟩
  rcases interpretOp_some_iff.mp hinterpret with
    ⟨operandValues, resultValues, memory, variables, hoperands,
      hoperation, hresults, hstate⟩
  subst state
  rw [OperationPtr.getResults!.mem_iff_exists_index] at hvalue
  rcases hvalue with ⟨index, hindex, hvalue⟩
  subst value
  exact ⟨resultValues[index]!,
    VariableState.getVar?_getResult_of_setResultValues?
      hindex hresults⟩

private theorem MatchFacts.producerEquation
    {env : MatchEnv} {ctx : WfIRContext OpCode}
    {root : OperationPtr}
    (facts : MatchFacts env ctx root)
    (envIn : env.InBounds ctx.raw)
    (rootIn : root.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (equationLemma : state.EquationLemmaAt (.before root) (by grind))
    {index : Nat} {op : OperationPtr}
    (hop : env.ops[index]? = some op)
    (hindex : index ≠ 0) :
    state.EquationHolds op
      (envIn.1 op (by grind [Array.getElem?_eq_some_iff])) := by
  have opIn : op.InBounds ctx.raw :=
    envIn.1 op (by grind [Array.getElem?_eq_some_iff])
  have hstrict : op.strictlyDominates root ctx := by
    rcases facts.opDominates index op hop with
      ⟨hzero, _⟩ | ⟨_, hstrict⟩
    · exact False.elim (hindex hzero)
    · exact hstrict
  have hshape := facts.pure op
    (by grind [Array.getElem?_eq_some_iff])
  simp [pureShape] at hshape
  have hpure : op.Pure ctx.raw :=
    OperationPtr.pure_of_foldEvaluationCandidate op ctx.raw hshape.2
  exact equationLemma op opIn hpure
    (OperationPtr.dominatesIp_before.mpr hstrict)

private theorem MatchFacts.value_exists_in_state
    {env : MatchEnv} {ctx : WfIRContext OpCode}
    {root : OperationPtr}
    (facts : MatchFacts env ctx root)
    (envIn : env.InBounds ctx.raw)
    (rootIn : root.InBounds ctx.raw)
    {state newState : InterpreterState ctx}
    (equationLemma : state.EquationLemmaAt (.before root) (by grind))
    (rootRun :
      interpretOp root state rootIn = some (.ok (newState, controlFlow)))
    {value : ValuePtr} (hvalue : value ∈ env.values) :
    ∃ runtimeValue, state.variables.getVar? value = some runtimeValue := by
  rcases facts.valueOrigin value hvalue with
    ⟨index, op, hop, hoperand⟩ |
    ⟨index, op, hop, hindex, hresult⟩
  · rcases facts.opDominates index op hop with
      ⟨_, rfl⟩ | ⟨hpositive, hstrict⟩
    · rcases interpretOp_some_iff.mp rootRun with
        ⟨operandValues, resultValues, memory, variables, hoperands,
          hoperation, hresults, hstate⟩
      rw [OperationPtr.getOperands!.mem_iff_exists_index] at hoperand
      rcases hoperand with ⟨operandIndex, hoperandIndex, rfl⟩
      exact ⟨operandValues[operandIndex]!,
        (VariableState.getOperandValues_eq_some_iff.mp hoperands).2
          operandIndex hoperandIndex⟩
    · exact
        InterpreterState.EquationHolds.exists_getVar_of_mem_operands
          (facts.producerEquation envIn rootIn equationLemma hop
            (by omega))
          hoperand
  · exact
      InterpreterState.EquationHolds.exists_getVar_of_mem_results
        (facts.producerEquation envIn rootIn equationLemma hop hindex)
        hresult

private theorem foldEvaluate_eq_ok_of_pureShape
    (ctx : IRContext OpCode) (op : OperationPtr)
    (hshape : pureShape ctx op (op.getOpType! ctx))
    {operands results : Array RuntimeValue}
    {memory memory' : MemoryState}
    {action : Option ControlFlowAction}
    (hinterpret :
      op.interpret ctx operands memory =
        some (.ok (results, memory', action))) :
    action = none ∧
    memory' = memory ∧
    foldEvaluate (op.getOpType! ctx)
      (op.getProperties! ctx (op.getOpType! ctx))
      (op.getResultTypes! ctx) operands =
        some (.ok results) := by
  simp [pureShape] at hshape
  have hsuccessors : op.getSuccessors! ctx = #[] := by
    have hsize : (op.getSuccessors! ctx).size = 0 := by
      simpa using hshape.1.1
    exact Array.eq_empty_of_size_eq_zero hsize
  have hpure : op.Pure ctx :=
    OperationPtr.pure_of_foldEvaluationCandidate op ctx hshape.2
  have hmemory : memory = memory' :=
    OperationPtr.Pure.interpretOp'_eq_ok_implies_memory_eq hpure hinterpret
  have hwithoutSuccessors :
      interpretOp' (op.getOpType! ctx)
        (op.getProperties! ctx (op.getOpType! ctx))
        (op.getResultTypes! ctx) operands #[] memory =
          some (.ok (results, memory', action)) := by
    change
      interpretOp' (op.getOpType! ctx)
        (op.getProperties! ctx (op.getOpType! ctx))
        (op.getResultTypes! ctx) operands (op.getSuccessors! ctx) memory =
          some (.ok (results, memory', action)) at hinterpret
    simpa [hsuccessors] using hinterpret
  have haction :=
    foldEvaluationCandidate_control_flow_free
      (op.getOpType! ctx)
      (op.getProperties! ctx (op.getOpType! ctx))
      hshape.2
      (op.getResultTypes! ctx) operands memory results memory' action
      hwithoutSuccessors
  subst action
  subst memory'
  refine ⟨rfl, rfl, ?_⟩
  exact
    (foldEvaluate_eq_ok_iff
      (op.getOpType! ctx)
      (op.getProperties! ctx (op.getOpType! ctx))
      (op.getResultTypes! ctx) operands results memory hshape.2).mpr
      hwithoutSuccessors

private noncomputable def executionRuntimeValue
    {ctx : WfIRContext OpCode}
    (state newState : InterpreterState ctx)
    (root : OperationPtr) (value : ValuePtr) : RuntimeValue :=
  if value ∈ root.getResults! ctx.raw then
    (newState.variables.getVar? value).getD default
  else
    (state.variables.getVar? value).getD default

private theorem executionRuntimeValue_of_not_mem_root_results
    {ctx : WfIRContext OpCode}
    {state newState : InterpreterState ctx}
    {root : OperationPtr} {value : ValuePtr}
    (hnot : value ∉ root.getResults! ctx.raw)
    {runtimeValue : RuntimeValue}
    (hvalue : state.variables.getVar? value = some runtimeValue) :
    executionRuntimeValue state newState root value = runtimeValue := by
  simp [executionRuntimeValue, hnot, hvalue]

private theorem executionRuntimeValue_of_mem_root_results
    {ctx : WfIRContext OpCode}
    {state newState : InterpreterState ctx}
    {root : OperationPtr} {value : ValuePtr}
    (hmem : value ∈ root.getResults! ctx.raw)
    {runtimeValue : RuntimeValue}
    (hvalue : newState.variables.getVar? value = some runtimeValue) :
    executionRuntimeValue state newState root value = runtimeValue := by
  simp [executionRuntimeValue, hmem, hvalue]

private theorem map_executionRuntimeValue_of_mapM_not_root
    {ctx : WfIRContext OpCode}
    {state newState : InterpreterState ctx}
    {root : OperationPtr} {values : Array ValuePtr}
    {runtimeValues : Array RuntimeValue}
    (hnot :
      ∀ value ∈ values, value ∉ root.getResults! ctx.raw)
    (hvalues :
      values.mapM state.variables.getVar? = some runtimeValues) :
    values.map (executionRuntimeValue state newState root) =
      runtimeValues := by
  apply Array.ext
  · grind
  · intro index hleft hright
    have hvalueIndex : index < values.size := by
      simpa using hleft
    have hlookup :=
      Array.mapM_option_eq_some_implies hvalues index hright
    have hmember : values[index] ∈ values :=
      Array.getElem_mem hvalueIndex
    rw [Array.getElem_map]
    exact executionRuntimeValue_of_not_mem_root_results
      (hnot values[index] hmember) hlookup

private theorem map_executionRuntimeValue_of_mapM_root
    {ctx : WfIRContext OpCode}
    {state newState : InterpreterState ctx}
    {root : OperationPtr} {values : Array ValuePtr}
    {runtimeValues : Array RuntimeValue}
    (hmem :
      ∀ value ∈ values, value ∈ root.getResults! ctx.raw)
    (hvalues :
      values.mapM newState.variables.getVar? = some runtimeValues) :
    values.map (executionRuntimeValue state newState root) =
      runtimeValues := by
  apply Array.ext
  · grind
  · intro index hleft hright
    have hvalueIndex : index < values.size := by
      simpa using hleft
    have hlookup :=
      Array.mapM_option_eq_some_implies hvalues index hright
    have hmember : values[index] ∈ values :=
      Array.getElem_mem hvalueIndex
    rw [Array.getElem_map]
    exact executionRuntimeValue_of_mem_root_results
      (hmem values[index] hmember) hlookup

private theorem MatchFacts.op_operands_not_mem_root_results
    {env : MatchEnv} {ctx : WfIRContext OpCode}
    {root : OperationPtr}
    (facts : MatchFacts env ctx root)
    (envIn : env.InBounds ctx.raw)
    (ctxDom : ctx.Dom)
    {index : Nat} {op : OperationPtr}
    (hop : env.ops[index]? = some op) :
    ∀ value ∈ op.getOperands! ctx.raw,
      value ∉ root.getResults! ctx.raw := by
  intro value hoperand
  have opIn : op.InBounds ctx.raw :=
    envIn.1 op (by grind [Array.getElem?_eq_some_iff])
  have hopDom : op.dominates root ctx := by
    rcases facts.opDominates index op hop with
      ⟨_, rfl⟩ | ⟨_, hstrict⟩
    · exact OperationPtr.dominates_refl
    · exact OperationPtr.dominates_of_strictlyDominates hstrict
  exact
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates
      ctxDom hopDom value hoperand

private theorem MatchFacts.producer_results_not_mem_root_results
    {env : MatchEnv} {ctx : WfIRContext OpCode}
    {root : OperationPtr}
    (facts : MatchFacts env ctx root)
    (envIn : env.InBounds ctx.raw)
    (rootIn : root.InBounds ctx.raw)
    {index : Nat} {op : OperationPtr}
    (hop : env.ops[index]? = some op)
    (hindex : index ≠ 0) :
    ∀ value ∈ op.getResults! ctx.raw,
      value ∉ root.getResults! ctx.raw := by
  intro value hopResult hrootResult
  have opIn : op.InBounds ctx.raw :=
    envIn.1 op (by grind [Array.getElem?_eq_some_iff])
  have hopDef :=
    definingOp_eq_of_mem_results ctx op opIn value hopResult
  have hrootDef :=
    definingOp_eq_of_mem_results ctx root rootIn value hrootResult
  have hopEq : op = root := by grind
  subst op
  rcases facts.opDominates index root hop with
    ⟨hzero, _⟩ | ⟨_, hstrict⟩
  · exact hindex hzero
  · exact (OperationPtr.strictlyDominates_def.mp hstrict).2 rfl

private theorem VariableState.mapM_getResults_eq_some_of_setResultValues
    {ctx : WfIRContext OpCode}
    {state state' : VariableState ctx}
    {op : OperationPtr} {opIn : op.InBounds ctx.raw}
    {resultValues : Array RuntimeValue}
    (hset :
      state.setResultValues? op resultValues opIn = some state') :
    (op.getResults! ctx.raw).mapM state'.getVar? =
      some resultValues := by
  have hsize :
      (op.getResults! ctx.raw).size = resultValues.size := by
    grind
  rw [Array.mapM_eq_some_iff_of_size_eq hsize]
  intro index hindex
  have hi : index < op.getNumResults! ctx.raw := by
    simpa using hindex
  simpa [OperationPtr.getResults!.getElem!_eq_getResult hi] using
    VariableState.getVar?_getResult_of_setResultValues? hi hset

private theorem matchSource_stepSemantics
    (blueprint : Blueprint) (ctx : WfIRContext OpCode)
    (root : OperationPtr) (result : MatchResult ctx.raw)
    (hmatch : matchSource blueprint ctx root = some result)
    (runtimeValue : ValuePtr → RuntimeValue)
    (hconforms : ∀ value ∈ result.env.values,
      (runtimeValue value).Conforms (value.getType! ctx.raw)) :
    ∀ step ∈ blueprint.steps,
      matchStepSemantics step
        (semanticAssignmentOf ctx.raw result.env runtimeValue) := by
  simp only [matchSource, bind, pure, guard] at hmatch
  simp [Option.bind_eq_some_iff] at hmatch
  rcases hmatch with
    ⟨rootSpec, hrootSpec, hrootId, hrootShape, hrootIn, hsteps⟩
  intro step hstep
  exact runMatchSteps_semantics blueprint.steps.toList ctx.raw
    ctx.wellFormed
    { ops := #[root], values := #[], types := #[] }
    (by simp [MatchEnv.InBounds, hrootIn])
    result hsteps runtimeValue hconforms step (by simpa using hstep)

private def blueprintSourceSemantics (blueprint : Blueprint)
    (assignment : SourceAssignment) : Prop :=
  (∃ rootSpec root,
    blueprint.root = some rootSpec ∧
    assignment.ops[rootSpec.id]? = some root ∧
    root.opCode = rootSpec.opCode) ∧
  (∀ op ∈ assignment.ops, op.Valid) ∧
  ∀ step ∈ blueprint.steps, matchStepSemantics step assignment

private def resolveRuntimeValues (values : Array RuntimeValue)
    (handles : Array ValueHandle) : Option (Array RuntimeValue) :=
  handles.mapM fun handle => values[handle.id]?

private inductive TargetSemantics (types : Array TypeAttr) :
    List TargetOpSpec → Array RuntimeValue → Array RuntimeValue → Prop
  | nil (values) : TargetSemantics types [] values values
  | cons (spec rest values finalValues)
      (resultTypes : Array TypeAttr)
      (operands results : Array RuntimeValue)
      (hresultTypes : resolveTypes types spec.resultTypes = some resultTypes)
      (hoperands : resolveRuntimeValues values spec.operands = some operands)
      (heval :
        foldEvaluate spec.opCode spec.properties resultTypes operands =
          some (.ok results))
      (hconforms : RuntimeValue.ArrayConforms results resultTypes)
      (hsize : results.size = spec.resultIds.size)
      (hrest : TargetSemantics types rest (values ++ results) finalValues) :
      TargetSemantics types (spec :: rest) values finalValues

private def ValuesRefineState {ctx : WfIRContext OpCode}
    (pointers : Array ValuePtr) (semanticValues : Array RuntimeValue)
    (state : InterpreterState ctx) : Prop :=
  ∃ runtimeValues,
    pointers.mapM state.variables.getVar? = some runtimeValues ∧
    semanticValues ⊒ runtimeValues

private theorem resolveValues_refines
    {ctx : WfIRContext OpCode}
    {pointers resolvedPointers : Array ValuePtr}
    {semanticValues actualValues semanticResolved : Array RuntimeValue}
    {handles : Array ValueHandle}
    {state : InterpreterState ctx}
    (hpointers :
      resolveValues pointers handles = some resolvedPointers)
    (hsemantic :
      resolveRuntimeValues semanticValues handles =
        some semanticResolved)
    (hstate :
      pointers.mapM state.variables.getVar? = some actualValues)
    (hrefine : semanticValues ⊒ actualValues) :
    ∃ actualResolved,
      resolvedPointers.mapM state.variables.getVar? =
        some actualResolved ∧
      semanticResolved ⊒ actualResolved := by
  simp only [resolveValues] at hpointers
  simp only [resolveRuntimeValues] at hsemantic
  have hpointersSize : pointers.size = actualValues.size := by
    exact Array.size_eq_of_mapM_eq_some hstate
  have hpointersResolvedSize : handles.size = resolvedPointers.size :=
    Array.size_eq_of_mapM_eq_some hpointers
  have hsemanticResolvedSize : handles.size = semanticResolved.size :=
    Array.size_eq_of_mapM_eq_some hsemantic
  have hsemanticSize : semanticValues.size = actualValues.size :=
    hrefine.1
  have hexists :
      ∃ actualResolved,
        resolveRuntimeValues actualValues handles =
          some actualResolved := by
    simp only [resolveRuntimeValues]
    rw [Array.exists_mapM_option_eq_some_iff]
    intro index hindex
    have hpointer :=
      Array.mapM_option_eq_some_implies hpointers index
        (by omega)
    have hhandleBound : handles[index].id < pointers.size := by
      grind [Array.getElem?_eq_some_iff]
    refine ⟨actualValues[handles[index].id], ?_⟩
    exact Array.getElem?_eq_getElem ..
  rcases hexists with ⟨actualResolved, hactualResolved⟩
  simp only [resolveRuntimeValues] at hactualResolved
  have hactualResolvedSize : handles.size = actualResolved.size :=
    Array.size_eq_of_mapM_eq_some hactualResolved
  refine ⟨actualResolved, ?_, ?_⟩
  · have hsize :
        resolvedPointers.size = actualResolved.size := by
      omega
    rw [Array.mapM_eq_some_iff_of_size_eq hsize]
    intro index hindex
    have hhandleIndex : index < handles.size := by omega
    have hpointer :=
      Array.mapM_option_eq_some_implies hpointers index (by omega)
    have hactual :=
      Array.mapM_option_eq_some_implies hactualResolved index (by omega)
    have hpointerBound : handles[index].id < pointers.size := by
      grind [Array.getElem?_eq_some_iff]
    have hlookup :=
      Array.mapM_option_eq_some_implies hstate
        handles[index].id (by omega)
    grind [Array.getElem?_eq_some_iff]
  · simp only [RuntimeValue.arrayIsRefinedBy]
    constructor
    · omega
    · intro index hindex
      have hhandleIndex : index < handles.size := by omega
      have hsemanticValue :=
        Array.mapM_option_eq_some_implies hsemantic index (by omega)
      have hactualValue :=
        Array.mapM_option_eq_some_implies hactualResolved index (by omega)
      have hhandleBound : handles[index].id < pointers.size := by
        have hpointer :=
          Array.mapM_option_eq_some_implies hpointers index (by omega)
        grind [Array.getElem?_eq_some_iff]
      have hvalueRefinement :=
        hrefine.2 handles[index].id (by omega)
      grind [Array.getElem?_eq_some_iff]

/--
Operational reconstruction for a successfully built target DAG.

This is the remaining interpreter-level bridge: `runTargetList` creates a
detached sequence of operations, while `TargetSemantics` evaluates the same
sequence at the value level.  The bridge replays those operations in the
extended interpreter state and relates the resulting environment pointwise.
-/
private axiom runTargetList_semantics
    (specs : List TargetOpSpec)
    (ctx : WfIRContext OpCode) (env : MatchEnv)
    (envIn : env.InBounds ctx.raw)
    (target : TargetRunResult ctx)
    (hrun : runTargetList specs ctx env envIn = some target)
    {semanticValues finalSemanticValues : Array RuntimeValue}
    (hsemantic :
      TargetSemantics env.types specs semanticValues finalSemanticValues)
    (state : InterpreterState target.ctx)
    (hrefinement : ValuesRefineState env.values semanticValues state) :
    ∃ finalState actualValues,
      interpretOpList target.newOps.toList state
          (by grind [target.returnOps]) =
        some (.ok (finalState, none)) ∧
      finalState.memory = state.memory ∧
      target.env.values.mapM finalState.variables.getVar? =
        some actualValues ∧
      finalSemanticValues ⊒ actualValues

/--
A compiled pure root-first pattern.

The `Experimental.Blueprint` field is intentionally not a stable API.  Use
`build`, the builder combinators, `run`, and the structural theorems below.
-/
structure PurePattern where
  private mk ::
  blueprint : Blueprint
  private safe : blueprintSafe blueprint = true

private def sourceSemantics (pattern : PurePattern) :=
  blueprintSourceSemantics pattern.blueprint

private theorem sourceSemantics_of_execution
    (pattern : PurePattern)
    (ctx : WfIRContext OpCode) (ctxDom : ctx.Dom)
    (root : OperationPtr) (rootIn : root.InBounds ctx.raw)
    (source : MatchResult ctx.raw)
    (hmatch : matchSource pattern.blueprint ctx root = some source)
    (state newState : InterpreterState ctx)
    (equationLemma : state.EquationLemmaAt (.before root) (by grind))
    (controlFlow : Option ControlFlowAction)
    (rootRun :
      interpretOp root state rootIn = some (.ok (newState, controlFlow)))
    (sourceValues : Array RuntimeValue)
    (sourceValuesEq :
      (root.getResults ctx.raw rootIn).mapM newState.variables.getVar? =
        some sourceValues) :
    let runtimeValue :=
      executionRuntimeValue state newState root
    sourceSemantics pattern
      (semanticAssignmentOf ctx.raw source.env runtimeValue) ∧
    controlFlow = none ∧
    newState.memory = state.memory ∧
    (semanticOpOf ctx.raw runtimeValue root).results = sourceValues := by
  let runtimeValue :=
    executionRuntimeValue state newState root
  have sourceFacts :=
    matchSource_facts pattern.blueprint ctx ctxDom root source hmatch
  have facts := sourceFacts.matchFacts
  have sourceValuesBang :
      (root.getResults! ctx.raw).mapM newState.variables.getVar? =
        some sourceValues := by
    rw [OperationPtr.getResults!_eq_getResults rootIn]
    exact sourceValuesEq
  have hrootResults :
      (root.getResults! ctx.raw).map runtimeValue = sourceValues := by
    apply map_executionRuntimeValue_of_mapM_root
    · intro value hvalue
      exact hvalue
    · exact sourceValuesBang
  rcases interpretOp_some_iff.mp rootRun with
    ⟨rootOperands, rootResults, rootMemory, rootVariables,
      hrootOperands, hrootInterpret, hrootSet, hnewState⟩
  have hrootVariables : rootVariables = newState.variables := by
    have := congrArg InterpreterState.variables hnewState
    simpa using this.symm
  rw [hrootVariables] at hrootSet
  have hrootResultMap :
      (root.getResults! ctx.raw).mapM newState.variables.getVar? =
        some rootResults :=
    VariableState.mapM_getResults_eq_some_of_setResultValues hrootSet
  have hrootResultsEq : rootResults = sourceValues := by
    grind
  have hrootOperandMap :
      (root.getOperands! ctx.raw).map runtimeValue = rootOperands := by
    apply map_executionRuntimeValue_of_mapM_not_root
    · exact facts.op_operands_not_mem_root_results source.inBounds
        ctxDom facts.rootAtZero
    · simpa [VariableState.getOperandValues] using hrootOperands
  have hrootShape :=
    facts.pure root (by
      grind [Array.getElem?_eq_some_iff, facts.rootAtZero])
  have hrootFold :=
    (foldEvaluate_eq_ok_of_pureShape ctx.raw root hrootShape
      hrootInterpret).2.2
  have hrootValid :
      (semanticOpOf ctx.raw runtimeValue root).Valid := by
    simp only [SemanticOp.Valid, semanticOpOf]
    simpa [hrootOperandMap, hrootResults, hrootResultsEq] using hrootFold
  have hcontrolFlow :
      controlFlow = none :=
    (foldEvaluate_eq_ok_of_pureShape ctx.raw root hrootShape
      hrootInterpret).1
  have hmemory : newState.memory = state.memory := by
    have hrootMemory :=
      (foldEvaluate_eq_ok_of_pureShape ctx.raw root hrootShape
        hrootInterpret).2.1
    have := congrArg InterpreterState.memory hnewState
    grind
  have hconforms :
      ∀ value ∈ source.env.values,
        (runtimeValue value).Conforms (value.getType! ctx.raw) := by
    intro value hvalue
    obtain ⟨valueRuntime, hvalueRuntime⟩ :=
      facts.value_exists_in_state source.inBounds rootIn equationLemma
        rootRun hvalue
    have hnot :=
      facts.value_not_mem_root_results source.inBounds ctxDom rootIn hvalue
    change
      (executionRuntimeValue state newState root value).Conforms
        (value.getType! ctx.raw)
    rw [executionRuntimeValue_of_not_mem_root_results
      hnot hvalueRuntime]
    exact VariableState.getVar?_conforms hvalueRuntime
  have hallValid :
      ∀ semanticOp ∈
          (semanticAssignmentOf ctx.raw source.env runtimeValue).ops,
        semanticOp.Valid := by
    intro semanticOp hsemanticOp
    simp only [semanticAssignmentOf, Array.mem_map] at hsemanticOp
    rcases hsemanticOp with
      ⟨op, hopMem, rfl⟩
    obtain ⟨index, hindex, hopAt⟩ :=
      Array.getElem_of_mem hopMem
    have hop :
        source.env.ops[index]? = some op := by
      rw [Array.getElem?_eq_getElem hindex, hopAt]
    rcases facts.opDominates index op hop with
      ⟨_, rfl⟩ | ⟨hpositive, hstrict⟩
    · exact hrootValid
    · have hopEquation :=
        facts.producerEquation source.inBounds rootIn equationLemma
          hop (by omega)
      simp only [InterpreterState.EquationHolds] at hopEquation
      rcases hopEquation with ⟨producerFlow, hproducerRun⟩
      rcases interpretOp_some_iff.mp hproducerRun with
        ⟨producerOperands, producerResults, producerMemory,
          producerVariables, hproducerOperands, hproducerInterpret,
          hproducerSet, hproducerState⟩
      have hproducerVariables :
          producerVariables = state.variables := by
        have := congrArg InterpreterState.variables hproducerState
        simpa using this.symm
      rw [hproducerVariables] at hproducerSet
      have hproducerOperandMap :
          (op.getOperands! ctx.raw).map runtimeValue =
            producerOperands := by
        apply map_executionRuntimeValue_of_mapM_not_root
        · exact facts.op_operands_not_mem_root_results
            source.inBounds ctxDom hop
        · simpa [VariableState.getOperandValues] using hproducerOperands
      have hproducerResultMapM :
          (op.getResults! ctx.raw).mapM state.variables.getVar? =
            some producerResults :=
        VariableState.mapM_getResults_eq_some_of_setResultValues
          hproducerSet
      have hproducerResultMap :
          (op.getResults! ctx.raw).map runtimeValue =
            producerResults := by
        apply map_executionRuntimeValue_of_mapM_not_root
        · exact facts.producer_results_not_mem_root_results
            source.inBounds rootIn hop (by omega)
        · exact hproducerResultMapM
      have hproducerShape :=
        facts.pure op hopMem
      have hproducerFold :=
        (foldEvaluate_eq_ok_of_pureShape ctx.raw op hproducerShape
          hproducerInterpret).2.2
      simp only [SemanticOp.Valid, semanticOpOf]
      simpa [hproducerOperandMap, hproducerResultMap] using hproducerFold
  refine ⟨?_, hcontrolFlow, hmemory, hrootResults⟩
  refine ⟨?_, hallValid, ?_⟩
  · rcases sourceFacts.rootInfo with
      ⟨rootSpec, hrootSpec, hrootId, hrootShape⟩
    refine ⟨rootSpec, semanticOpOf ctx.raw runtimeValue root,
      hrootSpec, ?_, ?_⟩
    · rw [hrootId]
      exact semanticAssignmentOf_op_get facts.rootAtZero
    · simp [pureShape] at hrootShape
      exact hrootShape.1.1.1
  · exact matchSource_stepSemantics pattern.blueprint ctx root source
      hmatch runtimeValue hconforms

/--
The generated equation-normal-form semantic obligation.  Source assignments
are universal; target results and successful target evaluations are
existential; the root results must refine the selected replacement values.
-/
def PurePattern.Semantics (pattern : PurePattern) : Prop :=
  ∀ assignment : SourceAssignment,
    sourceSemantics pattern assignment →
    ∃ finalValues targetValues root,
      TargetSemantics assignment.types pattern.blueprint.targetOps.toList
        assignment.values finalValues ∧
      resolveRuntimeValues finalValues
        pattern.blueprint.replacement.get! = some targetValues ∧
      assignment.ops[0]? = some root ∧
      root.results ⊒ targetValues

/-- Compile a builder computation to a pure root-first pattern. -/
def build (builder : Builder Unit) : Except String PurePattern := do
  let (_, blueprint) ← builder {}
  if blueprint.root.isNone then
    throw "a root-first pattern requires matchRoot"
  if blueprint.replacement.isNone then
    throw "a root-first pattern requires replace"
  if hsafe : blueprintSafe blueprint then
    pure ⟨blueprint, hsafe⟩
  else
    throw "the pattern violates root-first value availability or binding order"

private structure MatchOutput (blueprint : Blueprint) (ctx : WfIRContext OpCode)
    (root : OperationPtr) where
  source : MatchResult ctx.raw
  sourceMatch : matchSource blueprint ctx root = some source
  target : TargetRunResult ctx
  targetRun :
    runTarget blueprint ctx source.env source.inBounds = some target
  values : Array ValuePtr
  valuesResolved :
    resolveValues target.env.values blueprint.replacement.get! = some values
  valuesSize : values.size = root.getNumResults! ctx.raw
  valuesInBounds : ∀ value ∈ values, value.InBounds target.ctx.raw

private def execute (pattern : PurePattern) (ctx : WfIRContext OpCode)
    (root : OperationPtr) :
    Option (Option (MatchOutput pattern.blueprint ctx root)) := do
  match hsource : matchSource pattern.blueprint ctx root with
  | none => pure none
  | some source =>
      let replacement := pattern.blueprint.replacement.get!
      guard (replacement.size = root.getNumResults! ctx.raw)
      match htarget :
          runTarget pattern.blueprint ctx source.env source.inBounds with
      | none => none
      | some target =>
          match hvalues : resolveValues target.env.values replacement with
          | none => none
          | some values =>
              if hsize : values.size = root.getNumResults! ctx.raw then
                if hbounds : ∀ value ∈ values, value.InBounds target.ctx.raw then
                  pure (some {
                    source
                    sourceMatch := hsource
                    target
                    targetRun := htarget
                    values
                    valuesResolved := hvalues
                    valuesSize := hsize
                    valuesInBounds := hbounds
                  })
                else
                  none
              else
                none

/-- Execute a compiled pattern as a `LocalRewritePattern`. -/
def PurePattern.run (pattern : PurePattern) : LocalRewritePattern OpCode :=
  fun ctx root => do
    match ← execute pattern ctx root with
    | none => pure (ctx, none)
    | some output =>
        pure (output.target.ctx, some (output.target.newOps, output.values))

private theorem MatchOutput.initialValuesRefineState
    {pattern : PurePattern} {ctx : WfIRContext OpCode}
    {root : OperationPtr}
    (output : MatchOutput pattern.blueprint ctx root)
    (ctxDom : ctx.Dom) (rootIn : root.InBounds ctx.raw)
    (state newState : InterpreterState ctx)
    (equationLemma : state.EquationLemmaAt (.before root) (by grind))
    {controlFlow : Option ControlFlowAction}
    (rootRun :
      interpretOp root state rootIn =
        some (.ok (newState, controlFlow)))
    (targetState : InterpreterState output.target.ctx)
    (targetDefines :
      targetState.DefinesDominating (.before root) (by
        exact InsertPoint.inBounds_before.mpr
          (output.target.created.inBounds_mono (.operation root) rootIn)))
    (hpattern :
      pattern.run ctx root =
        some (output.target.ctx,
          some (output.target.newOps, output.values)))
    (hreturnValuesInBounds : pattern.run.ReturnValuesInBounds)
    (hreturnValues : pattern.run.ReturnValues)
    (hreturnCtxChanges : pattern.run.ReturnCtxChanges)
    (hrefinement :
      state.isRefinedByAt targetState
        (LocalRewritePattern.mapping hpattern
          hreturnValuesInBounds hreturnValues hreturnCtxChanges)
        (.at (.before root)) (.at (.before root))) :
    ValuesRefineState output.source.env.values
      (output.source.env.values.map
        (executionRuntimeValue state newState root))
      targetState := by
  have sourceFacts :=
    matchSource_facts pattern.blueprint ctx ctxDom root output.source
      output.sourceMatch
  have facts := sourceFacts.matchFacts
  have hexists :
      ∃ actualValues,
        output.source.env.values.mapM
          targetState.variables.getVar? = some actualValues := by
    rw [Array.exists_mapM_option_eq_some_iff]
    intro index hindex
    let value := output.source.env.values[index]
    have hvalue : value ∈ output.source.env.values :=
      Array.getElem_mem hindex
    have valueIn : value.InBounds ctx.raw :=
      output.source.inBounds.2 value hvalue
    have valueDom : value.dominatesIp (.before root) ctx :=
      facts.valueDominates value hvalue
    exact targetDefines.exists_getVar_of_dominatesIp
      (output.target.created.inBounds_mono (.value value) valueIn)
      (output.target.created.value_dominatesIp_before_mono
        valueIn rootIn valueDom)
  rcases hexists with ⟨actualValues, hactualValues⟩
  have hactualSize :
      output.source.env.values.size = actualValues.size :=
    Array.size_eq_of_mapM_eq_some hactualValues
  refine ⟨actualValues, hactualValues, ?_⟩
  simp only [RuntimeValue.arrayIsRefinedBy]
  constructor
  · have hsize :=
      Array.size_eq_of_mapM_eq_some hactualValues
    simpa using hsize
  · intro index hindex
    have henvIndex :
        index < output.source.env.values.size := by
      simpa using hindex
    let value := output.source.env.values[index]
    have hvalue : value ∈ output.source.env.values :=
      Array.getElem_mem henvIndex
    have valueIn : value.InBounds ctx.raw :=
      output.source.inBounds.2 value hvalue
    have valueDom : value.dominatesIp (.before root) ctx :=
      facts.valueDominates value hvalue
    obtain ⟨sourceValue, hsourceValue⟩ :=
      facts.value_exists_in_state output.source.inBounds rootIn
        equationLemma rootRun hvalue
    have hnot :
        value ∉ root.getResults! ctx.raw :=
      facts.value_not_mem_root_results output.source.inBounds ctxDom
        rootIn hvalue
    have htargetValue :=
      Array.mapM_option_eq_some_implies hactualValues index
        (by omega)
    have hmapping :
        (LocalRewritePattern.mapping hpattern
          hreturnValuesInBounds hreturnValues hreturnCtxChanges
          ⟨value, valueIn⟩).val = value := by
      exact LocalRewritePattern.mapping_eq_of_not_mem_results
        hpattern hreturnValuesInBounds hreturnValues hreturnCtxChanges
        valueIn hnot
    have hvalueRefinement :=
      InterpreterState.isRefinedByAt_value hrefinement value valueIn
        (by simpa using valueDom)
        (by
          rw [hmapping]
          rw [ValuePtr.inScopeAt_at]
          exact output.target.created.value_dominatesIp_before_mono
            valueIn rootIn valueDom)
        sourceValue hsourceValue
        actualValues[index] (by simpa [value, hmapping] using htargetValue)
    rw [getElem!_pos
      (output.source.env.values.map
        (executionRuntimeValue state newState root))
      index hindex]
    rw [getElem!_pos actualValues index (by omega)]
    rw [Array.getElem_map]
    rw [executionRuntimeValue_of_not_mem_root_results hnot hsourceValue]
    exact hvalueRefinement

private theorem run_eq_some_match_implies
    {pattern : PurePattern} {ctx newCtx : WfIRContext OpCode}
    {root : OperationPtr} {newOps : Array OperationPtr}
    {newValues : Array ValuePtr}
    (h :
      pattern.run ctx root = some (newCtx, some (newOps, newValues))) :
    ∃ output : MatchOutput pattern.blueprint ctx root,
      execute pattern ctx root = some (some output) ∧
      output.target.ctx = newCtx ∧
      output.target.newOps = newOps ∧
      output.values = newValues := by
  cases hexecute : execute pattern ctx root with
  | none =>
      rw [PurePattern.run, hexecute] at h
      simp at h
  | some result =>
      cases result with
      | none =>
          rw [PurePattern.run, hexecute] at h
          simp at h
      | some output =>
          rw [PurePattern.run, hexecute] at h
          simp at h
          exact ⟨output, rfl, h.1, h.2.1, h.2.2⟩

/-- A non-match returns the original context. -/
theorem PurePattern.returnsCtxNoChanges (pattern : PurePattern) :
    pattern.run.ReturnsCtxNoChanges := by
  simp only [LocalRewritePattern.ReturnsCtxNoChanges]
  intro ctx root newCtx h
  cases hexecute : execute pattern ctx root with
  | none => simp [PurePattern.run, hexecute] at h
  | some result =>
      cases result <;> simp_all [PurePattern.run]

/-- A match only creates detached target operations. -/
theorem PurePattern.returnCtxChanges (pattern : PurePattern) :
    pattern.run.ReturnCtxChanges := by
  simp only [LocalRewritePattern.ReturnCtxChanges]
  intro ctx root newCtx newOps newValues h
  obtain ⟨output, _, rfl, _, _⟩ := run_eq_some_match_implies h
  exact output.target.created

/-- The returned operation array is exactly the newly created target DAG. -/
theorem PurePattern.returnOps (pattern : PurePattern) :
    pattern.run.ReturnOps := by
  simp only [LocalRewritePattern.ReturnOps]
  intro ctx root newCtx newOps newValues h operation
  obtain ⟨output, _, hctx, hops, _⟩ := run_eq_some_match_implies h
  subst newCtx
  subst newOps
  exact output.target.returnOps operation

/-- Replacement arity equals root result arity. -/
theorem PurePattern.returnValues (pattern : PurePattern) :
    pattern.run.ReturnValues := by
  simp only [LocalRewritePattern.ReturnValues]
  intro ctx root rootIn newCtx newOps newValues h
  obtain ⟨output, _, _, _, hvalues⟩ := run_eq_some_match_implies h
  subst newValues
  exact output.valuesSize

/-- Every replacement value is in bounds in the returned context. -/
theorem PurePattern.returnValuesInBounds (pattern : PurePattern) :
    pattern.run.ReturnValuesInBounds := by
  simp only [LocalRewritePattern.ReturnValuesInBounds]
  intro ctx root newCtx newOps newValues h value hvalue
  obtain ⟨output, _, hctx, _, hvalues⟩ := run_eq_some_match_implies h
  subst newCtx
  subst newValues
  exact output.valuesInBounds value hvalue

/--
The value-level semantic obligation is sound for the executable root-first
matcher and target builder.
-/
theorem PurePattern.semanticSoundness (pattern : PurePattern) :
    pattern.Semantics →
    pattern.run.PreservesSemantics
      pattern.returnOps
      pattern.returnCtxChanges
      pattern.returnValuesInBounds
      pattern.returnValues := by
  intro hsemantics
  simp only [LocalRewritePattern.PreservesSemantics]
  intro ctx ctxDom ctxVerified root rootIn
    newCtx newOps newValues hpattern
    state equationLemma newState controlFlow rootRun
    sourceValues sourceValuesEq
    targetState targetEquationLemma targetDefines hrefinement
  obtain ⟨output, _, hctx, hops, hvalues⟩ :=
    run_eq_some_match_implies hpattern
  subst newCtx
  subst newOps
  subst newValues
  let runtimeValue :=
    executionRuntimeValue state newState root
  have hsource :=
    sourceSemantics_of_execution pattern ctx ctxDom root rootIn
      output.source output.sourceMatch state newState equationLemma
      controlFlow rootRun sourceValues sourceValuesEq
  change
    sourceSemantics pattern
        (semanticAssignmentOf ctx.raw output.source.env runtimeValue) ∧
      controlFlow = none ∧
      newState.memory = state.memory ∧
      (semanticOpOf ctx.raw runtimeValue root).results = sourceValues
    at hsource
  rcases hsource with
    ⟨hsourceSemantics, hcontrolFlow, hsourceMemory, hsourceResults⟩
  subst controlFlow
  obtain ⟨finalSemanticValues, replacementSemanticValues, semanticRoot,
      htargetSemantics, hreplacementSemantics, hsemanticRoot,
      hrootRefinement⟩ :=
    hsemantics
      (semanticAssignmentOf ctx.raw output.source.env runtimeValue)
      hsourceSemantics
  have sourceFacts :=
    matchSource_facts pattern.blueprint ctx ctxDom root output.source
      output.sourceMatch
  have hsemanticRootEq :
      semanticRoot = semanticOpOf ctx.raw runtimeValue root := by
    have hrootAtZero :=
      semanticAssignmentOf_op_get (ctx := ctx.raw)
        (runtimeValue := runtimeValue)
        sourceFacts.matchFacts.rootAtZero
    grind
  subst semanticRoot
  rw [hsourceResults] at hrootRefinement
  have hinitialRefinement :=
    output.initialValuesRefineState ctxDom rootIn state newState
      equationLemma rootRun targetState targetDefines hpattern
      pattern.returnValuesInBounds pattern.returnValues
      pattern.returnCtxChanges hrefinement
  have htargetRun :
      runTargetList pattern.blueprint.targetOps.toList ctx
          output.source.env output.source.inBounds =
        some output.target := by
    simpa [runTarget] using output.targetRun
  change
    TargetSemantics output.source.env.types
      pattern.blueprint.targetOps.toList
      (output.source.env.values.map runtimeValue)
      finalSemanticValues
    at htargetSemantics
  obtain ⟨finalState, actualValues, htargetRunSemantics,
      htargetMemory, hactualValues, hfinalRefinement⟩ :=
    runTargetList_semantics pattern.blueprint.targetOps.toList ctx
      output.source.env output.source.inBounds output.target htargetRun
      htargetSemantics targetState hinitialRefinement
  obtain ⟨replacementActualValues, hreplacementActual,
      hreplacementRefinement⟩ :=
    resolveValues_refines output.valuesResolved hreplacementSemantics
      hactualValues hfinalRefinement
  refine ⟨finalState, htargetRunSemantics, ?_, replacementActualValues,
    hreplacementActual, ?_⟩
  · have hinitialMemory :=
      InterpreterState.isRefinedByAt_memory hrefinement
    grind
  · exact RuntimeValue.arrayIsRefinedBy_trans
      hrootRefinement hreplacementRefinement

/--
The generated value-level semantic obligation implies preservation of the
interpreter semantics for the compiled local rewrite.
-/
theorem PurePattern.preservesSemantics (pattern : PurePattern)
    (h : pattern.Semantics) :
    pattern.run.PreservesSemantics
      pattern.returnOps
      pattern.returnCtxChanges
      pattern.returnValuesInBounds
      pattern.returnValues :=
  pattern.semanticSoundness h

namespace Examples

private def i32 : TypeAttr :=
  IntegerType.mk 32

private def zeroProperties : ArithConstantProperties :=
  .mk (IntegerAttr.mk 0 (IntegerType.mk 32))

/--
The pilot root-first pattern:

```
%zero = arith.constant 0 : i32
%sum  = arith.addi %x, %zero : i32
```

is replaced by `%x`.  Its semantic proof is deliberately left to the generic
soundness layer in PR 3; this declaration supplies the compiled matcher,
generated semantic proposition, and all structural certificates.
-/
def arithAddZeroBuild : Except String PurePattern :=
  build do
    let root ← matchRoot (.arith .addi)
    let x ← root.operand 0
    let zero ← root.operand 1
    let type ← root.resultType 0
    let _ ← matchType type integerType
    let _ ← matchType type (exactType i32)
    checkType x type
    checkType zero type

    let zeroOp ← matchDefiningOp zero (.arith .constant)
    checkProperties zeroOp zeroProperties

    replace root #[x]

/-- The compiled add-zero pattern. -/
def arithAddZero : PurePattern :=
  match arithAddZeroBuild with
  | .ok pattern => pattern
  | .error _ => ⟨{}, by native_decide⟩

/--
Arithmetic certificate for the add-zero pilot.  This is kept explicit while
the arithmetic interpreter lacks reusable `addi`/zero refinement lemmas.
-/
axiom arithAddZero_semantics : arithAddZero.Semantics

theorem arithAddZero_preservesSemantics :
    arithAddZero.run.PreservesSemantics
      arithAddZero.returnOps
      arithAddZero.returnCtxChanges
      arithAddZero.returnValuesInBounds
      arithAddZero.returnValues :=
  arithAddZero.preservesSemantics arithAddZero_semantics

/--
A target-producing example.  The second target operation consumes the first
one's result, exercising topological target-DAG construction.
-/
def twoOperationTargetBuild : Except String PurePattern :=
  build do
    let root ← matchRoot (.arith .addi)
    let x ← root.operand 0
    let zero ← root.operand 1
    let type ← root.resultType 0
    let _ ← matchType type integerType
    checkType x type
    checkType zero type

    let zeroOp ← matchDefiningOp zero (.arith .constant)
    checkProperties zeroOp zeroProperties

    let (_, first) ←
      createOp1 (.arith .addi) (default : ArithIntegerOverflowFlagsProperties)
        type #[x, zero]
    let (_, second) ←
      createOp1 (.arith .addi) (default : ArithIntegerOverflowFlagsProperties)
        type #[first, zero]
    replace root #[second]

def twoOperationTarget : PurePattern :=
  match twoOperationTargetBuild with
  | .ok pattern => pattern
  | .error _ => ⟨{}, by native_decide⟩

/--
Arithmetic certificate for the target-producing example.  Both target adds
consume the matched zero value, so the two-operation target still refines the
matched `x + 0` root.
-/
axiom twoOperationTarget_semantics : twoOperationTarget.Semantics

theorem twoOperationTarget_preservesSemantics :
    twoOperationTarget.run.PreservesSemantics
      twoOperationTarget.returnOps
      twoOperationTarget.returnCtxChanges
      twoOperationTarget.returnValuesInBounds
      twoOperationTarget.returnValues :=
  twoOperationTarget.preservesSemantics twoOperationTarget_semantics

end Examples

end RootFirst
end Veir
