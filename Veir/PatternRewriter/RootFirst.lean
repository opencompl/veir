module

public import Veir.Interpreter.Purity
public import Veir.PatternRewriter.Semantics

import all Veir.IR.Basic

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

private def blueprintSourceSemantics (blueprint : Blueprint)
    (assignment : SourceAssignment) : Prop :=
  assignment.ops.size = blueprint.sourceOps.size ∧
  assignment.values.size =
    blueprint.valueCount -
      blueprint.targetOps.foldl (fun n op => n + op.resultIds.size) 0 ∧
  assignment.types.size = blueprint.typeCount ∧
  (∀ spec ∈ blueprint.sourceOps,
    ∃ op,
      assignment.ops[spec.id]? = some op ∧
      op.opCode = spec.opCode ∧
      op.Valid) ∧
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
      (hsize : results.size = spec.resultIds.size)
      (hrest : TargetSemantics types rest (values ++ results) finalValues) :
      TargetSemantics types (spec :: rest) values finalValues

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
Trusted semantic bridge for the initial root-first vertical slice.

The executable side of the DSL establishes binding availability, source
matching, pure target construction, context growth, and replacement
well-formedness.  The remaining bridge packages the dominance/equation-lemma
transport and reconstruction of the target `interpretOpList`.  It is kept as
one explicit axiom while the underlying dominance model is axiomatic, rather
than scattering assumptions about dominance and `createOp` preservation
through the matcher proofs.
-/
axiom PurePattern.semanticSoundnessAxiom (pattern : PurePattern) :
    pattern.Semantics →
    pattern.run.PreservesSemantics
      pattern.returnOps
      pattern.returnCtxChanges
      pattern.returnValuesInBounds
      pattern.returnValues

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
  pattern.semanticSoundnessAxiom h

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
