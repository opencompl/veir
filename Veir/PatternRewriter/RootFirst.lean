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

private def runMatchSteps (steps : List MatchStep) (ctx : IRContext OpCode)
    (env : MatchEnv) (henv : env.InBounds ctx) : Option (MatchResult ctx) :=
  match steps with
  | [] => some ⟨env, henv⟩
  | step :: rest => do
      let result ← runMatchStep step ctx env henv
      runMatchSteps rest ctx result.env result.inBounds

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

private structure TargetStepResult (initialCtx : WfIRContext OpCode) where
  ctx : WfIRContext OpCode
  env : MatchEnv
  op : OperationPtr
  created : WfIRContext.WithCreatedOps initialCtx ctx
  operationInBounds :
    ∀ operation, operation.InBounds ctx.raw ↔
      operation.InBounds initialCtx.raw ∨ operation = op
  opNotInBounds : ¬op.InBounds initialCtx.raw
  envInBounds : env.InBounds ctx.raw

private def runTargetOpSpec (spec : TargetOpSpec)
    (ctx : WfIRContext OpCode) (env : MatchEnv)
    (henv : env.InBounds ctx.raw) :
    Option (TargetStepResult ctx) := do
  let resultTypes ← resolveTypes env.types spec.resultTypes
  let operands ← resolveValues env.values spec.operands
  if hoper : ∀ operand, operand ∈ operands → operand.InBounds ctx.raw then
    match hcreate :
      WfRewriter.createOp ctx spec.opCode resultTypes operands #[] #[]
        spec.properties none hoper (by simp) (by simp) (by simp [Option.maybe_def]) with
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

private def SemanticOp.propertiesAs (op : SemanticOp) (opCode : OpCode) :
    Option (propertiesOf opCode) :=
  if h : op.opCode = opCode then
    some (h ▸ op.properties)
  else
    none

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

private def blueprintSourceSemantics (blueprint : Blueprint)
    (assignment : SourceAssignment) : Prop :=
  assignment.ops.size = blueprint.sourceOps.size ∧
  assignment.values.size =
    blueprint.valueCount - blueprint.targetOps.foldl (fun n op => n + op.resultIds.size) 0 ∧
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
  blueprint : Blueprint

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
  pure ⟨blueprint⟩

private structure MatchOutput (ctx : WfIRContext OpCode)
    (root : OperationPtr) where
  target : TargetRunResult ctx
  values : Array ValuePtr
  valuesSize : values.size = root.getNumResults! ctx.raw
  valuesInBounds : ∀ value ∈ values, value.InBounds target.ctx.raw

private def execute (pattern : PurePattern) (ctx : WfIRContext OpCode)
    (root : OperationPtr) : Option (Option (MatchOutput ctx root)) := do
  let some source := matchSource pattern.blueprint ctx root
    | pure none
  let replacement := pattern.blueprint.replacement.get!
  guard (replacement.size = root.getNumResults! ctx.raw)
  let target ← runTarget pattern.blueprint ctx source.env source.inBounds
  let values ← resolveValues target.env.values replacement
  if hsize : values.size = root.getNumResults! ctx.raw then
    if hbounds : ∀ value ∈ values, value.InBounds target.ctx.raw then
      pure (some { target, values, valuesSize := hsize, valuesInBounds := hbounds })
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
    ∃ output : MatchOutput ctx root,
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
  | .error _ => ⟨{}⟩

/--
A target-producing example.  The second target operation consumes the first
one's result, exercising topological target-DAG construction.
-/
def twoOperationTargetBuild : Except String PurePattern :=
  build do
    let root ← matchRoot (.arith .addi)
    let x ← root.operand 0
    let y ← root.operand 1
    let type ← root.resultType 0
    let _ ← matchType type integerType
    checkType x type
    checkType y type

    let (_, first) ←
      createOp1 (.arith .addi) (default : ArithIntegerOverflowFlagsProperties)
        type #[x, y]
    let (_, second) ←
      createOp1 (.arith .addi) (default : ArithIntegerOverflowFlagsProperties)
        type #[first, x]
    replace root #[second]

end Examples

end RootFirst
end Veir
