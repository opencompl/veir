module

public import Veir.PatternRewriter.Puddle.Execution
public import Veir.PatternRewriter.Puddle.Builders
public import Veir.Interpreter.Evaluate
public import Veir.PatternRewriter.Semantics

import Veir.Data.Refinement
import all Veir.GlobalOpInfo
import all Veir.Interpreter.Basic
import all Veir.Interpreter.Refinement.Basic
import all Veir.IR.Attribute
import all Veir.IR.Basic
import all Veir.PatternRewriter.Semantics

/-!
# Puddle Patterns Validity

This file defines the obligations for a Puddle pattern to be considered valid (`Pattern.Valid`),
both structurally and semantically. If `Pattern.Valid` holds, then compiling the Puddle pattern to
with `Pattern.compile` should produce a rewrite pattern that satisfies `LocalRewritePattern.Valid`.
-/

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-!
## Supported Opcodes

Puddle currently supports operations that cannot terminate a block and have no memory effects.
-/

/--
An opcode is supported when it is not a terminator and has no memory effects for any possible
property value.

We could in the future support opcodes when we know that the properties matched or created by the
pattern are such that the operation has no memory effects, but this is only happening in rare cases.
-/
def SupportedOpCode (opCode : OpInfo) : Prop :=
  HasOpInfo.isTerminator opCode = false ∧
    ∀ property, HasOpInfo.getEffects opCode property = .none

/-- A match declaration is supported when the opcode of an operation declaration is supported. -/
@[expose]
def MatchDecl.Supported (decl : MatchDecl OpInfo) : Prop :=
  match decl with
  | .operation opCode _ _ _ _ _ _ _ => SupportedOpCode opCode
  | _ => True

/-- Every declaration in a match program uses supported opcodes. -/
@[expose]
def MatchProg.Supported (prog : MatchProg OpInfo α) : Prop :=
  ∀ decl ∈ prog.decls, decl.Supported

/-- A creation declaration is supported when the opcode of an operation declaration is supported. -/
@[expose]
def CreateDecl.Supported : CreateDecl OpInfo → Prop
  | .operation opCode _ _ _ _ _ => SupportedOpCode opCode
  | _ => True

/-- Every declaration in a creation program uses supported opcodes. -/
@[expose]
def CreateProg.Supported (prog : CreateProg OpInfo α) : Prop :=
  ∀ decl ∈ prog.decls, decl.Supported

/-- The pattern only references supported opcodes. -/
@[expose]
def Pattern.Supported (rule : Pattern OpInfo) : Prop :=
  rule.matcher.Supported ∧ rule.creation.Supported

/-! ## Denotational validity

This interpretation is deliberately separate from `Pattern`: pattern authors only write the matcher
and replacement. The interpreter below turns those two pieces of syntax into the proposition they
must prove. -/

inductive SemanticBinding where
| op (results : Array RuntimeValue)
| value (value : RuntimeValue)
| type (type : TypeAttr)
| property (opCode : OpCode) (value : propertiesOf opCode)

abbrev SemanticAssignment := Array (Option SemanticBinding)

@[expose]
def SemanticAssignment.empty (size : Nat) : SemanticAssignment :=
  Array.replicate size none

@[expose]
def SemanticAssignment.bind (assignment : SemanticAssignment)
    (id : Nat) (binding : SemanticBinding) : SemanticAssignment :=
  if h : id < assignment.size then
    assignment.set id (some binding)
  else
    assignment ++ Array.replicate (id - assignment.size) none ++ #[some binding]

@[expose]
def SemanticAssignment.bindOp (assignment : SemanticAssignment)
    (handle : Handle OpCode .op) (results : Array RuntimeValue) : SemanticAssignment :=
  assignment.bind handle.id (.op results)

@[expose]
def SemanticAssignment.bindValue (assignment : SemanticAssignment)
    (handle : Handle OpCode .value) (value : RuntimeValue) : SemanticAssignment :=
  assignment.bind handle.id (.value value)

@[expose]
def SemanticAssignment.bindType (assignment : SemanticAssignment)
    (handle : Handle OpCode .type) (type : TypeAttr) : SemanticAssignment :=
  assignment.bind handle.id (.type type)

@[expose]
def SemanticAssignment.bindProperty (assignment : SemanticAssignment)
    (handle : Handle OpCode (.prop opCode)) (value : propertiesOf opCode) : SemanticAssignment :=
  assignment.bind handle.id (.property opCode value)

@[expose]
def SemanticAssignment.bindValues (assignment : SemanticAssignment)
    (handles : List (Handle OpCode .value)) (values : List RuntimeValue) : SemanticAssignment :=
  match handles, values with
  | handle :: handles, value :: values =>
    (assignment.bindValue handle value).bindValues handles values
  | _, _ => assignment

@[expose]
def SemanticAssignment.getOp (assignment : SemanticAssignment)
    (handle : Handle OpCode .op) : Option (Array RuntimeValue) :=
  match assignment[handle.id]? with
  | some (some (.op results)) => some results
  | _ => none

@[expose]
def SemanticAssignment.getValue (assignment : SemanticAssignment)
    (handle : Handle OpCode .value) : Option RuntimeValue :=
  match assignment[handle.id]? with
  | some (some (.value value)) => some value
  | _ => none

@[expose]
def SemanticAssignment.getType (assignment : SemanticAssignment)
    (handle : Handle OpCode .type) : Option TypeAttr :=
  match assignment[handle.id]? with
  | some (some (.type type)) => some type
  | _ => none

@[expose]
def SemanticAssignment.getProperty (assignment : SemanticAssignment)
    (handle : Handle OpCode (.prop opCode)) : Option (propertiesOf opCode) :=
  match assignment[handle.id]? with
  | some (some (.property actualOpCode value)) =>
    if h : actualOpCode = opCode then
      some (h ▸ value)
    else none
  | _ => none

@[expose]
def SemanticAssignment.getValues (assignment : SemanticAssignment)
    (handles : Array (Handle OpCode .value)) : Option (Array RuntimeValue) :=
  handles.mapM assignment.getValue

@[expose]
def SemanticAssignment.getTypes (assignment : SemanticAssignment)
    (handles : Array (Handle OpCode .type)) : Option (Array TypeAttr) :=
  handles.mapM assignment.getType

/-- Interpreter-backed denotation used for effect-free operations without a specialized Puddle
denotation.  Successors and control flow are existential because matcher syntax records neither;
the result values are the observable part used by a rewrite. -/
@[expose]
def InterpretsTo (opCode : OpCode) (actual : propertiesOf opCode)
    (resultTypes : Array TypeAttr) (operands results : Array RuntimeValue) : Prop :=
  ∃ successors memory controlFlow,
    interpretOp' opCode actual resultTypes operands successors memory =
      .ok (results, memory, controlFlow)

@[expose]
def MatchDecl.Models (decl : MatchDecl OpCode) (assignment : SemanticAssignment) : Prop :=
  match decl with
  | .type matcher handle =>
    ∃ type, assignment.getType handle = some type ∧ matcher type = true
  | .value typeHandle handle =>
    ∃ type,
      assignment.getType typeHandle = some type ∧
      ∀ value, assignment.getValue handle = some value → value.Conforms type
  | .operation opCode operandHandles returnTypeHandles property propertyHandle handle resultHandles _ =>
    ∃ operands resultTypes results actualProperty,
      assignment.getValues operandHandles = some operands ∧
      assignment.getTypes returnTypeHandles = some resultTypes ∧
      assignment.getOp handle = some results ∧
      assignment.getProperty propertyHandle = some actualProperty ∧
      (∀ boundResults, assignment.getValues resultHandles = some boundResults →
        boundResults = results) ∧
      property actualProperty = true ∧
      InterpretsTo opCode actualProperty resultTypes operands results

/-! ## Root Constraint -/

/--
The first declaration in the match program is an operation declaration whose operation handle is
the program's distinguished root handle.
-/
def MatchProg.ConstrainsRoot (prog : MatchProg OpInfo α) : Prop :=
  match prog.decls with
  | .operation _ _ _ _ _ opHandle _ _ :: _ => opHandle = prog.rootHandle
  | _ => False

/-- Return the hidden SSA-result handles from the program's leading root constraint. -/
@[expose]
def MatchProg.rootResults? (prog : MatchProg OpCode α) :
    Option (Array (Handle OpCode .value)) :=
  match prog.decls with
  | .operation _ _ _ _ _ opHandle results _ :: _ =>
    if opHandle = prog.rootHandle then some results else none
  | _ => none

/-- Pointwise semantic facts for every matcher declaration. -/
@[expose]
def MatchProg.Models (prog : MatchProg OpCode α) (assignment : SemanticAssignment) : Prop :=
  (assignment.getOp prog.rootHandle).isSome ∧
    ∀ decl ∈ prog.decls, decl.Models assignment

@[expose]
def Replacement.refinesRoot (replacement : Replacement OpCode) (root : Handle OpCode .op)
    (matched final : SemanticAssignment) : Prop :=
  match matched.getOp root, final.getValues replacement.values with
  | some rootResults, some replacementValues => rootResults ⊒ replacementValues
  | _, _ => False

/-! ## Structural well-formedness -/

/-- The abstract context of handle identifiers and their runtime kinds. -/
structure HandleContext where
  bindings : List (Nat × HandleType OpCode)
  unavailable : List Nat
deriving DecidableEq

namespace HandleContext

/-- The empty handle context. -/
def empty : HandleContext := ⟨[], []⟩

/-- Look up the kind occupying an identifier. -/
def lookup (handles : HandleContext) (id : Nat) : Option (HandleType OpCode) :=
  let rec lookupBindings : List (Nat × HandleType OpCode) → Option (HandleType OpCode)
    | [] => none
    | (definedId, kind) :: rest =>
        if definedId = id then some kind else lookupBindings rest
  lookupBindings handles.bindings

/-- Succeed exactly when a typed handle has already been defined with precisely that kind. -/
@[expose]
def require (handles : HandleContext) {kind : HandleType OpCode}
    (handle : Handle OpCode kind) : Option HandleContext :=
  if handles.lookup handle.id = some kind ∧ handle.id ∉ handles.unavailable then
    some handles
  else
    none

/--
Record a matcher-defined handle. Repeated definitions of the same typed handle are permitted,
because matcher binding is idempotent, but reusing an identifier at another kind is rejected.
-/
def insert (handles : HandleContext) {kind : HandleType OpCode}
    (handle : Handle OpCode kind) : Option HandleContext :=
  match handles.lookup handle.id with
  | none => some ⟨(handle.id, kind) :: handles.bindings, handles.unavailable⟩
  | some actual => if actual = kind then some handles else none

/-- Record several matcher-defined handles. -/
@[expose]
def insertMany (handles : HandleContext) :
    List (Handle OpCode kind) → Option HandleContext
  | [] => some handles
  | handle :: rest => do
      let handles ← handles.insert handle
      handles.insertMany rest

/--
Record a creation output, requiring its identifier to be entirely fresh regardless of kind.
-/
def insertFresh (handles : HandleContext) {kind : HandleType OpCode}
    (handle : Handle OpCode kind) : Option HandleContext :=
  match handles.lookup handle.id with
  | none => some ⟨(handle.id, kind) :: handles.bindings, handles.unavailable⟩
  | some _ => none

/-- Record several creation outputs, checking freshness between the outputs as well. -/
@[expose]
def insertManyFresh (handles : HandleContext) :
    List (Handle OpCode kind) → Option HandleContext
  | [] => some handles
  | handle :: rest => do
      let handles ← handles.insertFresh handle
      handles.insertManyFresh rest

/-- Require every handle in a homogeneous list to be available. -/
@[expose]
def requireMany (handles : HandleContext) :
    List (Handle OpCode kind) → Option HandleContext
  | [] => some handles
  | handle :: used => do
      let handles ← handles.require handle
      handles.requireMany used

/-- Mark an allocated handle as unavailable to creation and replacement inputs. -/
def forbid (handles : HandleContext) (handle : Handle OpCode kind) : HandleContext :=
  ⟨handles.bindings, handle.id :: handles.unavailable⟩

/-- Mark several allocated handles as unavailable while retaining them for freshness checks. -/
@[expose]
def forbidMany (handles : HandleContext) :
    List (Handle OpCode kind) → HandleContext
  | [] => handles
  | handle :: rest => (handles.forbid handle).forbidMany rest

end HandleContext

/-- Collect the handles that a matcher declaration can bind during a successful match. -/
@[expose]
def MatchDecl.collectBindings (decl : MatchDecl OpCode)
    (defined : HandleContext) : Option HandleContext := do
  match decl with
  | .operation _ operands resultTypes _ propertyHandle opHandle results _ =>
      let defined ← defined.insert opHandle
      let defined ← defined.insertMany results.toList
      let defined ← defined.insert propertyHandle
      let defined ← defined.insertMany resultTypes.toList
      defined.insertMany operands.toList
  | .value typeHandle _ =>
      defined.insert typeHandle
  | .type .. =>
      some defined

/-- Collect matcher-defined handles globally, without imposing matcher use-point ordering. -/
@[expose]
def MatchProg.collectBindingsDecls :
    List (MatchDecl OpCode) → HandleContext → Option HandleContext
  | [], defined => some defined
  | decl :: decls, defined => do
      let defined ← decl.collectBindings defined
      MatchProg.collectBindingsDecls decls defined

/-- Collect every handle that can be bound by a successful matcher. -/
@[expose]
def MatchProg.collectBindings (prog : MatchProg OpCode α) : Option HandleContext :=
  do
    let rootResults ← prog.rootResults?
    let defined ← HandleContext.empty.insert prog.rootHandle
    let defined ← MatchProg.collectBindingsDecls prog.decls defined
    let defined := defined.forbid prog.rootHandle
    return defined.forbidMany rootResults.toList

/--
Check one creation declaration and extend the context with its outputs. Inputs must be available at
this exact program point, while all outputs must have globally fresh identifiers.
-/
@[expose]
def CreateDecl.checkBindings (decl : CreateDecl OpCode)
    (defined : HandleContext) : Option HandleContext := do
  match decl with
  | .type _ result =>
      defined.insertFresh result
  | .property _ _ result =>
      defined.insertFresh result
  | .operation _ operands resultTypes properties opHandle resultHandles =>
      let defined ← defined.requireMany operands.toList
      let defined ← defined.requireMany resultTypes.toList
      let defined ← defined.require properties
      guard (resultHandles.size = resultTypes.size)
      let defined ← defined.insertFresh opHandle
      defined.insertManyFresh resultHandles.toList

/-- Traverse creation declarations in execution order, threading the available-handle context. -/
@[expose]
def CreateProg.checkBindingsDecls :
    List (CreateDecl OpCode) → HandleContext → Option HandleContext
  | [], defined => some defined
  | decl :: decls, defined => do
      let defined ← decl.checkBindings defined
      CreateProg.checkBindingsDecls decls defined

/-- Validate a creation program from a matcher-defined handle context. -/
@[expose]
def CreateProg.checkBindings (prog : CreateProg OpCode α)
    (defined : HandleContext) : Option HandleContext :=
  CreateProg.checkBindingsDecls prog.decls defined

/-- Require every replacement value to be available after the creation program. -/
@[expose]
def Replacement.checkBindings (replacement : Replacement OpCode)
    (defined : HandleContext) : Option HandleContext :=
  defined.requireMany replacement.values.toList

/-- Run the complete structural checker. -/
@[expose]
def Pattern.checkStructure (rule : Pattern OpCode) : Option HandleContext := do
  let defined ← rule.matcher.collectBindings
  let defined ← rule.creation.checkBindings defined
  rule.replacement.checkBindings defined

/--
Structural validity for the whole rule. The matcher is collected globally; creation is checked in
execution order; replacement is checked against the final context.
-/
@[expose]
def Pattern.StructurallyWellFormed (rule : Pattern OpCode) : Prop :=
  rule.checkStructure.isSome = true

instance (rule : Pattern OpCode) : Decidable rule.StructurallyWellFormed := by
  unfold Pattern.StructurallyWellFormed
  infer_instance

/-- Pointwise semantic facts imposed by one creation declaration on the final assignment. -/
@[expose]
def CreateDecl.Models (decl : CreateDecl OpCode) (assignment : SemanticAssignment) : Prop :=
  match decl with
  | .type value result =>
      assignment.getType result = some value
  | .property _ value result =>
      assignment.getProperty result = some value
  | .operation opCode operandHandles resultTypeHandles propertyHandle opHandle resultHandles =>
      ∃ operands resultTypes property results,
        assignment.getValues operandHandles = some operands ∧
        assignment.getTypes resultTypeHandles = some resultTypes ∧
        assignment.getProperty propertyHandle = some property ∧
        assignment.getOp opHandle = some results ∧
        assignment.getValues resultHandles = some results ∧
        InterpretsTo opCode property resultTypes operands results

/-- Pointwise semantic facts for every creation declaration. -/
@[expose]
def CreateProg.Models (prog : CreateProg OpCode α) (assignment : SemanticAssignment) : Prop :=
  ∀ decl ∈ prog.decls, decl.Models assignment

/-- Evaluate a created operation semantically using a canonical empty memory. Creation only admits
effect-free, nonterminating operations, so the observable result is its array of runtime values. -/
@[expose]
def CreateDecl.evalResults :
    CreateDecl OpCode → SemanticAssignment → Option (Array RuntimeValue)
  | .operation opCode operands resultTypeHandles propertyHandle _ _, assignment => do
      let values ← assignment.getValues operands
      let resultTypes ← assignment.getTypes resultTypeHandles
      let property ← assignment.getProperty propertyHandle
      match interpretOp' opCode property resultTypes values #[] .empty with
      | .ok (results, _, none) => some results
      | _ => none
  | _, _ => none

/-- Semantically execute one creation declaration and bind all of its outputs. -/
@[expose]
def CreateDecl.eval (decl : CreateDecl OpCode)
    (assignment : SemanticAssignment) : Option SemanticAssignment :=
  match decl with
  | .type value result =>
      some (assignment.bindType result value)
  | .property _ value result =>
      some (assignment.bindProperty result value)
  | .operation _ _ _ _ opHandle resultHandles => do
      let results ← decl.evalResults assignment
      pure ((assignment.bindOp opHandle results).bindValues
        resultHandles.toList results.toList)

/-- Semantically execute creation declarations in program order. -/
@[expose]
def CreateProg.evalDecls (decls : List (CreateDecl OpCode))
    (assignment : SemanticAssignment) : Option SemanticAssignment :=
  match decls with
  | [] => some assignment
  | decl :: decls => do
      let assignment ← decl.eval assignment
      CreateProg.evalDecls decls assignment

/-- Run the semantic creation phase and pass its final assignment to the terminal obligation.
Failure is invalid: this is the user-facing proof that all created operations interpret
successfully for the runtime values admitted by the matcher. -/
@[expose]
def CreateProg.denote (prog : CreateProg OpCode α) (assignment : SemanticAssignment)
    (next : SemanticAssignment → Prop) : Prop :=
  match CreateProg.evalDecls prog.decls assignment with
  | some final => next final
  | none => False

/-!
## Pattern Validity

`Pattern.Valid` is the predicate that a Puddle pattern is both sound structurally and
semantically.  If `Pattern.Valid` holds, then compiling the Puddle pattern to
with `Pattern.compile` should produce a rewrite pattern that satisfies `LocalRewritePattern.Valid`.
-/

/-- The denotational proposition derived from a rule's matcher and replacement.

No operational preservation proof is stored here. Pattern authors prove only this algebraic
obligation; the generic compiler theorem derives `PreservesSemantics`. -/
structure Pattern.Valid (rule : Pattern OpCode) : Prop where
  /-- Every operation declaration in the pattern uses a supported opcode. -/
  Supported : rule.Supported
  /-- The match program starts with an operation declaration constraining its root handle. -/
  ConstrainsRoot : rule.matcher.ConstrainsRoot
  structurallyWellFormed : rule.StructurallyWellFormed
  refines :
    ∀ assignment, rule.matcher.Models assignment →
      rule.creation.denote assignment fun final =>
        rule.replacement.refinesRoot rule.matcher.rootHandle assignment final
end

end Veir.Puddle
