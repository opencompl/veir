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
both structurally and semantically. If `Pattern.Valid` holds, then compiling the Puddle pattern
with `Pattern.compile` should produce a rewrite pattern that satisfies `LocalRewritePattern.Valid`.
-/

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-!
## Supported Opcodes

Puddle currently only supports operations that cannot terminate a block and have no memory effects.
-/

/--
An opcode is supported when it is not a terminator and has no memory effects for any possible
property value.

We could in the future support opcodes when we know that the properties matched or created by the
pattern are such that the operation has no memory effects, but this is only happening in rare cases.
-/
@[expose]
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

/-! ## Root Constraint -/

/--
The first declaration in the match program is an operation declaration whose operation handle is
the program's distinguished root handle.
-/
@[expose]
def MatchProg.ConstrainsRoot (prog : MatchProg OpInfo α) : Prop :=
  match prog.decls with
  | .operation _ _ _ _ _ opHandle _ _ :: _ => opHandle = prog.rootHandle
  | _ => False

/--
Return the hidden SSA-result handles from the program's root constraint.

The root is assumed to be the first declaration in the match program. If it is not, then this
function returns `none`.
-/
@[expose]
def MatchProg.rootResults? (prog : MatchProg OpCode α) :
    Option (Array (Handle OpCode .value)) :=
  match prog.decls with
  | .operation _ _ _ _ _ opHandle results _ :: _ =>
    if opHandle = prog.rootHandle then some results else none
  | _ => none

/-!
## Structural well-formedness

This section defines `Pattern.StructurallyWellFormed`, the obligations of a Puddle pattern to be
considered structurally well-formed, and therefore structurally valid. While `Builders` ensure that
the pattern is well-formed, it is still possible to construct a pattern that is not well-formed by
using the underlying `MatchProg` and `CreateProg` constructors directly.
-/

/--
The abstract context of handle identifiers and their runtime kinds.

This context is used to record the handles that have been bound by the matcher and creation phase,
to check at each step if the inputs are available, and if the output is fresh, or was declared with
the same kind.
-/
structure HandleContext where
  /- The bindings ids that have been established, with their kinds. -/
  bindings : List (Nat × HandleType OpCode)
  /-
  The bindings that have been established, but that are not allowed to be used.
  This is used to mark the root and its results as unavailable to the creation phase and
  replacement phase, even though they are still bound by the matcher.
  -/
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
def require (ctx : HandleContext) (handle : Handle OpCode kind) : Bool :=
  ctx.lookup handle.id = some kind ∧ handle.id ∉ ctx.unavailable

/-- Require every handle in a homogeneous list to be available. -/
@[expose]
def requireMany (ctx : HandleContext) (handles : List (Handle OpCode kind)) : Bool :=
  handles.all ctx.require

/--
Record a matcher-defined handle. Repeated definitions of the same typed handle are permitted,
but reusing an identifier at another kind is rejected.
-/
@[expose]
def insert (ctx : HandleContext) (handle : Handle OpCode kind) : Option HandleContext :=
  match ctx.lookup handle.id with
  | none => some ⟨(handle.id, kind) :: ctx.bindings, ctx.unavailable⟩
  | some actual => if actual = kind then some ctx else none

/-- Record several matcher-defined handles. -/
@[expose]
def insertMany (ctx : HandleContext) (handles : List (Handle OpCode kind))
    : Option HandleContext :=
  handles.foldlM insert ctx

/-- Record a creation output, requiring its identifier to be fresh in the context. -/
@[expose]
def insertFresh (ctx : HandleContext) (handle : Handle OpCode kind) : Option HandleContext :=
  match ctx.lookup handle.id with
  | none => some ⟨(handle.id, kind) :: ctx.bindings, ctx.unavailable⟩
  | some _ => none

/-- Record several creation outputs, checking freshness between the outputs as well. -/
@[expose]
def insertManyFresh (ctx : HandleContext) (handles : List (Handle OpCode kind))
    : Option HandleContext :=
  handles.foldlM insertFresh ctx

/-- Mark an allocated handle as unavailable to creation and replacement inputs. -/
@[expose]
def forbid (ctx : HandleContext) (handle : Handle OpCode kind) : HandleContext :=
  ⟨ctx.bindings, handle.id :: ctx.unavailable⟩

/-- Mark several allocated handles as unavailable while retaining them for freshness checks. -/
@[expose]
def forbidMany (ctx : HandleContext) (handles : List (Handle OpCode kind)) : HandleContext :=
  handles.foldl forbid ctx

end HandleContext

namespace MetadataTuple.Shape

/-- Require every handle described by a metadata tuple shape to be available. -/
@[expose]
def requireBindings (shape : MetadataTuple.Shape OpCode Handles) (ctx : HandleContext)
    (handles : Handles) : Bool :=
  match shape with
  | .unit => true
  | .atom .type => ctx.require handles
  | .atom (.property _) => ctx.require handles
  | .cons .type tail => ctx.require handles.1 && tail.requireBindings ctx handles.2
  | .cons (.property _) tail => ctx.require handles.1 && tail.requireBindings ctx handles.2

/-- Insert every handle described by a metadata tuple shape, requiring each one to be fresh. -/
@[expose]
def insertFreshBindings (shape : MetadataTuple.Shape OpCode Handles) (ctx : HandleContext)
    (handles : Handles) : Option HandleContext :=
  match shape with
  | .unit => some ctx
  | .atom .type => ctx.insertFresh handles
  | .atom (.property _) => ctx.insertFresh handles
  | .cons .type tail => do
      let ctx ← ctx.insertFresh handles.1
      tail.insertFreshBindings ctx handles.2
  | .cons (.property _) tail => do
      let ctx ← ctx.insertFresh handles.1
      tail.insertFreshBindings ctx handles.2

end MetadataTuple.Shape
/-- Collect the handles that a matcher declaration binds during a successful match. -/
@[expose]
def MatchDecl.collectBindings (decl : MatchDecl OpCode)
    (defined : HandleContext) : Option HandleContext := do
  match decl with
  | .operation _ operands resultTypes _ propertyHandle opHandle results _ =>
      /-
      An operation discovered through the root operation handle, or through one of its result
      handles, is the root again.  Propagate that unavailability to every alias introduced by this
      declaration.  This is needed because matcher handles are not required to be injective: a
      later operation declaration may rediscover the root under a fresh operation/result handle.
      -/
      let rootAlias := opHandle.id ∈ defined.unavailable ∨
        ∃ result ∈ results.toList, result.id ∈ defined.unavailable
      let defined ← defined.insert opHandle
      let defined ← defined.insertMany results.toList
      let defined ← defined.insert propertyHandle
      let defined ← defined.insertMany resultTypes.toList
      let defined ← defined.insertMany operands.toList
      if rootAlias then
        some ((defined.forbid opHandle).forbidMany results.toList)
      else
        some defined
  | .value typeHandle _ =>
      defined.insert typeHandle
  | .type _ _ =>
      some defined
  | @MatchDecl.applyNative _ _ _ inputBundle inputs _ => do
      guard (inputBundle.shape.requireBindings defined inputs)
      return defined

/--
Collect all the handles that a list of matcher declarations bind during a successful match.
In particular, this includes the root result handles.
-/
@[expose]
def MatchProg.collectDeclBindings :
    List (MatchDecl OpCode) → HandleContext → Option HandleContext
  | [], defined => some defined
  | decl :: decls, defined => do
      let defined ← decl.collectBindings defined
      MatchProg.collectDeclBindings decls defined

/--
Collect every available handle that can be bound by a successful matcher, and mark as unavailable
the root operation handle and its result handles.
-/
@[expose]
def MatchProg.collectBindings (prog : MatchProg OpCode α) : Option HandleContext :=
  do
    let _rootResults ← prog.rootResults?
    let defined ← HandleContext.empty.insert prog.rootHandle
    let defined := defined.forbid prog.rootHandle
    let defined ← MatchProg.collectDeclBindings prog.decls defined
    return defined

/--
Check one creation declaration and extend the context with its outputs. Inputs must be available at
this exact program point, while all outputs must have globally fresh identifiers.
-/
@[expose]
def CreateDecl.checkBindings (ctx : HandleContext) (decl : CreateDecl OpCode)
    : Option HandleContext := do
  match decl with
  | .type _ result =>
      ctx.insertFresh result
  | .property _ _ result =>
      ctx.insertFresh result
  | .operation _ operands resultTypes properties opHandle resultHandles =>
      guard (ctx.requireMany operands.toList)
      guard (ctx.requireMany resultTypes.toList)
      guard (ctx.require properties)
      guard (resultHandles.size = resultTypes.size)
      let defined ← ctx.insertFresh opHandle
      defined.insertManyFresh resultHandles.toList
  | @CreateDecl.applyNative _ _ _ _ inputBundle outputBundle inputs _ outputs => do
      guard (inputBundle.shape.requireBindings ctx inputs)
      outputBundle.shape.insertFreshBindings ctx outputs

@[expose]
def CreateProg.checkBindingsDecls :
    List (CreateDecl OpCode) → HandleContext → Option HandleContext
  | [], ctx => some ctx
  | decl :: decls, ctx => do
      let ctx ← decl.checkBindings ctx
      checkBindingsDecls decls ctx

/-- Validate a creation program from a matcher-defined handle context. -/
@[expose]
def CreateProg.checkBindings (ctx : HandleContext) (prog : CreateProg OpCode α)
    : Option HandleContext :=
  checkBindingsDecls prog.decls ctx

/-- Require every replacement value to be available after the creation program. -/
@[expose]
def Replacement.checkBindings (replacement : Replacement OpCode)
    (ctx : HandleContext) : Bool :=
  ctx.requireMany replacement.values.toList

/-- Run the complete structural checker on a pattern. -/
@[expose]
def Pattern.checkStructure (rule : Pattern OpCode) : Option HandleContext := do
  let defined ← rule.matcher.collectBindings
  let defined ← rule.creation.checkBindings defined
  guard (rule.replacement.checkBindings defined)
  return defined

/--
Structural validity of a Puddle pattern. It checks that:
* the match program begins with an operation declaration for its root;
* matcher bindings that share an identifier also share a runtime kind;
* every creation input is bound by the matcher or by an earlier creation declaration;
* every creation output has an identifier that is globally fresh;
* each created operation has as many result handles as result-type handles;
* every replacement value is bound by the matcher or the creation program; and
* the matched root and its results are not available to the creation or replacement phases.
-/
@[expose]
def Pattern.StructurallyWellFormed (rule : Pattern OpCode) : Prop :=
  rule.checkStructure.isSome = true

instance (rule : Pattern OpCode) : Decidable rule.StructurallyWellFormed := by
  unfold Pattern.StructurallyWellFormed
  infer_instance

/-!
## Semantic validity

This section defines `Pattern.PreservesSemantics`, the condition a Puddle pattern must satisfy to
ensure that applying it does not change the program’s semantics.

Concretely, we assign for each handle a semantic binding, which represents a possible runtime value
associated to a handle. The proof of correctness of a Puddle pattern is that for every possible
assignment that satisfies the matcher, the creation program produces a valid assignment that
refines the root operation's results.
-/

/-- The denotation of a handle for a particular program execution. -/
inductive SemanticBinding where
| op (results : Array RuntimeValue)
| value (value : RuntimeValue)
| type (type : TypeAttr)
| property (opCode : OpCode) (value : propertiesOf opCode)

/-- An assignment from handle identifiers to semantic values. -/
abbrev SemanticAssignment := Array (Option SemanticBinding)

/-- An empty assignment with a preallocated size. -/
@[expose]
def SemanticAssignment.empty (size : Nat) : SemanticAssignment :=
  Array.replicate size none

/-- Binds a value to a handle, possibly erasing the existing binding. -/
@[expose]
def SemanticAssignment.bind (assignment : SemanticAssignment)
    (id : Nat) (binding : SemanticBinding) : SemanticAssignment :=
  if h : id < assignment.size then
    assignment.set id (some binding)
  else
    /- Extend the array if necessary. -/
    assignment ++ Array.replicate (id - assignment.size) none ++ #[some binding]

/-- Binds an operation results to an operation handle. -/
@[expose]
def SemanticAssignment.bindOp (assignment : SemanticAssignment)
    (handle : Handle OpCode .op) (results : Array RuntimeValue) : SemanticAssignment :=
  assignment.bind handle.id (.op results)

/-- Binds a runtime value to a value handle. -/
@[expose]
def SemanticAssignment.bindValue (assignment : SemanticAssignment)
    (handle : Handle OpCode .value) (value : RuntimeValue) : SemanticAssignment :=
  assignment.bind handle.id (.value value)

/-- Binds a concrete type to a type handle. -/
@[expose]
def SemanticAssignment.bindType (assignment : SemanticAssignment)
    (handle : Handle OpCode .type) (type : TypeAttr) : SemanticAssignment :=
  assignment.bind handle.id (.type type)

/-- Binds a property to a property handle. -/
@[expose]
def SemanticAssignment.bindProperty (assignment : SemanticAssignment)
    (handle : Handle OpCode (.prop opCode)) (value : propertiesOf opCode) : SemanticAssignment :=
  assignment.bind handle.id (.property opCode value)

/-- Binds multiple values to multiple value handles. -/
@[expose]
def SemanticAssignment.bindValues (assignment : SemanticAssignment)
    (handles : List (Handle OpCode .value)) (values : List RuntimeValue) : SemanticAssignment :=
  match handles, values with
  | handle :: handles, value :: values =>
    (assignment.bindValue handle value).bindValues handles values
  | _, _ => assignment

/-- Get the binding of an operation handle. -/
@[expose]
def SemanticAssignment.getOp (assignment : SemanticAssignment)
    (handle : Handle OpCode .op) : Option (Array RuntimeValue) :=
  match assignment[handle.id]? with
  | some (some (.op results)) => some results
  | _ => none

/-- Get the binding of a value handle. -/
@[expose]
def SemanticAssignment.getValue (assignment : SemanticAssignment)
    (handle : Handle OpCode .value) : Option RuntimeValue :=
  match assignment[handle.id]? with
  | some (some (.value value)) => some value
  | _ => none

/-- Get the binding of a type handle. -/
@[expose]
def SemanticAssignment.getType (assignment : SemanticAssignment)
    (handle : Handle OpCode .type) : Option TypeAttr :=
  match assignment[handle.id]? with
  | some (some (.type type)) => some type
  | _ => none

/-- Get the binding of a property handle. -/
@[expose]
def SemanticAssignment.getProperty (assignment : SemanticAssignment)
    (handle : Handle OpCode (.prop opCode)) : Option (propertiesOf opCode) :=
  match assignment[handle.id]? with
  | some (some (.property actualOpCode value)) =>
    if h : actualOpCode = opCode then
      some (h ▸ value)
    else none
  | _ => none

/-- Get the bindings of multiple value handles. -/
@[expose]
def SemanticAssignment.getValues (assignment : SemanticAssignment)
    (handles : Array (Handle OpCode .value)) : Option (Array RuntimeValue) :=
  handles.mapM assignment.getValue

/-- Get the bindings of multiple type handles. -/
@[expose]
def SemanticAssignment.getTypes (assignment : SemanticAssignment)
    (handles : Array (Handle OpCode .type)) : Option (Array TypeAttr) :=
  handles.mapM assignment.getType

namespace MetadataTuple.Atom

/-- Resolve a metadata atom's handle against a semantic assignment. -/
@[expose]
def resolveSemantic {HandleRep : Type} :
    (metadataAtom : MetadataTuple.Atom OpCode HandleRep) →
      SemanticAssignment → HandleRep → Option metadataAtom.Value
| .type, assignment, handle => assignment.getType handle
| .property _, assignment, handle => assignment.getProperty handle

/-- Bind a metadata atom's handle in a semantic assignment. -/
@[expose]
def bindSemantic {HandleRep : Type} :
    (metadataAtom : MetadataTuple.Atom OpCode HandleRep) →
      SemanticAssignment → HandleRep → metadataAtom.Value → Option SemanticAssignment
| .type, assignment, handle, value => some (assignment.bindType handle value)
| .property _, assignment, handle, value => some (assignment.bindProperty handle value)

end MetadataTuple.Atom

namespace MetadataTuple.Shape

/-- Resolve every handle in a metadata-tuple shape against a semantic assignment. -/
@[expose]
def resolveSemantic : (shape : MetadataTuple.Shape OpCode Handles) →
    SemanticAssignment → Handles → Option shape.Values
| .unit, _, _ => some ()
| .atom metadataAtom, assignment, handle => metadataAtom.resolveSemantic assignment handle
| .cons head tail, assignment, handles => do
    let headValue ← head.resolveSemantic assignment handles.1
    let tailValues ← tail.resolveSemantic assignment handles.2
    return (headValue, tailValues)

/-- Bind every handle in a metadata-tuple shape in a semantic assignment. -/
@[expose]
def bindSemantic : (shape : MetadataTuple.Shape OpCode Handles) →
    SemanticAssignment → Handles → shape.Values → Option SemanticAssignment
| .unit, assignment, _, _ => some assignment
| .atom metadataAtom, assignment, handle, value =>
    metadataAtom.bindSemantic assignment handle value
| .cons head tail, assignment, handles, values => do
    let assignment ← head.bindSemantic assignment handles.1 values.1
    tail.bindSemantic assignment handles.2 values.2

end MetadataTuple.Shape

namespace MetadataTuple

/-- Resolve all handles in a metadata tuple against a semantic assignment. -/
@[expose]
def resolveSemantic {Handles : Type} [self : IsMetadataTuple OpCode Handles]
    (assignment : SemanticAssignment) (handles : Handles) :
    Option (MetadataValues OpCode Handles) :=
  self.shape.resolveSemantic assignment handles

/-- Bind all handles in a metadata tuple in a semantic assignment. -/
@[expose]
def bindSemantic {Handles : Type} [self : IsMetadataTuple OpCode Handles]
    (assignment : SemanticAssignment) (handles : Handles) (values : MetadataValues OpCode Handles) :
    Option SemanticAssignment :=
  self.shape.bindSemantic assignment handles values

end MetadataTuple

/--
Interpreter-based denotation of an operation on a set of operands and properties, for operations
without regions or successors.
-/
@[expose]
def InterpretsTo (opCode : OpCode) (actual : propertiesOf opCode)
    (resultTypes : Array TypeAttr) (operands results : Array RuntimeValue) : Prop :=
  ∀ memory, interpretOp' opCode actual resultTypes operands #[] memory = .ok (results, memory, none)

/-- A semantic assignment satisfies the constraints of a matcher declaration. -/
@[expose]
def MatchDecl.Models (decl : MatchDecl OpCode) (assignment : SemanticAssignment) : Prop :=
  match decl with
  | .type matcher handle =>
    ∃ type, assignment.getType handle = some type ∧ matcher type = true
  | .value typeHandle handle =>
    ∃ type value,
      assignment.getType typeHandle = some type ∧
      assignment.getValue handle = some value ∧
      value.Conforms type
  | .operation opCode operandHandles returnTypeHandles property propertyHandle handle resultHandles _ =>
    ∃ operands resultTypes results actualProperty,
      assignment.getValues operandHandles = some operands ∧
      assignment.getTypes returnTypeHandles = some resultTypes ∧
      assignment.getOp handle = some results ∧
      assignment.getProperty propertyHandle = some actualProperty ∧
      assignment.getValues resultHandles = some results ∧
      property actualProperty = true ∧
      InterpretsTo opCode actualProperty resultTypes operands results
  | @MatchDecl.applyNative _ _ _ inputBundle inputs predicate =>
    ∃ values,
      MetadataTuple.resolveSemantic (self := inputBundle) assignment inputs = some values ∧
      predicate values = true

/-- Pointwise semantic facts for every matcher declaration. -/
@[expose]
def MatchProg.Models (prog : MatchProg OpCode α) (assignment : SemanticAssignment) : Prop :=
  ∀ decl ∈ prog.decls, decl.Models assignment

/--
The runtime value of the replacement values refine the runtime value of the matched root operation
results.
-/
@[expose]
def Replacement.refinesRoot (replacement : Replacement OpCode) (root : Handle OpCode .op)
    (matched final : SemanticAssignment) : Prop :=
  match matched.getOp root, final.getValues replacement.values with
  | some rootResults, some replacementValues => rootResults ⊒ replacementValues
  | _, _ => False

/-- Semantically execute one creation declaration and bind all of its outputs. -/
@[expose]
def CreateDecl.eval (assignment : SemanticAssignment) (decl : CreateDecl OpCode)
     : Option SemanticAssignment :=
  match decl with
  | .type value result =>
      some (assignment.bindType result value)
  | .property _ value result =>
      some (assignment.bindProperty result value)
  | .operation opCode operands resultTypeHandles propertyHandle opHandle resultHandles => do
      let values ← assignment.getValues operands
      let resultTypes ← assignment.getTypes resultTypeHandles
      let property ← assignment.getProperty propertyHandle
      let results ←
        match interpretOp' opCode property resultTypes values #[] .empty with
        | .ok (results, _, none) => some results
        | _ => none
      pure ((assignment.bindOp opHandle results).bindValues
        resultHandles.toList results.toList)
  | @CreateDecl.applyNative _ _ _ _ inputBundle outputBundle inputs rewrite outputs => do
      let inputValues ← MetadataTuple.resolveSemantic (self := inputBundle) assignment inputs
      let outputValues ← rewrite inputValues
      MetadataTuple.bindSemantic (self := outputBundle) assignment outputs outputValues

/-- Semantically execute creation declarations in program order. -/
@[expose]
def CreateProg.evalDecls (decls : List (CreateDecl OpCode)) (assignment : SemanticAssignment)
    : Option SemanticAssignment :=
  decls.foldlM CreateDecl.eval assignment

/-- The semantic preservation property of a pattern. -/
@[expose]
def Pattern.PreservesSemantics (rule : Pattern OpCode) : Prop :=
  ∀ assignment, rule.matcher.Models assignment →
    ∃ final, CreateProg.evalDecls rule.creation.decls assignment = some final ∧
      rule.replacement.refinesRoot rule.matcher.rootHandle assignment final

/-!
## Pattern Validity

`Pattern.Valid` is the predicate that a Puddle pattern is both sound structurally and
semantically.  If `Pattern.Valid` holds, then compiling the Puddle pattern
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
  /-- Structural validity of the pattern. -/
  structurallyWellFormed : rule.StructurallyWellFormed
  /-- Semantic validity of the pattern. -/
  refines : rule.PreservesSemantics
end

/-!
## Validity Tactics

This section defines tactics for proving the different obligations of `Pattern.Valid`. These tactics
are intended to be used in the proof of `Pattern.Valid` for a specific Puddle pattern.
-/

/-- Unfold and simplify the builders used to construct a concrete Puddle pattern. -/
macro "unfoldPuddleBuilder" : tactic =>
  `(tactic| (
    /- Unfold the builder functions -/
    simp only [Pattern.Builder, MatchProg.build, CreateProg.build, bind, pure,
      MatchProg.value, MatchProg.type, MatchProg.root, MatchProg.operation, MatchProg.matchNative,
      CreateProg.operation, CreateProg.property, CreateProg.applyNative, MetadataTuple.fresh,
      MetadataTuple.Shape.fresh, MetadataTuple.Atom.fresh,
      /- Simplify the resulting expressions with standard simplifications -/
      Nat.zero_add, Nat.reduceAdd, List.size_toArray, List.length_cons, List.length_nil,
      Array.size_map, Array.size_range, Nat.lt_add_one, getElem!_pos, Array.getElem_map,
      Array.getElem_range, Nat.add_zero, List.cons_append, List.nil_append, List.reverse_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]))

/-- Prove a `Puddle.Supported` goal. -/
macro "provePuddleSupported" : tactic =>
  `(tactic| (
    simp [Pattern.Supported, CreateProg.Supported, MatchProg.Supported, MatchDecl.Supported,
      CreateDecl.Supported, SupportedOpCode, get_effects, is_terminator];
    done
  ))

/-- Prove a `Puddle.Valid` goal. -/
macro "provePuddleValid" : tactic =>
  `(tactic| (
    unfoldPuddleBuilder
    constructor
    · provePuddleSupported
    · cbv
    · cbv
  ))

end Veir.Puddle
