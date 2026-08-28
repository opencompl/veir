module

public import Veir.PatternRewriter.Puddle.Builders
public import Veir.Interpreter.Refinement.Lemmas

/-!
# Puddle Validity and Proof Automation

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

/-- Record an output, requiring its identifier to be fresh in the context. -/
def insertFresh (ctx : HandleContext) (handle : Handle OpCode kind) : Option HandleContext :=
  match ctx.lookup handle.id with
  | none => some ⟨(handle.id, kind) :: ctx.bindings, ctx.unavailable⟩
  | some _ => none

/-- Record several outputs, checking freshness between the outputs as well. -/
@[expose]
def insertManyFresh (ctx : HandleContext) (handles : List (Handle OpCode kind))
    : Option HandleContext :=
  handles.foldlM insertFresh ctx

/-- Mark an allocated handle as unavailable to creation and replacement inputs. -/
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

/--
Collect the handles that a matcher declaration binds during a successful match.
Requires that all inputs are available in the context, and that all outputs are fresh.
-/
@[expose]
def MatchDecl.collectBindings (decl : MatchDecl OpCode)
    (defined : HandleContext) : Option HandleContext := do
  match decl with
  | .operation _ operands resultTypes _ propertyHandle opHandle results _ =>
      guard (defined.requireMany operands.toList)
      guard (defined.requireMany resultTypes.toList)
      let defined ← defined.insertManyFresh results.toList
      let defined ← defined.insertFresh propertyHandle
      defined.insertFresh opHandle
  | .value typeHandle result =>
      guard (defined.require typeHandle)
      defined.insertFresh result
  | .type _ result =>
      defined.insertFresh result
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

/-- Order the matching declarations from leaves to root, then native guards. -/
@[expose]
def MatchProg.bindingDecls (prog : MatchProg OpInfo α) : List (MatchDecl OpInfo) :=
  let (structural, guards) := prog.decls.partition fun
    | @MatchDecl.applyNative _ _ _ _ _ _ => false
    | _ => true
  structural.reverse ++ guards

/--
Collect every available handle that can be bound by a successful matcher, and mark as unavailable
the root operation handle and its result handles.
-/
@[expose]
def MatchProg.collectBindings (prog : MatchProg OpCode α) : Option HandleContext :=
  do
    let rootResults ← prog.rootResults?
    let defined ← MatchProg.collectDeclBindings prog.bindingDecls .empty
    let defined := defined.forbid prog.rootHandle
    return defined.forbidMany rootResults.toList

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

/-- Validate a creation program from a matcher-defined handle context. -/
@[expose]
def CreateProg.checkBindings (ctx : HandleContext) (prog : CreateProg OpCode α)
    : Option HandleContext :=
  prog.decls.foldlM CreateDecl.checkBindings ctx

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
* the match program executes an operation declaration for its root first;
* when the declarations are processed in reverse order, inputs are introduced before
  use and outputs are fresh
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

This section defines the semantic obligation `Pattern.PreservesSemantics` for Puddle patterns.

We assign runtime values to SSA value handles and concrete metadata to type and property handles.
Operation handles remain structural: their results are represented by the individual SSA value
handles. The semantic obligation is that for every assignment satisfying the matcher, the creation
program produces an assignment that refines the root operation's results.
-/

/-- The denotation of a value or metadata handle for a particular program execution. -/
inductive SemanticBinding where
| value (value : RuntimeValue)
| type (type : TypeAttr)
| property (opCode : OpCode) (value : propertiesOf opCode)

/-- An assignment from handle identifiers to semantic values. -/
abbrev SemanticAssignment := Nat → Option SemanticBinding

/-- The empty assignment. -/
@[expose]
def SemanticAssignment.empty : SemanticAssignment :=
  fun _ => none

/-- Binds a value to a handle, possibly erasing the existing binding. -/
@[expose]
def SemanticAssignment.bind (assignment : SemanticAssignment)
    (id : Nat) (binding : SemanticBinding) : SemanticAssignment :=
  fun queried => if queried = id then some binding else assignment queried

@[simp]
theorem SemanticAssignment.empty_apply (id : Nat) :
    SemanticAssignment.empty id = none := rfl

@[simp]
theorem SemanticAssignment.bind_same_eq (assignment : SemanticAssignment)
    (id : Nat) (binding : SemanticBinding) :
    assignment.bind id binding id = some binding := by
  simp [SemanticAssignment.bind]

@[simp]
theorem SemanticAssignment.bind_of_ne_eq (assignment : SemanticAssignment)
    (id queried : Nat) (binding : SemanticBinding) (hne : queried ≠ id) :
    assignment.bind id binding queried = assignment queried := by
  simp [SemanticAssignment.bind, hne]

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

/-- Get the binding of a value handle. -/
@[expose]
def SemanticAssignment.getValue (assignment : SemanticAssignment)
    (handle : Handle OpCode .value) : Option RuntimeValue :=
  match assignment handle.id with
  | some (.value value) => some value
  | _ => none

/--
Get the binding of a type handle.
If the handle is unbound or bound with a different type, return none.
-/
@[expose]
def SemanticAssignment.getType (assignment : SemanticAssignment)
    (handle : Handle OpCode .type) : Option TypeAttr :=
  match assignment handle.id with
  | some (.type type) => some type
  | _ => none

/--
Get the binding of a property handle.
If the handle is unbound or bound with a different property, return none.
-/
@[expose]
def SemanticAssignment.getProperty (assignment : SemanticAssignment)
    (handle : Handle OpCode (.prop opCode)) : Option (propertiesOf opCode) :=
  match assignment handle.id with
  | some (.property actualOpCode value) =>
    if h : actualOpCode = opCode then
      some (h ▸ value)
    else none
  | _ => none

/--
Get the bindings of multiple value handles.
If any handle is unbound or bound with a different kind, return none.
-/
@[expose]
def SemanticAssignment.getValues (assignment : SemanticAssignment)
    (handles : List (Handle OpCode .value)) : Option (List RuntimeValue) :=
  handles.mapM assignment.getValue

/--
Get the bindings of multiple type handles.
If any handle is unbound or bound with a different kind, return none.
-/
@[expose]
def SemanticAssignment.getTypes (assignment : SemanticAssignment)
    (handles : List (Handle OpCode .type)) : Option (List TypeAttr) :=
  handles.mapM assignment.getType

namespace MetadataTuple.Atom

/-- Resolve a metadata atom's handle against a semantic assignment. -/
@[expose]
def resolveSemantic (assignment : SemanticAssignment) (handle : HandleRep)
    (atom : MetadataTuple.Atom OpCode HandleRep) : Option atom.Value :=
  match atom with
  | .type => assignment.getType handle
  | .property _ => assignment.getProperty handle

/-- Bind a metadata atom's handle in a semantic assignment. -/
@[expose]
def bindSemantic (assignment : SemanticAssignment) (handle : HandleRep)
  (atom : MetadataTuple.Atom OpCode HandleRep) (value : atom.Value) : SemanticAssignment :=
  match atom with
  | .type => assignment.bindType handle value
  | .property _ => assignment.bindProperty handle value

end MetadataTuple.Atom

namespace MetadataTuple.Shape

/-- Resolve every handle in a metadata-tuple shape against a semantic assignment. -/
@[expose]
def resolveSemantic (assignment : SemanticAssignment)
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles) : Option shape.Values :=
  match shape with
  | .unit => some ()
  | .atom metadataAtom => metadataAtom.resolveSemantic assignment handles
  | .cons head tail => do
    let headValue ← head.resolveSemantic assignment handles.1
    let tailValues ← tail.resolveSemantic assignment handles.2
    return (headValue, tailValues)

/-- Bind every handle in a metadata-tuple shape in a semantic assignment. -/
@[expose]
def bindSemantic (assignment : SemanticAssignment)
    (shape : MetadataTuple.Shape OpCode Handles) (handles : Handles) (values : shape.Values)
    : SemanticAssignment :=
  match shape with
  | .unit => assignment
  | .atom metadataAtom => metadataAtom.bindSemantic assignment handles values
  | .cons head tail =>
    let assignment := head.bindSemantic assignment handles.1 values.1
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
    SemanticAssignment :=
  self.shape.bindSemantic assignment handles values

end MetadataTuple

/-- The interpretation of a pure operation succeeds with the given results of given types. -/
@[expose]
def InterpretsTo (opCode : OpCode) (actual : propertiesOf opCode)
    (resultTypes : Array TypeAttr) (operands results : Array RuntimeValue) : Prop :=
  RuntimeValue.ArrayConforms results resultTypes ∧
    ∀ memory, interpretOp' opCode actual resultTypes operands #[] memory = .ok (results, memory, none)

/-!
### Matcher semantics

This section defines the semantics of a matching program. The semantics are defined in terms of
propositions over `SemanticAssignment`. The semantics are written in continuation-passing style
so that each generated value remains in scope both in the updated assignment and in the final
proposition.
-/

/--
Universally bind one runtime value for every handle, in handle order.
Then, call the continuation with the list of values and the updated assignment.
-/
@[expose]
def SemanticAssignment.forallValues (assignment : SemanticAssignment)
    (handles : List (Handle OpCode .value))
    (continuation : List RuntimeValue → SemanticAssignment → Prop) : Prop :=
  match handles with
  | [] => continuation [] assignment
  | handle :: handles =>
      ∀ value, SemanticAssignment.forallValues (assignment.bindValue handle value) handles
        fun values assignment => continuation (value :: values) assignment

/--
Collect the constraints of a matching declaration on the given assignment,
and call the continuation with the updated assignment.
-/
@[expose]
def MatchDecl.Models (decl : MatchDecl OpCode) (assignment : SemanticAssignment)
    (continuation : SemanticAssignment → Prop) : Prop :=
  match decl with
  | .type matcher handle =>
    ∀ type, matcher type → continuation (assignment.bindType handle type)
  | .value typeHandle handle =>
    match assignment.getType typeHandle with
    | some ty => ∀ value, value.Conforms ty → continuation (assignment.bindValue handle value)
    | none => False
  | .operation opCode operandHandles resultTypeHandles propertyMatcher propertyHandle _
      resultHandles _ =>
    match assignment.getValues operandHandles.toList,
      assignment.getTypes resultTypeHandles.toList with
    | some operands, some resultTypes =>
      ∀ property, assignment.forallValues resultHandles.toList fun results assignment =>
        propertyMatcher property = true →
        InterpretsTo opCode property resultTypes.toArray operands.toArray results.toArray →
        continuation (assignment.bindProperty propertyHandle property)
      | _, _ => False
  | @MatchDecl.applyNative _ _ _ inputBundle inputs predicate =>
    match MetadataTuple.resolveSemantic (self := inputBundle) assignment inputs with
    | some values => predicate values = true → continuation assignment
    | none => False

/-- Generates matcher semantics for the given declarations, then call the continuation. -/
@[expose]
def MatchProg.modelsDecls (decls : List (MatchDecl OpCode)) (assignment : SemanticAssignment)
    (continuation : SemanticAssignment → Prop) : Prop :=
  match decls with
  | [] => continuation assignment
  | decl :: decls =>
      decl.Models assignment fun assignment =>
        MatchProg.modelsDecls decls assignment continuation

/-- Generate matcher semantics in binding order, then call the continuation. -/
@[expose]
def MatchProg.Models (prog : MatchProg OpCode α)
    (continuation : SemanticAssignment → Prop) : Prop :=
  MatchProg.modelsDecls prog.bindingDecls SemanticAssignment.empty continuation

/-!
### Creation semantics

This section defines the semantics of a creation program. The semantics are defined in terms of
propositions over `SemanticAssignment`. The semantics are written in continuation-passing style
so that each generated value remains in scope both in the updated assignment and in the final
proposition.
-/

/-- Existentially bind one runtime value for every handle, in handle order. -/
@[expose]
def SemanticAssignment.existsValues (assignment : SemanticAssignment)
    (handles : List (Handle OpCode .value))
    (continuation : List RuntimeValue → SemanticAssignment → Prop) : Prop :=
  match handles with
  | [] => continuation [] assignment
  | handle :: handles =>
      ∃ value, SemanticAssignment.existsValues (assignment.bindValue handle value) handles
        fun values assignment => continuation (value :: values) assignment

/--
Collect the constraints of a creation declaration on the given assignment,
and call the continuation with the updated assignment.
-/
@[expose]
def CreateDecl.Models (decl : CreateDecl OpCode) (assignment : SemanticAssignment)
    (continuation : SemanticAssignment → Prop) : Prop :=
  match decl with
  | .type value result =>
    continuation (assignment.bindType result value)
  | .property _ value result =>
    continuation (assignment.bindProperty result value)
  | .operation opCode operandHandles resultTypeHandles propertyHandle _ resultHandles =>
    match assignment.getValues operandHandles.toList,
      assignment.getTypes resultTypeHandles.toList, assignment.getProperty propertyHandle with
    | some operands, some resultTypes, some actualProperty =>
      assignment.existsValues resultHandles.toList fun results assignment =>
        InterpretsTo opCode actualProperty resultTypes.toArray operands.toArray results.toArray ∧
          continuation assignment
    | _, _, _ => False
  | @CreateDecl.applyNative _ _ _ _ inputBundle outputBundle inputs rewrite outputs =>
    match MetadataTuple.resolveSemantic (self := inputBundle) assignment inputs >>= rewrite with
    | none => False
    | some values =>
        continuation (MetadataTuple.bindSemantic (self := outputBundle) assignment outputs values)

/-- Generate creation semantics for the declaration list, then call the continuation. -/
@[expose]
def CreateProg.modelsDecls (decls : List (CreateDecl OpCode)) (assignment : SemanticAssignment)
    (continuation : SemanticAssignment → Prop) : Prop :=
  match decls with
  | [] => continuation assignment
  | decl :: decls =>
    decl.Models assignment fun assignment =>
      CreateProg.modelsDecls decls assignment continuation

/-- Generate creation semantics in execution order, then call the continuation. -/
@[expose]
def CreateProg.Models (prog : CreateProg OpCode α) (assignment : SemanticAssignment)
    (continuation : SemanticAssignment → Prop) : Prop :=
  CreateProg.modelsDecls prog.decls assignment continuation

/--
Check that the root results of the matcher assignment refine the replacement values
in the assignment after the creation phase.
-/
@[expose]
def Replacement.refinesRoot (replacement : Replacement OpCode)
    (rootResults : Option (Array (Handle OpCode .value)))
    (matched final : SemanticAssignment) : Prop :=
  match rootResults.bind (fun handles => matched.getValues handles.toList),
    final.getValues replacement.values.toList with
  | some rootValues, some replacementValues => rootValues.toArray ⊒ replacementValues.toArray
  | _, _ => False

/-- The semantic preservation property of a pattern. -/
@[expose]
def Pattern.PreservesSemantics (rule : Pattern OpCode) : Prop :=
  rule.matcher.Models fun matched =>
    rule.creation.Models matched fun final =>
      rule.replacement.refinesRoot rule.matcher.rootResults? matched final

/-!
## Pattern Validity

`Pattern.Valid` is the predicate that a Puddle pattern is both sound structurally and
semantically.  If `Pattern.Valid` holds, then compiling the Puddle pattern
with `Pattern.compile` should produce a rewrite pattern that satisfies `LocalRewritePattern.Valid`.
-/

/-- The static validity conditions required by a Puddle pattern. -/
structure Pattern.Valid (rule : Pattern OpCode) : Prop where
  /-- Every operation declaration in the pattern uses a supported opcode. -/
  Supported : rule.Supported
  /-- The first executed declaration constrains the match program's root handle. -/
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
      CreateProg.type, CreateProg.operation, CreateProg.property, CreateProg.applyNative,
      MetadataTuple.fresh,
      IsMetadataTuple.shape_unit, IsMetadataTuple.shape_type, IsMetadataTuple.shape_property,
      IsMetadataTuple.shape_type_cons, IsMetadataTuple.shape_property_cons,
      MetadataTuple.Shape.fresh, MetadataTuple.Atom.fresh,
      /- Simplify the resulting expressions with standard simplifications -/
      Nat.zero_add, Nat.reduceAdd, List.size_toArray, List.length_cons, List.length_nil,
      Array.size_map, Array.size_range, Nat.lt_add_one, getElem!_pos, Array.getElem_map,
      Array.getElem_range, Nat.add_zero, List.cons_append, List.nil_append,
      List.reverse_cons, List.reverse_nil]))

/-- Prove a `Puddle.Supported` goal. -/
macro "provePuddleSupported" : tactic =>
  `(tactic| (
    simp [Pattern.Supported, CreateProg.Supported, MatchProg.Supported, MatchDecl.Supported,
      CreateDecl.Supported, SupportedOpCode, get_effects, is_terminator];
    done
  ))

/-- Normalize semantic plumbing, leaving operation denotations and value conformance opaque. -/
macro "simpPuddleSemantics" : tactic =>
  `(tactic| simp [Pattern.PreservesSemantics, MatchProg.Models,
    MatchProg.bindingDecls, List.partition_eq_filter_filter, List.range_succ, List.reverse_cons,
    MatchProg.modelsDecls, MatchDecl.Models,
    CreateProg.Models, CreateProg.modelsDecls, CreateDecl.Models,
    SemanticAssignment.getValues, SemanticAssignment.getTypes,
    SemanticAssignment.getValue, SemanticAssignment.getType,
    SemanticAssignment.getProperty,
    SemanticAssignment.bindProperty, SemanticAssignment.bindType,
    SemanticAssignment.bindValue, SemanticAssignment.bind,
    SemanticAssignment.forallValues, SemanticAssignment.existsValues,
    MetadataTuple.resolveSemantic, MetadataTuple.Shape.resolveSemantic,
    MetadataTuple.Atom.resolveSemantic, MetadataTuple.bindSemantic,
    MetadataTuple.Shape.bindSemantic, MetadataTuple.Atom.bindSemantic,
    Replacement.refinesRoot, MatchProg.rootResults?])

/-- Discharge structural obligations and expose a pattern's assignment-free semantic proposition. -/
macro "provePuddleValid" : tactic =>
  `(tactic| (
    unfoldPuddleBuilder
    constructor
    · provePuddleSupported
    · cbv
    · cbv
    simpPuddleSemantics
  ))

end Veir.Puddle
