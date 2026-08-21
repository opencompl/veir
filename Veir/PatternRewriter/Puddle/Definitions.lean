module

public import Veir.GlobalOpInfo

/-!
# Puddle DSL

Puddle is a small, deeply embedded DSL for describing peephole rewrites. It describes a rooted graph
of operations to match, a sequence of operations to create, and a terminal replacement that
replaces the root's results before the matched root is erased.

The objective of Puddle is to describe rewrites in a way that makes it easier to prove their
semantic preservation. Proving `LocalRewritePattern.Sound` requires discharging dozens of
correctness conditions, so Puddle is designed to discharge most of them automatically or make them
hold by construction. Additionally, Puddle's declarative source makes it much easier to reason
about the semantic soundness of a rewrite than the imperative source of a `LocalRewritePattern`.

A Puddle pattern (`Pattern`) has three phases, in this order:

1. A `MatchProg` describes a rooted graph of operations. Authors build the graph bottom-up, starting
  with free values and types and ending with the root operation. The resulting program executes
  top-down from that root. Every matched operation must be reachable from the root and fully
  constrained: its operands, result types, and properties must be specified.
2. A `CreateProg` derives metadata and creates the operations that will replace the matched root.
  Operations are created in order and inserted before the root. They may consume non-root values
  matched in the first phase or values produced by earlier creation declarations.
3. A `Replacement` selects, in order, the values that replace the root's results before the root is
  erased.

Puddle patterns are not meant to be constructed directly. Instead, they are built with
`Pattern.Builder`, defined in `Veir.PatternRewriter.Puddle.Builders`.
-/

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-!
## Handles

Handles are typed symbolic references to operations, SSA values, types, and operation properties.
Their phantom `HandleType` prevents, for example, passing an operation handle where a value handle
is required. During execution handles are resolved to concrete IR entities; validity proofs instead
interpret them in the semantic model.
-/

/-- The kind of entity referenced by a `Handle`. -/
inductive HandleType (OpInfo : Type) [HasOpInfo OpInfo] where
/-- An operation's opcode-specific property record. -/
| prop (opCode : OpInfo)
/-- An operation. -/
| op
/-- An SSA value, which can be an operation result or block argument. -/
| value
/-- A VeIR IR type. -/
| type

/--
A typed symbolic reference to an entity matched or created by a Puddle rule.

Handles are not supposed to be constructed by hand, but rather allocated by builders.
-/
structure Handle (OpInfo : Type) [HasOpInfo OpInfo] (handleType : HandleType OpInfo) where
  /-- The handle's rule-wide identifier. -/
  id : Nat
deriving Repr, DecidableEq, Inhabited

/-!
## Metadata tuples

In the Puddle DSL, metadata is a generic term for types and operation properties. Both
`MatchDecl.guard` and `CreateDecl.applyNative` need to translate between the concrete metadata
values and the handles that denote them. We thus need to define a translation between the two
representation types.

`MetadataTuple.Atom` describes a single type or property handle, while `MetadataTuple.Shape`
describes flat, right-associated tuples of those atoms. `IsMetadataTuple` witnesses that a type is
a valid metadata tuple, and `MetadataTuple.Shape.Values` gives the corresponding concrete metadata
type used during execution.
-/

/--
An atom of a metadata tuple, which is either a type handle or a property handle.
Its type parameter represents the kind of handle it denotes.
-/
inductive MetadataTuple.Atom (OpInfo : Type) [HasOpInfo OpInfo] : Type → Type 1 where
/-- A type handle. -/
| type : MetadataTuple.Atom OpInfo (Handle OpInfo .type)
/-- A property handle for an operation with opcode `opCode`. -/
| property (opCode : OpInfo) : MetadataTuple.Atom OpInfo (Handle OpInfo (.prop opCode))

/-- The concrete metadata type denoted by an atom's handle. -/
@[expose, reducible]
def MetadataTuple.Atom.Value {Handle : Type} : MetadataTuple.Atom OpInfo Handle → Type
| .type => TypeAttr
| .property opCode => propertiesOf opCode

/--
A flat right-associated tuple of type and property handles.
Its type parameter represents the tuple type it denotes.

It includes `unit` for empty tuples and `atom` to avoid a trailing `a × Unit` at the leaves.
-/
inductive MetadataTuple.Shape (OpInfo : Type) [HasOpInfo OpInfo] : Type → Type 1 where
/-- The shape of an empty metadata tuple. -/
| unit : MetadataTuple.Shape OpInfo Unit
/-- The shape of a single metadata handle. -/
| atom {Handle : Type} :
    MetadataTuple.Atom OpInfo Handle → MetadataTuple.Shape OpInfo Handle
/-- Prepend a metadata atom to an existing tuple shape. -/
| cons {Head Tail : Type} :
    MetadataTuple.Atom OpInfo Head → MetadataTuple.Shape OpInfo Tail →
      MetadataTuple.Shape OpInfo (Head × Tail)

/-- The concrete metadata type corresponding to a tuple shape. -/
@[expose, reducible]
def MetadataTuple.Shape.Values : MetadataTuple.Shape OpInfo Handles → Type
| .unit => Unit
| .atom metadataAtom => metadataAtom.Value
| .cons head tail => head.Value × tail.Values

/--
Witness that `Handles` is a tuple of type and property handle types.

The class only contains a `MetadataTuple.Shape` witness of the tuple type, which is used to
translate a tuple of handles into its tuple of concrete metadata values.

For example, `Handle OpInfo .type × Handle OpInfo (.prop opCode)` receives the shape
`.cons .type (.atom (.property opCode))` automatically.
-/
class IsMetadataTuple (OpInfo : Type) [HasOpInfo OpInfo] (Handles : Type) where
  shape : MetadataTuple.Shape OpInfo Handles

/--
The concrete metadata type denoted by a tuple of type and property handles.
For example, `Handle OpInfo .type × Handle OpInfo (.prop opCode)` denotes
`TypeAttr × propertiesOf opCode`.
-/
abbrev MetadataValues (OpInfo : Type) [HasOpInfo OpInfo] (Handles : Type)
    [self : IsMetadataTuple OpInfo Handles] : Type := self.shape.Values

/-!
The following instances synthesize `IsMetadataTuple` recursively for tuples of type and property
handles.
-/

instance : IsMetadataTuple OpInfo Unit := ⟨.unit⟩

instance : IsMetadataTuple OpInfo (Handle OpInfo .type) :=
  ⟨.atom .type⟩

instance (opCode : OpInfo) : IsMetadataTuple OpInfo (Handle OpInfo (.prop opCode)) :=
  ⟨.atom (.property opCode)⟩

instance [tail : IsMetadataTuple OpInfo Tail] :
    IsMetadataTuple OpInfo (Handle OpInfo .type × Tail) :=
  ⟨.cons .type tail.shape⟩

instance (opCode : OpInfo) [tail : IsMetadataTuple OpInfo Tail] :
    IsMetadataTuple OpInfo (Handle OpInfo (.prop opCode) × Tail) :=
  ⟨.cons (.property opCode) tail.shape⟩

/-!
## Matcher phase

`MatchDecl` is the internal declarative representation of a pattern constraint. Users should use
the `MatchProg.Builder` API, which allocates fresh handles, rather than construct declarations
directly.

Stored matcher declarations are ordered top-down, in execution order. The first declaration marks
the root operation; the remaining declarations constrain operations and operands recursively
reachable from the root.

Matching always proceeds from an entity already bound in the current assignment. The root
declaration seeds the assignment with the candidate root operation; every subsequent declaration
is anchored by an already-bound operation, SSA value, type, or metadata handle. A declaration may
reject that binding by checking additional constraints, and it may extend the assignment with newly
discovered operands, result types, properties, or results. Matching therefore expands outward from
the root through already-bound handles.
-/

/--
A predicate on an opcode-specific property record. It accepts a property when it returns `true`.
-/
abbrev PropertyMatcher (opCode : OpInfo) := propertiesOf opCode → Bool

/-- A predicate on an IR type. It accepts a type when it returns `true`. -/
abbrev TypeMatcher := TypeAttr → Bool

/--
A declarative matcher instruction for a Puddle pattern graph.

This is an internal representation; use `MatchProg.Builder` rather than constructing declarations
directly.
-/
inductive MatchDecl (OpInfo : Type) [HasOpInfo OpInfo] where
/-- Bind `type` to the type of the already-bound value `result`. -/
| value (type : Handle OpInfo .type) (result : Handle OpInfo .value)
/-- Require the type bound to `result` to be accepted by `matcher`. -/
| type (matcher : TypeMatcher) (result : Handle OpInfo .type)
/-- Require the concrete metadata denoted by `inputs` to satisfy `predicate`. -/
| guard {Inputs : Type} [IsMetadataTuple OpInfo Inputs]
    (inputs : Inputs) (predicate : MetadataValues OpInfo Inputs → Bool)
/-- Identify an operation from the already-bound `result` handle or first SSA-result handle in
`results`, require the given opcode, operands, result types, and properties, and bind the discovered
entities to their corresponding handles. -/
| operation (opCode : OpInfo)
    (operands : Array (Handle OpInfo .value))
    (returnTypes : Array (Handle OpInfo .type))
    (property : PropertyMatcher opCode)
    (propertyResult : Handle OpInfo (.prop opCode))
    (result : Handle OpInfo .op)
    (results : Array (Handle OpInfo .value))
/-- Mark `result` as the root operation and record its expected opcode, operands, result types, and
properties. `MatchProg.Builder` emits a companion `operation` declaration that enforces them. -/
| root (opCode : OpInfo)
    (operands : Array (Handle OpInfo .value))
    (returnTypes : Array (Handle OpInfo .type))
    (property : PropertyMatcher opCode)
    (propertyResult : Handle OpInfo (.prop opCode))
    (result : Handle OpInfo .op)

/--
A match program together with the value exported by its builder. Exports typically contain handles
used by the creation or replacement phase of a `Pattern`.

Declarations are stored in execution order, starting with the root marker and continuing through
the operation and operand constraints recursively reachable from it.
-/
structure MatchProg (OpInfo : Type) [HasOpInfo OpInfo] (Exports : Type) where
  /-- Match declarations in interpreter order, beginning with a root declaration. -/
  decls : List (MatchDecl OpInfo)
  /-- The number of rule-wide handle identifiers reserved by the matching phase. -/
  numHandles : Nat
  /-- Arbitrary builder output, typically handles needed by subsequent phases. -/
  exports : Exports

/-!
## Creation phase

After a successful match, the creation phase may derive metadata and create new operations.
Operations are created in declaration order, and their results can be used by later declarations or
by the terminal replacement.

Created operations may consume matched values or earlier-created values. Their result types must
be already-bound type handles, while their properties may be literal records or already-bound
property handles. Those handles may come from the matcher or an earlier `applyNative` declaration.
Puddle does not infer result types from operands or introduce unconstrained metadata during
creation.
-/

/--
An operand of a newly created operation.

The wrapped value handle may refer either to a matched value or to the result of an earlier creation
declaration. Pattern-wide handle numbering makes the two cases resolve uniformly.
-/
structure CreateOperand (OpInfo : Type) [HasOpInfo OpInfo] where
  /-- The matched or previously created value supplied as the operand. -/
  value : Handle OpInfo .value
deriving Repr, DecidableEq, Inhabited

/-- The source of the property record for a newly created operation. -/
inductive CreateProperty (OpInfo : Type) [HasOpInfo OpInfo] (opCode : OpInfo) where
/-- Use a concrete property record. -/
| literal (value : propertiesOf opCode)
/-- Resolve the property record from a previously bound handle. -/
| handle (value : Handle OpInfo (.prop opCode))

instance {opCode : OpInfo} :
    CoeTC (propertiesOf opCode) (CreateProperty OpInfo opCode) where
  coe := .literal

instance {opCode : OpInfo} :
    CoeTC (Handle OpInfo (.prop opCode)) (CreateProperty OpInfo opCode) where
  coe := .handle

/-- An internal declarative instruction in a creation program. -/
inductive CreateDecl (OpInfo : Type) [HasOpInfo OpInfo] where
/--
Create an operation, resolving its operands, result types, and properties, and bind the newly
created operation and SSA results to `result` and `results`.
-/
| operation (opCode : OpInfo) (operands : Array (CreateOperand OpInfo))
    (resultTypes : Array (Handle OpInfo .type))
    (properties : CreateProperty OpInfo opCode)
    (result : Handle OpInfo .op)
    (results : Array (Handle OpInfo .value))
/-- Run a pure metadata transformation and bind its output values to `outputs`. Returning `none`
rejects the creation phase. -/
| applyNative {Inputs Outputs : Type}
    [IsMetadataTuple OpInfo Inputs]
    [IsMetadataTuple OpInfo Outputs]
    (inputs : Inputs)
    (rewrite : MetadataValues OpInfo Inputs → Option (MetadataValues OpInfo Outputs))
    (outputs : Outputs)

/--
The ordered creation phase of a Puddle rule.

Each declaration may consume metadata or values bound during matching or by earlier creation
declarations. Every input must resolve through an already-bound handle. Handles allocated by the
creation builder occupy the half-open range `[firstHandleId, numHandles)`.
-/
structure CreateProg (OpInfo : Type) [HasOpInfo OpInfo] (Exports : Type) where
  /-- Creation declarations in execution order. -/
  decls : List (CreateDecl OpInfo)
  /-- The first handle identifier owned by the creation program. -/
  firstHandleId : Nat
  /-- The first unused rule-wide handle identifier after the creation program. -/
  numHandles : Nat
  /-- Arbitrary builder output, typically handles needed by the replacement phase. -/
  exports : Exports

/-!
## Replacement

A terminal replacement specifies the SSA values that replace the matched root operation's results.
Each selected handle may denote a non-root matched value or a value produced during creation. Order
and arity matter: entry `i` replaces root result `i`. Execution rejects a replacement whose length
differs from the root's result count or whose selected values include one of the root's own results.
-/

/-- Value handles that replace the root operation's results, in result order. -/
abbrev Replacement (OpInfo : Type) [HasOpInfo OpInfo] := Array (Handle OpInfo .value)

/-!
## Puddle Pattern

A Puddle rule packages its match program, ordered creation program, and terminal replacement. Its
export types allow builders to carry differently shaped collections of handles between phases.
-/

/--
A complete declarative Puddle rewrite pattern. Prefer constructing one with `Pattern.Builder`.
-/
structure Pattern (OpInfo : Type) [HasOpInfo OpInfo] where
  /-- The type of data exported by the matching phase. -/
  Exports : Type
  /-- The graph pattern matched against a candidate root operation. -/
  matcher : MatchProg OpInfo Exports
  /-- The type of data exported by the creation phase. -/
  CreationExports : Type
  /-- The creation program run after a successful match. -/
  creation : CreateProg OpInfo CreationExports
  /-- Values used to replace the root's results. -/
  replacement : Replacement OpInfo

end

end Veir.Puddle
