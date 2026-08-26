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
A declarative matcher instruction for a Puddle pattern graph; use `MatchProg.Builder` rather than
constructing declarations directly.
-/
inductive MatchDecl (OpInfo : Type) [HasOpInfo OpInfo] where
/-- Bind `type` to the type of the already-bound value `result`. -/
| value (type : Handle OpInfo .type) (result : Handle OpInfo .value)
/-- Require the type bound to `result` to be accepted by `matcher`. -/
| type (matcher : TypeMatcher) (result : Handle OpInfo .type)
/-- Identify an operation from the already-bound `result` or `results` handle, check every result
handle against that operation, require the given opcode, operands, result types, and properties,
and bind the discovered entities to their corresponding handles. -/
| operation (opCode : OpInfo)
    (operands : Array (Handle OpInfo .value))
    (returnTypes : Array (Handle OpInfo .type))
    (property : PropertyMatcher opCode)
    (propertyResult : Handle OpInfo (.prop opCode))
    (result : Handle OpInfo .op)
    (results : Array (Handle OpInfo .value))
/-- Bind `result` to the candidate root operation. `MatchProg.Builder` emits a companion `operation`
declaration that constrains the root after this declaration seeds the assignment. -/
| root (result : Handle OpInfo .op)

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

After a successful match, the creation phase may create new operations. Operations are created in
declaration order, and their results can be used by later declarations or by the terminal
replacement.

Created operations may consume matched values or earlier-created values. Their result types and
properties must be already-bound metadata handles. Those handles may come from the matcher or an
earlier property declaration.
-/

/-- An internal declarative instruction in a creation program. -/
inductive CreateDecl (OpInfo : Type) [HasOpInfo OpInfo] where
/-- Bind a concrete type to `result` for use by a later operation declaration. -/
| type (value : TypeAttr) (result : Handle OpInfo .type)
/-- Bind a concrete property record to `result` for use by a later operation declaration. -/
| property (opCode : OpInfo) (value : propertiesOf opCode) (result : Handle OpInfo (.prop opCode))
/--
Create an operation, resolving its operands, result types, and properties, and bind the newly
created operation and SSA results to `result` and `results`.
-/
| operation (opCode : OpInfo) (operands : Array (Handle OpInfo .value))
    (resultTypes : Array (Handle OpInfo .type))
    (properties : Handle OpInfo (.prop opCode))
    (result : Handle OpInfo .op)
    (results : Array (Handle OpInfo .value))

/--
The ordered creation phase of a Puddle rule.

Each declaration may consume metadata or values bound during matching or by earlier creation
declarations. Every input must resolve through an already-bound handle. The creation builder starts
allocating immediately after the matcher's handle range; `numHandles` records the first unused
pattern-wide handle identifier after creation.
-/
structure CreateProg (OpInfo : Type) [HasOpInfo OpInfo] (Exports : Type) where
  /-- Creation declarations in execution order. -/
  decls : List (CreateDecl OpInfo)
  /-- The first unused rule-wide handle identifier after the creation program. -/
  numHandles : Nat
  /-- Arbitrary builder output, typically handles needed by the replacement phase. -/
  exports : Exports

/-!
## Replacement

A terminal replacement specifies the SSA values that replace the matched root operation's results.
Each selected handle may denote a non-root matched value or a value produced during creation.
Execution will fail if the replacement differs in length from the root's result count or if the
replacement includes one of the root's own results.
-/

/-- Value handles that replace the root operation's results. -/
structure Replacement (OpInfo : Type) [HasOpInfo OpInfo] where
  /-- The replacement values, in root-result order. -/
  values : Array (Handle OpInfo .value)

/-!
## Puddle Pattern

A Puddle rule packages its match program, ordered creation program, and terminal replacement. The
exports types are used to pass handles between phases. The pattern is not meant to be constructed
directly; use `Pattern.Builder` instead.
-/

/--
A complete declarative Puddle rewrite pattern. Prefer constructing one with `Pattern.Builder`.
-/
structure Pattern (OpInfo : Type) [HasOpInfo OpInfo] where
  /-- The type of data (usually handles) exported by the matching phase. -/
  Exports : Type
  /-- The graph pattern matched against a candidate root operation. -/
  matcher : MatchProg OpInfo Exports
  /-- The type of data (usually handles) exported by the creation phase. -/
  CreationExports : Type
  /-- The creation program run after a successful match. -/
  creation : CreateProg OpInfo CreationExports
  /-- Values used to replace the root's results. -/
  replacement : Replacement OpInfo

end

end Veir.Puddle
