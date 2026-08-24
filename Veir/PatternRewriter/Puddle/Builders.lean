module

public import Veir.PatternRewriter.Puddle.Definitions

/-!
# Puddle Builders

This file contains author-facing builders for constructing declarative Puddle rewrite patterns
without having to manually manage handles for matched IR elements. The builders are based on a state
monad that automatically allocates handles, allowing the use of do-notations for authoring
match programs. In particular, the programs are built in the reverse order of the final match
program, so the root operation is declared last, and the leaves are declared first.
-/

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-!
## Matcher builder

`MatchProg.Builder` provides a monadic interface for authoring the matching phase of a Puddle
pattern. Each builder operation adds one constraint and returns fresh handles for later constraints
or for export to the following phases. Although the source reads from leaves to root, declarations
are prepended so the finished program can be interpreted from root to leaves.
-/

/-- Internal accumulator used by `MatchProg.Builder`. -/
structure MatchProg.BuilderState where
  /-- The next free identifier for a handle. -/
  nextId : Nat := 0
  /-- Declarations in interpreter order; after a well-formed build, the root is first. -/
  decls : List (MatchDecl OpCode) := []

/--
A stateful builder for a match program that exports a value of type `α`.
The exported value should consist of handles needed by the creation or replacement phase.
-/
structure MatchProg.Builder (α : Type) where
  /--
  Run the builder from an explicit internal state. Should not be used directly, use
  `MatchProg.build` instead.
  -/
  run : MatchProg.BuilderState → α × MatchProg.BuilderState

/--
The handles allocated for a matched operation. It contains the operation handle, an array of
handles for its SSA results, and a handle for its concrete properties.
-/
structure OpHandle (opCode : OpCode) where
  /-- The operation handle. -/
  op : Handle OpCode .op
  /-- The handles for each return value. -/
  res : Array (Handle OpCode .value)
  /-- The matched operation's concrete properties. -/
  properties : Handle OpCode (.prop opCode)

/-- Handles exported by a matched root without exposing the root's SSA results. -/
structure RootHandle (opCode : OpCode) where
  /-- The matched root's concrete properties. -/
  properties : Handle OpCode (.prop opCode)

/-- Monadic support for building match patterns. -/
@[inline]
instance MatchProg.instMonadBuilder : Monad MatchProg.Builder where
  pure value := ⟨fun state => (value, state)⟩
  bind action next := ⟨fun state =>
    let (value, state) := action.run state
    (next value).run state⟩

/--
Match a type with a given constraint.
For ease of use, the constraint can just be expressed as a predicate on a specific type attribute,
which can be `Attribute` if needed.
-/
@[expose, inline]
def MatchProg.type (Attr : Type) [IsTypeAttr Attr] (matcher : Attr → Bool := fun _ => true) :
    MatchProg.Builder (Handle OpCode .type) :=
  ⟨fun state =>
    let result := Handle.mk (OpInfo := OpCode) state.nextId
    let matcher := fun (attr : TypeAttr) => ((attr.cast? Attr).map matcher).getD false
    (result, {
      nextId := state.nextId + 1
      decls := .type matcher result :: state.decls
    })⟩

/--
Match a value with a given type. This should be used to match values where their kind
(i.e. whether they are block arguments or operation results) do not matter.
-/
@[expose, inline]
def MatchProg.value (type : Handle OpCode .type) : MatchProg.Builder (Handle OpCode .value) :=
  ⟨fun state =>
    let result := Handle.mk (OpInfo := OpCode) state.nextId
    (result, {
      nextId := state.nextId + 1
      decls := .value type result :: state.decls
    })⟩

/--
Match a non-root operation given its opcode, operands, result types, and properties. The operation
is assumed to have no block arguments or regions, but can have any attribute dictionary. Returns
a bundle of handles that contains the operation handle, an array of handles for its SSA results,
and a handle for its concrete properties.
-/
@[expose, inline]
def MatchProg.operation (opCode : OpCode) (operands : Array (Handle OpCode .value))
    (returnTypes : Array (Handle OpCode .type))
    (property : PropertyMatcher opCode := fun _ => true) :
    MatchProg.Builder (OpHandle opCode) :=
  ⟨fun state =>
    let op := Handle.mk (OpInfo := OpCode) state.nextId
    let res := (Array.range returnTypes.size).map fun index =>
      Handle.mk (OpInfo := OpCode) (state.nextId + index + 1)
    let properties := Handle.mk (OpInfo := OpCode) (state.nextId + returnTypes.size + 1)
    (⟨op, res, properties⟩, {
      nextId := state.nextId + returnTypes.size + 2
      decls := .operation opCode operands returnTypes property properties op res :: state.decls
    })⟩

/--
Match a root operation given its opcode, operands, result types, and properties. This should be the
last declaration in a Puddle match. At runtime, this is the entry point of the matcher. It returns
a handle for accessing its concrete properties, but in particular does not return handles for its
results or the operation itself, since those are accessible from the root through already-bound
handles.
-/
@[expose, inline]
def MatchProg.root (opCode : OpCode) (operands : Array (Handle OpCode .value))
    (returnTypes : Array (Handle OpCode .type))
    (property : PropertyMatcher opCode := fun _ => true) :
    MatchProg.Builder (RootHandle opCode) :=
  ⟨fun state =>
    let op := Handle.mk (OpInfo := OpCode) state.nextId
    let properties := Handle.mk (OpInfo := OpCode) (state.nextId + 1)
    (⟨properties⟩, {
      nextId := state.nextId + 2
      decls := .root opCode operands returnTypes property properties op ::
        .operation opCode operands returnTypes property properties op #[] :: state.decls
    })⟩

/-- Build a match program using `MatchProg.Builder`. -/
@[expose, inline]
def MatchProg.build (builder : MatchProg.Builder α) : MatchProg OpCode α :=
  let (exports, state) := builder.run {}
  ⟨state.decls, state.nextId, exports⟩

end

end Veir.Puddle
