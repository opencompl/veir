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
  /-- Non-root declarations in interpreter order. -/
  decls : List (MatchDecl OpCode) := []
  /-- The most recently designated root. -/
  root? : Option (Handle OpCode .op) := none
  /-- Operation constraints created by root designations. -/
  rootConstraints : List (MatchDecl OpCode) := []
  /-- Number of root designations, used to reject missing or duplicate roots structurally. -/
  numRoots : Nat := 0

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
  /-- The root operation handle. -/
  op : Handle OpCode .op
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
    (result, { state with
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
    (result, { state with
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
    (⟨op, res, properties⟩, { state with
      nextId := state.nextId + returnTypes.size + 2
      decls := .operation opCode operands returnTypes property properties op res :: state.decls
    })⟩

/--
Match a root operation given its opcode, operands, result types, and properties. This should be the
last declaration in a Puddle match, and should be called exactly once. At runtime, this is the entry
point of the matcher. It returns a handle for accessing its concrete properties, but in particular
does not return handles for its results or the operation itself, since those are accessible from the
root through already-bound handles.
-/
@[expose, inline]
def MatchProg.root (opCode : OpCode) (operands : Array (Handle OpCode .value))
    (returnTypes : Array (Handle OpCode .type))
    (property : PropertyMatcher opCode := fun _ => true) :
    MatchProg.Builder (RootHandle opCode) :=
  ⟨fun state =>
    let op := Handle.mk (OpInfo := OpCode) state.nextId
    let results := (Array.range returnTypes.size).map fun index =>
      Handle.mk (OpInfo := OpCode) (state.nextId + index + 1)
    let properties := Handle.mk (OpInfo := OpCode) (state.nextId + returnTypes.size + 1)
    (⟨op, properties⟩, { state with
      nextId := state.nextId + returnTypes.size + 2
      root? := some op
      rootConstraints :=
        .operation opCode operands returnTypes property properties op results ::
          state.rootConstraints
      numRoots := state.numRoots + 1
    })⟩

/-- Build a match program, panicking unless exactly one call to `MatchProg.root` was made. -/
@[expose, inline]
def MatchProg.build (builder : MatchProg.Builder α) : MatchProg OpCode α :=
  let (exports, state) := builder.run {}
  let rootHandle :=
    match state.numRoots, state.root? with
    | 1, some root => root
    | _, _ => panic! "MatchProg.build requires exactly one call to MatchProg.root"
  {
    rootHandle
    decls := state.rootConstraints ++ state.decls
    numHandles := state.nextId
    exports
  }

/-!
## Creation builder

`CreateProg.Builder` provides `do` notation for the creation phase. Each call to
`CreateProg` builder functions appends a logical step and returns fresh handles that later steps may
consume.
-/

/-- The operation and SSA-result handles introduced by a creation declaration. -/
structure CreatedOpHandle where
  /-- The newly-created operation. -/
  op : Handle OpCode .op
  /-- Its result values, in result order. -/
  res : Array (Handle OpCode .value)

/-- Coerce an operation-and-results bundle to its operation handle. -/
instance : Coe CreatedOpHandle (Handle OpCode .op) where
  coe := fun handle => handle.op

/-- Internal accumulator used by `CreateProg.Builder`. -/
structure CreateProg.BuilderState where
  /-- The next free pattern-wide handle identifier. -/
  nextId : Nat := 0
  /-- Declarations in reverse construction order. -/
  decls : List (CreateDecl OpCode) := []

/-- A stateful builder for an ordered creation program that exports a value of type `α`. -/
structure CreateProg.Builder (α : Type) where
  /-- Run the builder from an explicit internal state. -/
  run : CreateProg.BuilderState → α × CreateProg.BuilderState

/-- Monadic support for composing creation declarations in program order. -/
@[inline]
instance CreateProg.instMonadBuilder : Monad CreateProg.Builder where
  pure value := ⟨fun state => (value, state)⟩
  bind action next := ⟨fun state =>
    let (value, state) := action.run state
    (next value).run state⟩

/--
Append a concrete type to the creation program and return the handle bound to it.
-/
@[expose, inline]
def CreateProg.type {Attr : Type} [IsTypeAttr Attr] (value : Attr) :
    CreateProg.Builder (Handle OpCode .type) :=
  ⟨fun state =>
    let result := Handle.mk (OpInfo := OpCode) state.nextId
    (result, {
      nextId := state.nextId + 1
      decls := .type (value : TypeAttr) result :: state.decls
    })⟩

/--
Append a concrete property record to the creation program and return the handle bound to it.
-/
@[expose, inline]
def CreateProg.property (opCode : OpCode) (value : propertiesOf opCode) :
    CreateProg.Builder (Handle OpCode (.prop opCode)) :=
  ⟨fun state =>
    let result := Handle.mk (OpInfo := OpCode) state.nextId
    (result, {
      nextId := state.nextId + 1
      decls := .property opCode value result :: state.decls
    })⟩

/-- Append an operation to the creation program and return handles for it and its results. -/
@[expose, inline]
def CreateProg.operation (opCode : OpCode) (operands : Array (Handle OpCode .value))
    (resultTypes : Array (Handle OpCode .type))
    (properties : Handle OpCode (.prop opCode)) : CreateProg.Builder CreatedOpHandle :=
  ⟨fun state =>
    let op := Handle.mk (OpInfo := OpCode) state.nextId
    let res := (Array.range resultTypes.size).map fun index =>
      Handle.mk (OpInfo := OpCode) (state.nextId + index + 1)
    (⟨op, res⟩, {
      nextId := state.nextId + resultTypes.size + 1
      decls := .operation opCode operands resultTypes properties op res :: state.decls
    })⟩

/-- Build a creation program using the matcher's exports and continuing its handle numbering. -/
@[expose, inline]
def CreateProg.build (matcher : MatchProg OpCode α)
    (builder : α → CreateProg.Builder β) : CreateProg OpCode β :=
  let (exports, state) := (builder matcher.exports).run { nextId := matcher.numHandles }
  /- The creation declaration are reversed, since they are collected in opposite order. -/
  ⟨state.decls.reverse, state.nextId, exports⟩

/-- Build a creation program with no declarations, forwarding `matcher.exports` unchanged. -/
@[expose, inline]
def CreateProg.empty (matcher : MatchProg OpCode α) : CreateProg OpCode α :=
  CreateProg.build matcher pure

/-! ## Replacement and pattern builders -/

/-- Allow passing a single value handle directly as a replacement. -/
instance : Coe (Handle OpInfo .value) (Replacement OpInfo) where
  coe := fun value => ⟨#[value]⟩

/-- Allow passing an array of value handles directly as a replacement. -/
instance : Coe (Array (Handle OpInfo .value)) (Replacement OpInfo) where
  coe := Replacement.mk

/-- Allow replacing the root with all results of a newly-created operation. -/
instance : Coe CreatedOpHandle (Replacement OpCode) where
  coe := fun operation => ⟨operation.res⟩

/--
Build a puddle pattern by composing its three phases.

`matcherBuilder` is executed first. Its exported `α` is passed to `creationBuilder`, whose exported
`β` is then passed to `replacementBuilder`.
-/
@[expose, inline]
def Pattern.Builder (matcherBuilder : MatchProg.Builder α)
    (creationBuilder : α → CreateProg.Builder β)
    (replacementBuilder : β → Replacement OpCode) : Pattern OpCode :=
  let matcher := MatchProg.build matcherBuilder
  let creation := CreateProg.build matcher creationBuilder
  {
    Exports := α
    matcher := matcher
    CreationExports := β
    creation := creation
    replacement := replacementBuilder creation.exports
  }

end

end Veir.Puddle
