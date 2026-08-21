module

public import Veir.PatternRewriter.Puddle.Definitions

/-!
# Puddle Builders

This file contains author-facing builders for constructing declarative Puddle rewrite patterns
without having to manually manage handles for matched IR elements. The builders are based on a state
monad that automatically allocates handles, allowing the use of a do-notation style for authoring
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
Match a value with a given type. This should be used to match values where their definitions
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
Require an inline native predicate over matched type/property metadata.

Call `guard` after declaring every handle in `inputs`. It runs after those declarations have bound
their concrete metadata; returning `true` keeps the match and returning `false` rejects it.
-/
@[expose, inline]
protected def MatchProg.guard {Inputs : Type} [IsMetadataTuple OpCode Inputs]
    (inputs : Inputs) (predicate : MetadataValues OpCode Inputs → Bool) :
    MatchProg.Builder Unit :=
  ⟨fun state =>
    ((), {
      state with
      -- Match declarations normally execute in reverse authoring order. A guard consumes handles
      -- declared before it, so place it after the declarations already accumulated.
      decls := state.decls ++ [.guard inputs predicate]
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

/-!
## Creation builder

`CreateProg.Builder` provides `do` notation for the creation phase. Each call to
`CreateProg.operation` appends a logical step and returns fresh handles that later steps may
consume. `CreateProg.build` seeds handle allocation immediately after the matcher's handle range.
-/

namespace MetadataTuple.Atom

/-- Allocate the handle denoted by a metadata atom. -/
@[expose]
def fresh {Handle : Type} : MetadataTuple.Atom OpCode Handle → Nat → Handle × Nat
| .type, nextId => (⟨nextId⟩, nextId + 1)
| .property _, nextId => (⟨nextId⟩, nextId + 1)

end MetadataTuple.Atom

namespace MetadataTuple.Shape

/-- Allocate every handle in a metadata-tuple shape. -/
@[expose]
def fresh : (shape : MetadataTuple.Shape OpCode Handles) → Nat → Handles × Nat
| .unit, nextId => ((), nextId)
| .atom metadataAtom, nextId => metadataAtom.fresh nextId
| .cons head tail, nextId =>
    let (headHandle, nextId) := head.fresh nextId
    let (tailHandles, nextId) := tail.fresh nextId
    ((headHandle, tailHandles), nextId)

end MetadataTuple.Shape

namespace MetadataTuple

/-- Allocate all handles in a metadata tuple. -/
@[expose]
def fresh {Handles : Type} [self : IsMetadataTuple OpCode Handles] (nextId : Nat) : Handles × Nat :=
  self.shape.fresh nextId

@[simp]
theorem fresh_unit (nextId : Nat) :
    fresh (Handles := Unit) nextId = ((), nextId) := by
  rfl

@[simp]
theorem fresh_type (nextId : Nat) :
    fresh (Handles := Handle OpCode .type) nextId = (⟨nextId⟩, nextId + 1) := by
  rfl

@[simp]
theorem fresh_property {opCode : OpCode} (nextId : Nat) :
    fresh (Handles := Handle OpCode (.prop opCode)) nextId = (⟨nextId⟩, nextId + 1) := by
  rfl

end MetadataTuple

/-- Allow value handles to be written directly in creation operand arrays. -/
instance : Coe (Handle OpCode .value) (CreateOperand OpCode) where
  coe := fun value => ⟨value⟩

/-- The operation and SSA-result handles introduced by a creation declaration. -/
structure CreatedOpHandle where
  /-- The newly-created operation. -/
  op : Handle OpCode .op
  /-- Its result values, in result order. -/
  res : Array (Handle OpCode .value)

/-- Coerce an operation-and-results bundle to its operation handle. -/
instance : Coe CreatedOpHandle (Handle OpCode .op) where
  coe := fun handle => handle.op

/-- Convert a literal property record or property handle into creation syntax. -/
class CreatePropertyArg (opCode : OpCode) (Arg : Type) where
  toCreateProperty : Arg → CreateProperty OpCode opCode

instance : CreatePropertyArg opCode (propertiesOf opCode) where
  toCreateProperty := .literal

instance : CreatePropertyArg opCode (Handle OpCode (.prop opCode)) where
  toCreateProperty := .handle

/-- Expose the handle coercion to validity simplification without unfolding the typeclass. -/
@[simp]
theorem CreatePropertyArg.toCreateProperty_handle
    (handle : Handle OpCode (.prop opCode)) :
    CreatePropertyArg.toCreateProperty (opCode := opCode) handle = .handle handle := by
  rfl

instance : CreatePropertyArg (.arith .addi) ArithIntegerOverflowFlagsProperties where
  toCreateProperty := fun value =>
    CreateProperty.literal (OpInfo := OpCode) (opCode := .arith .addi)
      (show propertiesOf (OpCode.arith .addi) from value)

/-- Internal accumulator used by `CreateProg.Builder`. -/
structure CreateProg.BuilderState where
  /-- The next free rule-wide handle identifier. -/
  nextId : Nat := 0
  /-- Declarations in reverse construction order. -/
  decls : List (CreateDecl OpCode) := []

/-- A stateful builder for an ordered creation program that exports a value of type `α`. -/
structure CreateProg.Builder (α : Type) where
  /-- Run the builder from an explicit internal state. Prefer `CreateProg.build`. -/
  run : CreateProg.BuilderState → α × CreateProg.BuilderState

/-- `do`-notation support for composing creation declarations in program order. -/
@[inline]
instance CreateProg.instMonadBuilder : Monad CreateProg.Builder where
  pure value := ⟨fun state => (value, state)⟩
  bind action next := ⟨fun state =>
    let (value, state) := action.run state
    (next value).run state⟩

/--
Append an operation to the creation program and return handles for it and its results.

`operands` may contain matcher handles or handles returned by earlier creation steps. `resultTypes`
must contain matcher type handles and determines the number of result handles allocated. Unlike a
property matcher, `properties` is the concrete property record installed on the new operation.
-/
@[expose, inline]
def CreateProg.operation (opCode : OpCode) (operands : Array (CreateOperand OpCode))
    (resultTypes : Array (Handle OpCode .type)) {Properties : Type}
    [CreatePropertyArg opCode Properties] (properties : Properties) :
    CreateProg.Builder CreatedOpHandle :=
  ⟨fun state =>
    let op := Handle.mk (OpInfo := OpCode) state.nextId
    let res := (Array.range resultTypes.size).map fun index =>
      Handle.mk (OpInfo := OpCode) (state.nextId + index + 1)
    (⟨op, res⟩, {
      nextId := state.nextId + resultTypes.size + 1
      decls := .operation opCode operands resultTypes
        (CreatePropertyArg.toCreateProperty properties) op res :: state.decls
    })⟩

/--
Apply an inline native metadata function to a tuple of type/property handles.

`Outputs` is a bundle type built from `Unit`, type handles, property handles, and products. The
returned value has that same handle shape and may be consumed by later creation declarations.
Returning `none` from `rewrite` rejects creation.
-/
@[expose, inline]
def CreateProg.applyNative {Inputs Outputs : Type}
    [IsMetadataTuple OpCode Inputs] [IsMetadataTuple OpCode Outputs]
    (inputs : Inputs)
    (rewrite : MetadataValues OpCode Inputs → Option (MetadataValues OpCode Outputs)) :
    CreateProg.Builder Outputs :=
  ⟨fun state =>
    let (outputs, nextId) := MetadataTuple.fresh (Handles := Outputs) state.nextId
    (outputs, {
      nextId
      decls := .applyNative inputs rewrite outputs :: state.decls
    })⟩

/--
Build a creation program using the matcher's exports and continuing its handle numbering.

The callback receives `matcher.exports`. Declarations accumulated internally in reverse are stored
in execution order in the resulting program.
-/
@[expose, inline]
def CreateProg.build (matcher : MatchProg OpCode α)
    (builder : α → CreateProg.Builder β) : CreateProg OpCode β :=
  let firstHandleId := matcher.numHandles
  let (exports, state) := (builder matcher.exports).run { nextId := firstHandleId }
  ⟨state.decls.reverse, firstHandleId, state.nextId, exports⟩

/-- Build a creation program with no declarations, forwarding `matcher.exports` unchanged. -/
@[expose, inline]
def CreateProg.empty (matcher : MatchProg OpCode α) : CreateProg OpCode α :=
  CreateProg.build matcher pure

/-! ## Replacement and pattern builders -/

/-- Construct a one-element replacement for a single-result root operation. -/
@[expose]
def Replacement.ofValue (value : Handle OpCode .value) : Replacement OpCode :=
  #[value]

/--
Build a rule by composing its three phases.

`matcherBuilder` is executed first. Its exported `α` is passed to `creationBuilder`, whose exported
`β` is then passed to `replacementBuilder`. Use `pure` as the creation builder to create nothing
and forward the matcher exports. Use `Replacement.ofValue` as the final function for a
single-result root.

This function only assembles the rule. Semantic preservation is established separately by proving
the resulting rule's validity obligation.
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
