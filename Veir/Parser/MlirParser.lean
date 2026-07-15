import Veir.Parser.Parser
import Veir.Parser.AttrParser
import Veir.Parser.DecidableInBounds
import Veir.IR.Basic
import Veir.Rewriter.InsertPoint
import Veir.Rewriter.Basic
import Veir.Rewriter.GetSet
import Veir.Rewriter.WellFormed
import Veir.Rewriter.WfRewriter
import Veir.Properties
import Veir.GlobalOpInfo

open Veir.Parser.Lexer
open Veir.Parser
open Veir.AttrParser

namespace Veir.Parser

open Veir.Parser.ParserError

variable {ctx : IRContext OpCode}

/--
  The state of a block encountered during parsing.
  A block is either `Defined` (its label has been parsed) or `ForwardDeclared`
  (it has only been referenced, e.g., as a block operand, but not yet defined).
-/
inductive BlockEntry where
  | Defined (block : BlockPtr) (loc : Location)
  | ForwardDeclared (block : BlockPtr) (loc : Location)
  deriving Inhabited

/-- Get the block pointer of a `BlockEntry`, regardless of its state. -/
def BlockEntry.block : BlockEntry → BlockPtr
  | .Defined block _ => block
  | .ForwardDeclared block _ => block

/--
  Bookkeeping for an SSA value referenced before it is defined (a "forward reference").

  Following MLIR's generic-form parser, the name table is flat across all regions: a forward
  reference is resolved by the first textual definition of the name, wherever it appears. Each
  referenced result index holds a detached single-result placeholder operation standing in for
  the value; when the definition is parsed, all uses of each placeholder are replaced by the
  real value (via `Rewriter.replaceValue`) and the placeholder is erased.

  Whether such a reference is actually legal (dominance, `IsolatedFromAbove`) is a verifier
  concern that MLIR checks after parsing; we likewise leave it to a later verification pass and
  only report values that are never defined anywhere.

  This mirrors MLIR's approach that uses a throwaway operation result as the placeholder
  (specifically `unrealized_conversion_cast`).
-/
structure ForwardValue where
  /-- Placeholder operation per referenced result index, with that index's first-use location. -/
  placeholders : Std.HashMap Nat (OperationPtr × Location)
  /-- Location of the first use, used for error reporting if the value is never defined. -/
  loc : Location
  deriving Inhabited

structure MlirParserState where
  /-- The current IR context. -/
  ctx : WfIRContext OpCode
  /-- The values that have been defined for a given name at that point in the parser,
      along with the byte offset of where the value name token was parsed. -/
  values : Std.HashMap ByteArray (Array ValuePtr × Location)
  /--
    The values defined in each currently active nested scope.
    Each scope sees all values defined in parent scopes (those that appear earlier in the array).
  -/
  definitionsPerScope : Array (Std.HashSet ByteArray)
  /--
    Values referenced but not yet defined, keyed by name. Following MLIR's generic-form parser,
    this table is flat: a definition resolves the forward reference regardless of which region
    it appears in. Entries remaining when top-level parsing finishes are reported as uses of
    undefined values.
  -/
  forwardValues : Std.HashMap ByteArray ForwardValue
  /--
    The blocks that have been encountered during parsing, along with whether
    they have been defined or only forward declared.
  -/
  blocks : Std.HashMap ByteArray BlockEntry
  /-- Whether to accept ops/types/attrs from unregistered dialects. -/
  allowUnregisteredDialect : Bool := false
  deriving Inhabited

def MlirParserState.fromContext (ctx : WfIRContext OpCode)
    (allowUnregisteredDialect : Bool := false) : MlirParserState :=
  {
    ctx
    allowUnregisteredDialect
    values := Std.HashMap.emptyWithCapacity 128
    definitionsPerScope := #[Std.HashSet.emptyWithCapacity 2]
    forwardValues := Std.HashMap.emptyWithCapacity 1
    blocks := Std.HashMap.emptyWithCapacity 1
  }

abbrev MlirParserM := StateT MlirParserState (EStateM ParserError ParserState)

/--
  Execute the action with the given initial state.
  Returns the result along with the final state, or an error message.
-/
def MlirParserM.run (self : MlirParserM α)
  (mlirParserState : MlirParserState) (parserState: ParserState) : Except ParserError (α × MlirParserState × ParserState) :=
  match (StateT.run self mlirParserState).run parserState with
  | .ok (a, mlirParserState) parserState => .ok (a, mlirParserState, parserState)
  | .error err _ => .error err

/--
  Execute the action with the given initial state.
  Returns the result or an error message.
-/
def MlirParserM.run' (self : MlirParserM α)
  (mlirParserState : MlirParserState) (parserState: ParserState) : Except ParserError α :=
  match self.run mlirParserState parserState with
  | .ok (a, _, _) => .ok a
  | .error err => .error err

/--
  Get the current IR context that is stored in the parser state.
-/
def getContext : MlirParserM (WfIRContext OpCode) := do
  return (← get).ctx

/--
  Get the array of values associated with a previously parsed name.
-/
def getValues? (name : ByteArray) : MlirParserM (Option (Array ValuePtr × Location)) := do
  return (← get).values[name]?

/--
  Get the original input that is being parsed.
-/
def getInput : MlirParserM ByteArray := do
  return (← getThe ParserState).input

/--
  Run an action within a new nested scope. This scope will be able to see all definitions in
  parent scopes and any definitions it add will only be visible within it and child scopes.
-/
def inChildScope {α : Type} (m : MlirParserM α) : MlirParserM α := do
  /- Push a new scope. -/
  modify fun s => { s with definitionsPerScope := s.definitionsPerScope.push (.emptyWithCapacity 128) }

  let result ← m

  /- Pop the scope. -/
  modify fun s => Id.run do
    let mut values := s.values
    /- Erase each variable defined in the last scope. -/
    for name in s.definitionsPerScope.back! do
      values := values.erase name
    { s with values, definitionsPerScope := s.definitionsPerScope.pop }

  return result

/--
  Set the current IR context.
  This should be called whenever any modifications have been made to the context
  outside of the parser monad.
-/
def setContext (ctx : WfIRContext OpCode) : MlirParserM Unit := do
  modify fun s => {s with ctx := ctx}

/--
  Modifies the current IR context.
-/
def modifyContext (f : WfIRContext OpCode → WfIRContext OpCode) : MlirParserM Unit := do
  modify fun s => {s with ctx := f s.ctx}

/--
  Modifies the current IR context.

  This function should be used instead of modifying the context with
  `get`/`getContext` and `set`/`setContext` in order to preserve linearity.
-/
def modifyContextM' (f : WfIRContext OpCode → MlirParserM (α × WfIRContext OpCode)) : MlirParserM α := do
  let ctx ← getContext
  -- This `setContext` is required to preserve the linearity of the state
  setContext default
  let (r, ctx) ← f ctx
  setContext ctx
  pure r

/--
  Modifies the current IR context.

  This function should be used instead of modifying the context with
  `get`/`getContext` and `set`/`setContext` in order to preserve linearity.
-/
def modifyContextM (f : WfIRContext OpCode → MlirParserM (WfIRContext OpCode)) : MlirParserM Unit :=
  modifyContextM' (fun ctx => do pure ((), ← f ctx))

/--
  The operation code used for forward-reference placeholders.
  We use a throwaway operation result (specifically a `builtin.unrealized_conversion_cast`)
  to stand in for a value that is referenced before it is defined.
-/
def placeholderOpCode : OpCode := .builtin .unrealized_conversion_cast

/--
  Create a detached, single-result placeholder operation of the given type.
  Its result is used to stand in for a value that has been referenced but not yet
  defined. The operation is not inserted into any block; once the real definition is
  parsed, `resolveForwardValue` replaces all uses of this result with the real value
  and erases this operation.
-/
def createForwardRefPlaceholder (ty : TypeAttr) (loc : Location) : MlirParserM OperationPtr :=
  modifyContextM' fun ctx => do
    match WfRewriter.createOp ctx placeholderOpCode #[ty] #[] #[] #[]
        (default : propertiesOf placeholderOpCode) none with
    | none => throwAt loc "internal error: failed to create forward-reference placeholder"
    | some (ctx', op) => pure (op, ctx')

/--
  Replace every use of a placeholder operation's single result with `target`, then erase
  the (now unused, region-less) placeholder operation.
-/
def rewirePlaceholder (placeholderOp : OperationPtr) (target : ValuePtr) : MlirParserM Unit := do
  let placeholderValue : ValuePtr := placeholderOp.getResult 0
  modifyContextM fun ctx => do
    let ⟨hOldIn⟩ ← checkValueInBounds placeholderValue ctx.raw
    let ⟨hNewIn⟩ ← checkValueInBounds target ctx.raw
    let ⟨hNe⟩ ← checkValuesNe placeholderValue target
    pure (WfRewriter.replaceValue ctx placeholderValue target hNe hOldIn hNewIn)
  modifyContextM fun ctx => do
    let ⟨hOpIn⟩ ← checkOpInBounds placeholderOp ctx.raw
    let ⟨hNoRegions⟩ ← checkOpNoRegions placeholderOp ctx.raw
    let ⟨hNoUses⟩ ← checkOpNoUses placeholderOp ctx.raw
    pure (WfRewriter.eraseOp ctx placeholderOp hNoRegions hNoUses hOpIn)

/--
  Modify the (scope-wide) forward-reference table.
-/
def modifyForwardValues
    (f : Std.HashMap ByteArray ForwardValue → Std.HashMap ByteArray ForwardValue) : MlirParserM Unit :=
  modify fun s => { s with forwardValues := f s.forwardValues }

/--
  Resolve a forward-referenced value now that its real definition has been parsed. For each
  referenced result index, replace all uses of the placeholder result with the corresponding
  real value and erase the placeholder operation.
-/
def resolveForwardValue (name : ByteArray) (pos : Location) (fwd : ForwardValue)
    (values : Array ValuePtr) : MlirParserM Unit := do
  for (index, (placeholderOp, useLoc)) in fwd.placeholders do
    let some realValue := values[index]?
      | throw (({ msg := s!"definition of value %{String.fromUTF8! name} provides {values.size} results, but result #{index} was used",
                  pos := some pos } : ParserError).addNote useLoc "value used here")
    /- The value has a single type, so the definition must match every use. -/
    let placeholderValue : ValuePtr := placeholderOp.getResult 0
    let ⟨ctx, _⟩ ← getContext
    let usedType := placeholderValue.getType! ctx
    let definedType := realValue.getType! ctx
    if usedType ≠ definedType then
      throw (({ msg := s!"definition of value %{String.fromUTF8! name}#{index} has type {definedType} but was used with type {usedType}",
                pos := some pos } : ParserError).addNote useLoc "value used here")
    rewirePlaceholder placeholderOp realValue
  modifyForwardValues (·.erase name)

/--
  Register an array of parsed values with the given name in the current scope.
  This is used to keep track of values that have been defined during parsing.
  If the name was forward-referenced earlier, the placeholders created for it are resolved to
  the newly-parsed values (following MLIR: the first definition of a name resolves it).
-/
def registerValueDefs (name : ByteArray) (pos : Location) (values : Array ValuePtr) : MlirParserM Unit := do
  let st ← get
  if let some fwd := st.forwardValues[name]? then
    resolveForwardValue name pos fwd values
  if let some (_, existingPos) := (← get).values[name]? then
    let error := ParserError.mk s!"value %{String.fromUTF8! name} has already been defined" pos []
    let error := error.addNote existingPos "previously defined here"
    throw error
  modify fun s =>
    { s with
      values := s.values.insert name (values, pos)
      definitionsPerScope := s.definitionsPerScope.modify (s.definitionsPerScope.size - 1) (·.insert name)
    }

/--
  Register a single value with the given name in current scope.
  This is used to keep track of values that have been defined during parsing.
-/
def registerValueDef (name : ByteArray) (pos : Location) (value : ValuePtr) : MlirParserM Unit :=
  registerValueDefs name pos #[value]

/--
  Create a block at the given insert point and register its name in the parsing context.
  If a block was already declared with the given name, use that block instead, and
  insert it at the given insert point.
-/
def defineBlock (name : ByteArray) (ip : BlockInsertPoint) (loc : Location) : MlirParserM BlockPtr := do
  let state ← get
  match state.blocks[name]? with
  | some (.Defined block prevLoc) => -- Block of this name is already defined.
    throw (({ msg := s!"block %{String.fromUTF8! name} has already been defined",
              pos := some loc } : ParserError).addNote prevLoc "block previously defined here")
  | some (.ForwardDeclared block _) => -- Block of this name was forward declared.
    /- Insert the block at the given location. -/
    modifyContextM fun ctx => do
      let ⟨hip⟩ ← checkBlockInsertPointInBounds ip ctx.raw
      let ⟨hblock⟩ ← checkBlockInBounds block ctx.raw
      match hctx' : Rewriter.insertBlock ctx block ip hblock hip with
      | none => throwAt loc "internal error: failed to insert block"
      | some ctx' => pure ⟨ctx', by grind [Rewriter.insertBlock_WellFormed]⟩
    /- Notify the parsing context that the block is defined. -/
    modifyThe MlirParserState (fun state =>
    {state with
      blocks :=
        state.blocks.insert name (.Defined block loc)})
    return block
  | none => -- Block has not yet been declared or referenced.
    /- Create the block. -/
    let block ← modifyContextM' fun ctx => do
      let ⟨hip⟩ ← checkBlockInsertPointInBounds ip ctx.raw
      match hctx' : Rewriter.createBlock ctx #[] ip (by grind) (by grind) with
      | none => throwAt loc "internal error: failed to create block"
      | some (ctx', block) => pure ⟨block, ⟨ctx', by grind [Rewriter.createBlock_WellFormed]⟩⟩
    /- Notify the parsing context that the block is defined. -/
    modifyThe MlirParserState fun s =>
    {s with blocks := s.blocks.insert name (.Defined block loc)}
    return block

/--
  Forward declare a block with the given name.
  If the block was already forward declared or defined, return the existing block.
  Otherwise, create a new block without inserting it in a region.
-/
def defineBlockUse (name : ByteArray) (loc : Location) : MlirParserM BlockPtr := do
  let state ← get
  match state.blocks[name]? with
  | some entry => -- Block already defined or forward declared
    return entry.block
  | none => -- Block not yet encountered
    /- Create the block. -/
    let block ← modifyContextM' fun ctx => do
      match hctx' : Rewriter.createBlock ctx #[] none (by grind) Option.maybe_none with
      | none => throwAt loc "internal error: failed to create block"
      | some (ctx', block) => pure ⟨block, ⟨ctx', by grind [Rewriter.createBlock_WellFormed]⟩⟩
    /- Notify the parsing context that the block is forward declared. -/
    modifyThe MlirParserState fun s =>
      {s with blocks := s.blocks.insert name (.ForwardDeclared block loc)}
    return block

/--
  Parse an operation result and the number of values it defines.
  This corresponds to the syntax `%name` and `%name:numberOfResults`.
-/
def parseOpResult : MlirParserM (ByteArray × Nat × Location) := do
  let nameToken ← parseToken .percentIdent "operation result expected"
  let tokenPos := nameToken.slice.start
  let slice := { nameToken.slice with start := nameToken.slice.start + 1 } -- skip % character
  let name := slice.of (← getInput)

  /- If the next token is ':', we parse the expected result count, otherwise we return the name. -/
  if !(← parseOptionalToken .colon).isSome then
    return (name, 1, tokenPos)

  let count := (← parseInteger false false).toNat
  if count ≤ 1 then
    throwAt tokenPos "expected named operation to have at least 1 result"

  return (name, count, tokenPos)

/--
  Parse the results before an operation definition,
  either as a list of values followed by '=', or nothing.
-/
def parseOpResults : MlirParserM (Array (ByteArray × Nat × Location)) := do
  let .percentIdent := (← peekToken).kind | return #[]
  let results ← parseList parseOpResult
  parsePunctuation "=" "'=' expected after operation results"
  return results

/--
  An operand whose type has not yet been resolved.
  This is used during parsing to allow parsing operands before their types.
  Once the operation type is known, `resolveOperand` can be used to create an SSA value and
  check that the type matches with previous uses.

  `index` is used for the `%name#index` syntax to refer to an indexed result
  when multiple are defined for the same value.
-/
structure UnresolvedOperand where
  name : ByteArray
  index : Option Nat
  pos : Location

/--
  Get the name of an UnresolvedOperand as a String.
-/
def UnresolvedOperand.nameString (operand : UnresolvedOperand) : String :=
  String.fromUTF8! operand.name

/--
  Get the result index of an UnresolvedOperand. If one was not specified explicitly, this
  defaults to 0.
-/
def UnresolvedOperand.indexD (operand : UnresolvedOperand) : Nat :=
  operand.index.getD 0

instance : ToString UnresolvedOperand where
  toString operand :=
    match operand.index with
    | none => s!"%{operand.nameString}"
    | some n => s!"%{operand.nameString}#{n}"

/--
  Parse an operation operand.
  This has the syntax `%name` or `%name#resultCount`.
-/
def parseOperand : MlirParserM UnresolvedOperand := do
  let nameToken ← parseToken .percentIdent "operand expected"
  let tokenPos := nameToken.slice.start
  let name : ByteArray := { nameToken.slice with start := nameToken.slice.start + 1 }.of (← getInput)

  /- If no result number is specified, return without one. -/
  let some resultCount ← parseOptionalToken .hashIdent
    | return UnresolvedOperand.mk name none tokenPos

  /- Parse the result count as a Nat. -/
  let hashPos := resultCount.slice.start
  let resultCount := { resultCount.slice with start := resultCount.slice.start + 1 }.of (← getInput) -- skip # character
  let some resultCount := String.fromUTF8? resultCount >>= String.toNat?
    | throwAt hashPos "invalid SSA value result number"
  return UnresolvedOperand.mk name resultCount tokenPos

/--
  Parse a list of operation operands delimited by parentheses.
-/
def parseOperands : MlirParserM (Array UnresolvedOperand) := do
  parseDelimitedList .paren parseOperand

/--
  Parse a list of block operands delimited by square brackets, if present.
-/
def parseBlockOperand : MlirParserM BlockPtr := do
  let labelToken ← parseToken .caretIdent "block name expected"
  let slice := { labelToken.slice with start := labelToken.slice.start + 1 } -- skip ^ character
  let name := slice.of (← getInput)
  let block ← defineBlockUse name labelToken.slice.start
  return block

/--
  Parse a single block operand.
-/
def parseBlockOperands : MlirParserM (Array BlockPtr) := do
  return (← parseOptionalDelimitedList .square parseBlockOperand).getD #[]

/--
  Resolve a reference to a value that has not yet been defined by creating (or reusing)
  a placeholder operation whose result stands in for the eventual definition.
  The placeholder is recorded in the flat forward-reference table and resolved by the first
  definition of the name, wherever it later appears (as in MLIR's generic-form parser).
-/
def resolveForwardOperand (operand : UnresolvedOperand) (expectedType : TypeAttr) : MlirParserM ValuePtr := do
  let idx := operand.indexD
  match (← get).forwardValues[operand.name]? with
  | some fwd =>
    match fwd.placeholders[idx]? with
    | some (placeholderOp, useLoc) =>
      /- The same result index was referenced before: reuse its placeholder and
         check the type is consistent with the previous use. -/
      let placeholderValue : ValuePtr := placeholderOp.getResult 0
      let ⟨ctx, _⟩ ← getContext
      let parsedType := placeholderValue.getType! ctx
      if parsedType ≠ expectedType then
        throw (({ msg := s!"type mismatch for value {operand}: expected {expectedType}, got {parsedType}",
                  pos := some operand.pos } : ParserError).addNote useLoc "value first used here")
      return placeholderValue
    | none =>
      /- A new result index of an already forward-referenced value. -/
      let placeholderOp ← createForwardRefPlaceholder expectedType operand.pos
      modifyForwardValues (·.insert operand.name
        { fwd with
          placeholders := fwd.placeholders.insert idx (placeholderOp, operand.pos) })
      return placeholderOp.getResult 0
  | none =>
    /- First reference of a not-yet-defined value. -/
    let placeholderOp ← createForwardRefPlaceholder expectedType operand.pos
    modifyForwardValues (·.insert operand.name
      { placeholders := (Std.HashMap.emptyWithCapacity 1).insert idx (placeholderOp, operand.pos),
        loc := operand.pos })
    return placeholderOp.getResult 0

/--
  Resolve an operand to an SSA value of the expected type.
  If the value has not yet been defined, a forward-reference placeholder is created;
  it will be resolved when the definition is parsed, or reported as an error once
  top-level parsing finishes if the value is never defined.
-/
def resolveOperand (operand : UnresolvedOperand) (expectedType : TypeAttr) : MlirParserM ValuePtr := do
  let some (values, defPos) := (← getValues? operand.name)
    | resolveForwardOperand operand expectedType
  let some value := values[operand.indexD]?
    | throw (({ msg := s!"invalid result index {operand.indexD} for %{operand.nameString}",
                pos := some operand.pos } : ParserError).addNote defPos "value defined here")
  let ⟨ctx, _⟩ ← getContext
  let parsedType := value.getType! ctx
  if parsedType ≠ expectedType then
    throw (({ msg := s!"type mismatch for value {operand}: expected {expectedType}, got {parsedType}",
              pos := some operand.pos } : ParserError).addNote defPos "value defined here")
  return value

/--
  Parse a type, if present.
-/
def parseOptionalType : MlirParserM (Option TypeAttr) := do
  let allowUnregisteredDialect := (← get).allowUnregisteredDialect
  match AttrParser.parseOptionalType.run { allowUnregisteredDialect } (← getThe ParserState) with
  | .ok (ty, _, parserState) =>
    set parserState
    return ty
  | .error err => throw err

/--
  Parse a type, otherwise return an error.
-/
def parseType (errorMsg : String := "type expected") : MlirParserM TypeAttr := do
  match ← parseOptionalType with
  | some ty => return ty
  | none => throwAtCurrentPos errorMsg

/--
  Parse an operation type, consisting of a colon followed by a function type.
-/
def parseOperationType : MlirParserM (Array TypeAttr × Array TypeAttr) := do
  parsePunctuation ":"
  let inputs ← parseDelimitedList .paren parseType
  parsePunctuation "->"
  if (←peekToken).kind = .lParen then
    let outputs ← parseDelimitedList .paren parseType
    return (inputs, outputs)
  else
    let outputType ← parseType
    return (inputs, #[outputType])

/--
  Parse an SSA value followed by a colon and a type, if present.
  Also returns the location of the value definition.
-/
def parseTypedValue : MlirParserM (ByteArray × TypeAttr × Location) := do
  let nameToken ← parseToken .percentIdent "value expected"
  let tokenPos := nameToken.slice.start
  let slice := { nameToken.slice with start := nameToken.slice.start + 1 } -- skip % character
  let name := slice.of (← getInput)
  parsePunctuation ":"
  let ty ← parseType
  return (name, ty, tokenPos)

/--
  Parse the properties of an operation.
  Currently, these properties are not stored in the IR, but we still need to parse them to be able
  to parse valid MLIR syntax.
-/
def parseOpProperties (opCode : OpCode) : MlirParserM (propertiesOf opCode) := do
  let propertiesStart ← getPos
  if not (← parseOptionalPunctuation "<") then
    match Properties.fromAttrDict opCode {} with
    | .ok properties => return properties
    | .error err => throwAtCurrentPos err
  let allowUnregisteredDialect := (← get).allowUnregisteredDialect
  match AttrParser.parseAttributeDictionary.run { allowUnregisteredDialect } (← getThe ParserState) with
  | .ok (properties, _, parserState) =>
    set parserState
    parsePunctuation ">"
    match Properties.fromAttrDict opCode (.ofArray properties) with
    | .ok properties => return properties
    | .error err => throwAt propertiesStart err
  | .error err => throw err

/--
  Parse the attributes of an operation, if present.
  Currently, these attributes are not stored in the IR, but we still need to parse them to be able
  to parse valid MLIR syntax.
-/
def parseOpAttributes : MlirParserM DictionaryAttr := do
  match AttrParser.parseOptionalAttributeDictionary.run { allowUnregisteredDialect := (← get).allowUnregisteredDialect } (← getThe ParserState) with
  | .ok (attrs, _, parserState) =>
    set parserState
    match attrs with
    | none => return DictionaryAttr.empty
    | some attrs => return DictionaryAttr.fromArray attrs
  | .error err => throw err

/--
  Parse a block label, if present, and create and insert the block at the given insert point.
-/
def parseOptionalBlockLabel (ip : BlockInsertPoint) : MlirParserM (Option BlockPtr) := do
  /- Parse the block name. -/
  let some labelToken ← parseOptionalToken .caretIdent
    | return none
  let slice := { labelToken.slice with start := labelToken.slice.start + 1 } -- skip ^ character
  let name := slice.of (← getInput)
  /- Parse the arguments. -/
  let arguments := (← parseOptionalDelimitedList .paren parseTypedValue).getD #[]
  parsePunctuation ":" "':' expected after block label"
  /- Create the block or get it if it was forward declared. -/
  let block ← defineBlock name ip labelToken.slice.start
  /- Insert block arguments in the block. -/
  modifyContextM fun ctx => do
    let argTypes := arguments.map (·.2.1)
    let ⟨h_block_InBounds⟩ ← checkBlockInBounds block ctx.raw
    let ⟨h_block_NoArgs⟩ ← checkBlockHasNoArgs block ctx.raw
    pure (WfRewriter.setBlockArguments ctx block argTypes h_block_InBounds (by grind [BlockPtr.getArguments!.mem_iff_exists_index]))
  /- Register the block argument names in the parser state. -/
  for ((argName, _argType, tokenPos), index) in arguments.zipIdx do
    registerValueDef argName tokenPos (ValuePtr.blockArgument {block := block, index := index})
  return some block

/--
  Parse the label of an entry block and create and insert the block at the given insert point.
  Since the entry block does not need a label, if no label is found,
  a block with an empty name is created and returned.
-/
def parseEntryBlockLabel (ip : BlockInsertPoint) : MlirParserM BlockPtr := do
  /- Try to parse a block label. -/
  if let some block ← parseOptionalBlockLabel ip then
    return block
  else -- Otherwise, create a block with an empty name.
    let block ← defineBlock ByteArray.empty ip (← getPos)
    return block

mutual

/--
  Parse the regions of an operation.
-/
partial def parseOpRegions : MlirParserM (Array RegionPtr) := do
  return (← parseOptionalDelimitedList .paren parseRegion).getD #[]

/--
  Parse an operation, if present, and insert it at the given insert point.
-/
partial def parseOptionalOp (ip : Option InsertPoint) : MlirParserM (Option OperationPtr) := do
  /- Parse the operation. -/
  let results ← parseOpResults
  let opNameStart ← getPos
  let some opName ← parseOptionalStringLiteral | return none
  let some opNameStr := String.fromUTF8? opName
    | throwAt opNameStart s!"op '{escapeStringLiteral opName}' not a valid UTF8 string."
  let operands ← parseOperands
  let blockOperands ← parseBlockOperands

  /- Get the operation opcode. -/
  let opId := OpCode.fromName opName

  if let .builtin .unregistered := opId then
    if !(← get).allowUnregisteredDialect then
      throwAt opNameStart
        s!"op '{opNameStr}' is not registered. Consider using --allow-unregistered-dialect."

  let properties ← parseOpProperties opId
  /- For `builtin.unregistered`, record the original op name in the properties so it can be
     printed back out. The properties dictionary itself has already been populated by
     `Properties.fromAttrDict` (see `UnregisteredProperties.fromAttrDict`). -/
  let properties : propertiesOf opId := match opId, properties with
    | .builtin .unregistered, props => { props with opName := opName }
    | _, props => props
  let regions ← parseOpRegions
  let attrs ← parseOpAttributes
  let (inputTypes, outputTypes) ← parseOperationType

  /- Results can have multiple parts so sum the sizes. -/
  let numResults := results.foldl (· + ·.2.1) 0

  /- Check that the number of results matches with the operation type. -/
  if outputTypes.size ≠ numResults then
    throwAt opNameStart s!"operation '{opNameStr}' declares {outputTypes.size} result types, but {numResults} result values were provided"

  /- Check that the number and types of operands matches with the operation type. -/
  if inputTypes.size ≠ operands.size then
    throwAt opNameStart s!"operation '{opNameStr}' declares {inputTypes.size} operand types, but {operands.size} operands were provided"
  let operands ← operands.zip inputTypes |>.mapM (fun (operand, type) => resolveOperand operand type)

  let op ← modifyContextM' fun ctx => do
    let ⟨hoper⟩ ← checkAllValuesInBounds operands ctx.raw
    let ⟨hblockOperands⟩ ← checkAllBlocksInBounds blockOperands ctx.raw
    let ⟨hregions⟩ ← checkAllRegionsInBounds regions ctx.raw
    let ⟨hins⟩ ← checkMaybeInsertPointInBounds ip ctx.raw
    match hctx' : Rewriter.createOp ctx opId outputTypes operands blockOperands regions properties ip hoper hblockOperands hregions hins with
    | none => throwAt opNameStart "internal error: failed to create operation"
    | some (ctx', op) =>
      have hop : op.InBounds ctx' := Rewriter.createOp_new_inBounds op hctx'
      let ctx'' := op.setAttributes ctx' attrs hop
      /- Update the parser context. -/
      pure ⟨op, ⟨ctx'', by grind [Rewriter.createOp_WellFormed, OperationPtr.setAttributes_WellFormed]⟩⟩

  let ctx ← getContext

  /- Register the values for each result name. -/
  let mut index := 0
  for (name, count, tokenPos) in results do
    let values := .ofFn <| fun (i : Fin count) => op.getResult (index + i)
    registerValueDefs name tokenPos values
    index := index + count
  return op

/--
  Parse a region.
-/
partial def parseRegion : MlirParserM RegionPtr := do
  /- Ensure variables defined in this region do not leak out of it. -/
  inChildScope do

  /- Reset the block parsing state, as blocks are local to regions. -/
  let oldBlocks := (← getThe MlirParserState).blocks
  modifyThe MlirParserState fun s => {s with blocks := Std.HashMap.emptyWithCapacity 1}

  /- Create the region and parse the open delimiter. -/
  parsePunctuation "{"
  let region := ← modifyContextM' fun ctx => do
    match hctx' : Rewriter.createRegion ctx with
    | none => throwAtCurrentPos "internal error: failed to create region"
    | some (ctx', region) => pure (region, ⟨ctx', by grind [IRContext.wellFormed_Rewriter_createRegion]⟩)

  /- Case where there are no blocks inside the region. -/
  if (← parseOptionalPunctuation "}") then
    return region

  /- Parse the first block separately, as it may not have a label. -/
  let _ ← parseEntryBlock (BlockInsertPoint.atEnd region)
  /- Parse the following blocks. -/
  while true do
    if (← parseOptionalBlock (BlockInsertPoint.atEnd region)) = none then
      break

  /- Parse the closing delimiter. -/
  parsePunctuation "}"

  /- Check that all blocks in the regions that were forward declared were parsed. -/
  for (blockName, entry) in (← getThe MlirParserState).blocks do
    if let .ForwardDeclared _ forwardLoc := entry then
      throwAt forwardLoc s!"block %{String.fromUTF8! blockName} was used but never defined"

  /- Restore the previous block parsing state. -/
  modifyThe MlirParserState fun s => {s with blocks := oldBlocks}
  return region

/--
  Parse the entry block and insert it into the given region.
  Compared to a normal block, the entry block does not need a label.
-/
partial def parseEntryBlock (ip : BlockInsertPoint) : MlirParserM BlockPtr := do
  let block ← parseEntryBlockLabel ip
  while true do
    if (← parseOptionalOp (InsertPoint.atEnd block)) = none then
      break
  return block

/--
  Parse a block and insert it at the given block insert point.
-/
partial def parseOptionalBlock (ip : BlockInsertPoint) : MlirParserM (Option BlockPtr) := do
  let some block ← parseOptionalBlockLabel ip
    | return none
  while true do
    if (← parseOptionalOp (InsertPoint.atEnd block)) == none then
      break
  return block

end

/--
  Parse an operation.
-/
private def parseOp (ip : Option InsertPoint) : MlirParserM OperationPtr := do
  let some op ← parseOptionalOp ip | throwAtCurrentPos "operation expected"
  return op

/-- Check that all SSA values forward referenced while parsing were eventually defined. -/
def checkNoUnresolvedForwardValues : MlirParserM Unit := do
  for (valueName, fwd) in (← get).forwardValues do
    throwAt fwd.loc s!"use of undefined value %{String.fromUTF8! valueName}"

/-- Parse a top-level operation and report any unresolved SSA forward references. -/
partial def parseTopLevelOp : MlirParserM OperationPtr := do
  let op ← parseOp none
  checkNoUnresolvedForwardValues
  return op

end Veir.Parser
