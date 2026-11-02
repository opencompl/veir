module

public import Veir.Parser.AttrParser
public import Veir.Parser.BuffedIR

public section

open Veir.Parser.Lexer
open Veir.Parser
open Veir.AttrParser

namespace Veir.Parser

open Veir.Parser.ParserError

/--
  The state of a block encountered during parsing.
  A block is either `Defined` (its label has been parsed) or `ForwardDeclared`
  (it has only been referenced, e.g., as a block operand, but not yet defined).
-/
inductive BlockEntry where
  | Defined (block : IR.Block) (loc : Location)
  | ForwardDeclared (block : IR.Block) (loc : Location)
  deriving Inhabited

/-- Get the block pointer of a `BlockEntry`, regardless of its state. -/
def BlockEntry.block : BlockEntry → IR.Block
  | .Defined block _ => block
  | .ForwardDeclared block _ => block

/--
  Bookkeeping for an SSA value referenced before it is defined (a "forward reference").

  Following MLIR's generic-form parser, the name table is flat across all regions: a forward
  reference is resolved by the first textual definition of the name, wherever it appears. Each
  referenced result index holds a detached single-result placeholder operation standing in for
  the value; when the definition is parsed, all uses of each placeholder are replaced by the
  real value and the placeholder is erased.

  Whether such a reference is actually legal (dominance, `IsolatedFromAbove`) is a verifier
  concern that MLIR checks after parsing; we likewise leave it to a later verification pass and
  only report values that are never defined anywhere.

  This mirrors MLIR's approach that uses a throwaway operation result as the placeholder
  (specifically `unrealized_conversion_cast`).
-/
structure ForwardValue where
  /-- Placeholder operation per referenced result index, with that index's first-use location. -/
  placeholders : Std.HashMap Nat (IR.Op × Location)
  /-- Location of the first use, used for error reporting if the value is never defined. -/
  loc : Location
  deriving Inhabited

structure MlirParserState where
  /-- The current IR context. -/
  ctx : IR.Context
  /-- The values that have been defined for a given name at that point in the parser,
      along with the byte offset of where the value name token was parsed. -/
  values : Std.HashMap ByteArray (Array IR.Value × Location)
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
  /-- Type aliases defined so far, keyed by name without the `!`. -/
  typeAliases : Std.HashMap ByteArray TypeAttr := {}
  /-- The location of each parsed operation. -/
  opLocations : Std.HashMap Buffed.OperationMPtr Location := {}
  deriving Inhabited

def MlirParserState.fromContext (ctx : IR.Context)
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
  (mlirParserState : MlirParserState) (parserState: ParserState) :
    Except ParserError (α × MlirParserState × ParserState) :=
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
def getContext : MlirParserM IR.Context := do
  return (← get).ctx

/--
  Get the array of values associated with a previously parsed name.
-/
def getValues? (name : ByteArray) : MlirParserM (Option (Array IR.Value × Location)) := do
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
def setContext (ctx : IR.Context) : MlirParserM Unit := do
  modify fun s => {s with ctx := ctx}

/--
  Modifies the current IR context.

  This function should be used instead of modifying the context with
  `get`/`getContext` and `set`/`setContext` in order to preserve linearity: the context is
  taken out of the state before `f` runs, so the buffer is uniquely referenced and updated in
  place.
-/
@[inline]
def modifyContextM' (f : IR.Context → MlirParserM (α × IR.Context)) : MlirParserM α := do
  let ctx ← modifyGet fun s => (s.ctx, { s with ctx := default })
  let (r, ctx) ← f ctx
  setContext ctx
  pure r

/--
  Modifies the current IR context, preserving linearity (see `modifyContextM'`).
-/
@[inline]
def modifyContextM (f : IR.Context → MlirParserM IR.Context) : MlirParserM Unit :=
  modifyContextM' (fun ctx => do pure ((), ← f ctx))

/--
  Create a detached, single-result placeholder operation of the given type.
  Its result is used to stand in for a value that has been referenced but not yet
  defined. The operation is not inserted into any block; once the real definition is
  parsed, `resolveForwardValue` replaces all uses of this result with the real value
  and erases this operation.
-/
def createForwardRefPlaceholder (ty : TypeAttr) (loc : Location) : MlirParserM IR.Op :=
  modifyContextM' fun ctx => do
    match IR.createOp ctx (.builtin .unrealized_conversion_cast) #[ty] #[] #[] #[] () none with
    | none => throwAt loc "internal error: failed to create forward-reference placeholder"
    | some (ctx', op) => pure (op, ctx')

/--
  Replace every use of a placeholder operation's single result with `target`, then erase
  the (now unused, region-less) placeholder operation.
-/
def rewirePlaceholder (placeholderOp : IR.Op) (target : IR.Value) (loc : Location) :
    MlirParserM Unit := do
  modifyContextM fun ctx => do
    let placeholderValue := IR.opResult ctx placeholderOp 0
    let some ctx := IR.replaceValue ctx placeholderValue target
      | throwAt loc "internal error: failed to replace the uses of a forward-reference placeholder"
    pure (IR.eraseOp ctx placeholderOp)

/--
  Modify the (scope-wide) forward-reference table.
-/
def modifyForwardValues
    (f : Std.HashMap ByteArray ForwardValue → Std.HashMap ByteArray ForwardValue) :
    MlirParserM Unit :=
  modify fun s => { s with forwardValues := f s.forwardValues }

/--
  Resolve a forward-referenced value now that its real definition has been parsed. For each
  referenced result index, replace all uses of the placeholder result with the corresponding
  real value and erase the placeholder operation.
-/
def resolveForwardValue (name : ByteArray) (pos : Location) (fwd : ForwardValue)
    (values : Array IR.Value) : MlirParserM Unit := do
  for (index, (placeholderOp, useLoc)) in fwd.placeholders do
    let some realValue := values[index]?
      | throw (({ msg := s!"definition of value %{String.fromUTF8! name} provides {values.size} results, but result #{index} was used",
                  pos := some pos } : ParserError).addNote useLoc "value used here")
    /- The value has a single type, so the definition must match every use. -/
    let ctx ← getContext
    let usedType := IR.valueType ctx (IR.opResult ctx placeholderOp 0)
    let definedType := IR.valueType ctx realValue
    if usedType ≠ definedType then
      throw (({ msg := s!"definition of value %{String.fromUTF8! name}#{index} has type {definedType} but was used with type {usedType}",
                pos := some pos } : ParserError).addNote useLoc "value used here")
    rewirePlaceholder placeholderOp realValue pos
  modifyForwardValues (·.erase name)

/--
  Register an array of parsed values with the given name in the current scope.
  This is used to keep track of values that have been defined during parsing.
  If the name was forward-referenced earlier, the placeholders created for it are resolved to
  the newly-parsed values (following MLIR: the first definition of a name resolves it).
-/
def registerValueDefs (name : ByteArray) (pos : Location) (values : Array IR.Value) :
    MlirParserM Unit := do
  if let some fwd := (← get).forwardValues[name]? then
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
def registerValueDef (name : ByteArray) (pos : Location) (value : IR.Value) :
    MlirParserM Unit :=
  registerValueDefs name pos #[value]

/--
  Create a block with the given argument types at the given insert point and register its name
  in the parsing context.
  If a block was already forward declared with the given name, it is inserted at the given
  insert point instead. As the argument capacity of a block is fixed when it is allocated, a
  forward-declared block that turns out to have arguments is replaced by a fresh block: the uses
  of the placeholder are redirected to the new block, and the placeholder is erased.
-/
def defineBlock (name : ByteArray) (argTypes : Array TypeAttr) (ip : BlockInsertPoint)
    (loc : Location) : MlirParserM IR.Block := do
  let state ← get
  match state.blocks[name]? with
  | some (.Defined _ prevLoc) => -- Block of this name is already defined.
    throw (({ msg := s!"block %{String.fromUTF8! name} has already been defined",
              pos := some loc } : ParserError).addNote prevLoc "block previously defined here")
  | some (.ForwardDeclared placeholder _) => -- Block of this name was forward declared.
    let block ← modifyContextM' fun ctx => do
      if argTypes.isEmpty then
        /- Insert the placeholder block at the given location. -/
        let some ctx := IR.insertBlock ctx placeholder ip
          | throwAt loc "internal error: failed to insert block"
        pure (placeholder, ctx)
      else
        /- Create the block with its arguments, and redirect the uses of the placeholder. -/
        let some (ctx, block) := IR.createBlock ctx argTypes (some ip)
          | throwAt loc "internal error: failed to create block"
        let ctx := IR.replaceBlockUses ctx placeholder block
        pure (block, IR.eraseBlock ctx placeholder)
    /- Notify the parsing context that the block is defined. -/
    modify fun state => { state with blocks := state.blocks.insert name (.Defined block loc) }
    return block
  | none => -- Block has not yet been declared or referenced.
    /- Create the block. -/
    let block ← modifyContextM' fun ctx => do
      match IR.createBlock ctx argTypes (some ip) with
      | none => throwAt loc "internal error: failed to create block"
      | some (ctx', block) => pure (block, ctx')
    /- Notify the parsing context that the block is defined. -/
    modify fun s => {s with blocks := s.blocks.insert name (.Defined block loc)}
    return block

/--
  Forward declare a block with the given name.
  If the block was already forward declared or defined, return the existing block.
  Otherwise, create a new block without inserting it in a region.
-/
def defineBlockUse (name : ByteArray) (loc : Location) : MlirParserM IR.Block := do
  let state ← get
  match state.blocks[name]? with
  | some entry => -- Block already defined or forward declared
    return entry.block
  | none => -- Block not yet encountered
    /- Create the block. -/
    let block ← modifyContextM' fun ctx => do
      match IR.createBlock ctx #[] none with
      | none => throwAt loc "internal error: failed to create block"
      | some (ctx', block) => pure (block, ctx')
    /- Notify the parsing context that the block is forward declared. -/
    modify fun s => {s with blocks := s.blocks.insert name (.ForwardDeclared block loc)}
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
  Parse a single block operand.
-/
def parseBlockOperand : MlirParserM IR.Block := do
  let labelToken ← parseToken .caretIdent "block name expected"
  let slice := { labelToken.slice with start := labelToken.slice.start + 1 } -- skip ^ character
  let name := slice.of (← getInput)
  let block ← defineBlockUse name labelToken.slice.start
  return block

/--
  Parse a list of block operands delimited by square brackets, if present.
-/
def parseBlockOperands : MlirParserM (Array IR.Block) := do
  return (← parseOptionalDelimitedList .square parseBlockOperand).getD #[]

/--
  Resolve a reference to a value that has not yet been defined by creating (or reusing)
  a placeholder operation whose result stands in for the eventual definition.
  The placeholder is recorded in the flat forward-reference table and resolved by the first
  definition of the name, wherever it later appears (as in MLIR's generic-form parser).
-/
def resolveForwardOperand (operand : UnresolvedOperand) (expectedType : TypeAttr) :
    MlirParserM IR.Value := do
  let idx := operand.indexD
  match (← get).forwardValues[operand.name]? with
  | some fwd =>
    match fwd.placeholders[idx]? with
    | some (placeholderOp, useLoc) =>
      /- The same result index was referenced before: reuse its placeholder and
         check the type is consistent with the previous use. -/
      let ctx ← getContext
      let placeholderValue := IR.opResult ctx placeholderOp 0
      let parsedType := IR.valueType ctx placeholderValue
      if parsedType ≠ expectedType.val then
        throw (({ msg := s!"type mismatch for value {operand}: expected {expectedType}, got {parsedType}",
                  pos := some operand.pos } : ParserError).addNote useLoc "value first used here")
      return placeholderValue
    | none =>
      /- A new result index of an already forward-referenced value. -/
      let placeholderOp ← createForwardRefPlaceholder expectedType operand.pos
      modifyForwardValues (·.insert operand.name
        { fwd with
          placeholders := fwd.placeholders.insert idx (placeholderOp, operand.pos) })
      return IR.opResult (← getContext) placeholderOp 0
  | none =>
    /- First reference of a not-yet-defined value. -/
    let placeholderOp ← createForwardRefPlaceholder expectedType operand.pos
    modifyForwardValues (·.insert operand.name
      { placeholders := (Std.HashMap.emptyWithCapacity 1).insert idx (placeholderOp, operand.pos),
        loc := operand.pos })
    return IR.opResult (← getContext) placeholderOp 0

/--
  Resolve an operand to an SSA value of the expected type.
  If the value has not yet been defined, a forward-reference placeholder is created;
  it will be resolved when the definition is parsed, or reported as an error once
  top-level parsing finishes if the value is never defined.
-/
def resolveOperand (operand : UnresolvedOperand) (expectedType : TypeAttr) :
    MlirParserM IR.Value := do
  let some (values, defPos) := (← getValues? operand.name)
    | resolveForwardOperand operand expectedType
  let some value := values[operand.indexD]?
    | throw (({ msg := s!"invalid result index {operand.indexD} for %{operand.nameString}",
                pos := some operand.pos } : ParserError).addNote defPos "value defined here")
  let parsedType := IR.valueType (← getContext) value
  if parsedType ≠ expectedType.val then
    throw (({ msg := s!"type mismatch for value {operand}: expected {expectedType}, got {parsedType}",
              pos := some operand.pos } : ParserError).addNote defPos "value defined here")
  return value

/-- The attribute parser state derived from the current parser state. -/
def attrParserState : MlirParserM AttrParserState := do
  let state ← get
  return {
    allowUnregisteredDialect := state.allowUnregisteredDialect
    typeAliases := state.typeAliases
  }

/--
  Parse a type, if present.
-/
def parseOptionalType : MlirParserM (Option TypeAttr) := do
  match AttrParser.parseOptionalType.run (← attrParserState) (← getThe ParserState) with
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
  The integer literals in a `mod_arith` operation's properties are kept as written (see
  `AttrParserState.rawIntegerLiterals`).
-/
def parseOpProperties (opCode : OpCode) : MlirParserM (propertiesOf opCode) := do
  let propertiesStart ← getPos
  if not (← parseOptionalPunctuation "<") then
    match Properties.fromAttrDict opCode {} with
    | .ok properties => return properties
    | .error err => throwAtCurrentPos err
  let rawIntegerLiterals :=
    (String.fromUTF8! opCode.name).startsWith "mod_arith."
  let attrState := { (← attrParserState) with rawIntegerLiterals }
  match AttrParser.parseAttributeDictionary.run attrState (← getThe ParserState) with
  | .ok (properties, _, parserState) =>
    set parserState
    parsePunctuation ">"
    match Properties.fromAttrDict opCode (Std.HashMap.ofList properties.toList) with
    | .ok properties => return properties
    | .error err => throwAt propertiesStart err
  | .error err => throw err

/--
Record the source operation name in the properties of a `builtin.unregistered`
operation.
-/
private def optionallySetUnregisteredOpName (opCode : OpCode)
    (properties : propertiesOf opCode) (opName : ByteArray) :
    propertiesOf opCode :=
  match opCode, properties with
  | .builtin .unregistered, properties => UnregisteredProperties.mk opName properties.properties
  | _, properties => properties

/--
  Parse the attributes of an operation, if present.
-/
def parseOpAttributes : MlirParserM DictionaryAttr := do
  match AttrParser.parseOptionalAttributeDictionary.run (← attrParserState) (← getThe ParserState) with
  | .ok (attrs, _, parserState) =>
    set parserState
    match attrs with
    | none => return DictionaryAttr.empty
    | some attrs => return DictionaryAttr.fromArray attrs
  | .error err => throw err

/--
  Parse a block label, if present, and create and insert the block at the given insert point.
-/
def parseOptionalBlockLabel (ip : BlockInsertPoint) : MlirParserM (Option IR.Block) := do
  /- Parse the block name. -/
  let some labelToken ← parseOptionalToken .caretIdent
    | return none
  let slice := { labelToken.slice with start := labelToken.slice.start + 1 } -- skip ^ character
  let name := slice.of (← getInput)
  /- Parse the arguments. -/
  let arguments := (← parseOptionalDelimitedList .paren parseTypedValue).getD #[]
  parsePunctuation ":" "':' expected after block label"
  /- Create the block with its arguments, or get it if it was forward declared. -/
  let block ← defineBlock name (arguments.map (·.2.1)) ip labelToken.slice.start
  /- Register the block argument names in the parser state. -/
  for ((argName, _argType, tokenPos), index) in arguments.zipIdx do
    registerValueDef argName tokenPos (IR.blockArgument (← getContext) block index.toUInt64)
  return some block

/--
  Parse the label of an entry block and create and insert the block at the given insert point.
  Since the entry block does not need a label, if no label is found,
  a block with an empty name is created and returned.
-/
def parseEntryBlockLabel (ip : BlockInsertPoint) : MlirParserM IR.Block := do
  /- Try to parse a block label. -/
  if let some block ← parseOptionalBlockLabel ip then
    return block
  else -- Otherwise, create a block with an empty name.
    let block ← defineBlock ByteArray.empty #[] ip (← getPos)
    return block

mutual

/--
  Parse the regions of an operation.
-/
partial def parseOpRegions : MlirParserM (Array IR.Region) := do
  return (← parseOptionalDelimitedList .paren parseRegion).getD #[]

/--
  Parse an operation, if present, and insert it at the given insert point.
-/
partial def parseOptionalOp (ip : Option InsertPoint) : MlirParserM (Option IR.Op) := do
  /- Parse the operation. -/
  let opStart ← getPos
  let results ← parseOpResults
  let opNameStart ← getPos
  let some opName ← parseOptionalStringLiteral | return none
  let some opNameStr := String.fromUTF8? opName
    | throwAt opNameStart s!"op '{escapeStringLiteral (String.fromUTF8! opName)}' not a valid UTF8 string."
  let operands ← parseOperands
  let blockOperands ← parseBlockOperands

  /- Get the operation opcode. -/
  let opId := OpCode.fromName opName

  if opId = .builtin .unregistered then
    if !(← get).allowUnregisteredDialect then
      throwAt opNameStart
        s!"op '{opNameStr}' is not registered. Consider using --allow-unregistered-dialect."

  let properties ← parseOpProperties opId
  /- For `builtin.unregistered`, record the original op name in the properties so it can be
     printed back out. The properties dictionary itself has already been populated by
     `Properties.fromAttrDict` (see `UnregisteredProperties.fromAttrDict`). -/
  let properties := optionallySetUnregisteredOpName opId properties opName
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
    match IR.createOp ctx opId outputTypes operands blockOperands regions properties ip with
    | none => throwAt opNameStart "internal error: failed to create operation"
    | some (ctx, op) =>
      if attrs.entries.isEmpty then
        pure (op, ctx)
      else
        let some ctx := IR.setAttributes ctx op attrs
          | throwAt opNameStart "internal error: failed to set the operation attributes"
        pure (op, ctx)
  /- Record where the operation started for diagnostics. -/
  modify fun state => { state with opLocations := state.opLocations.insert op.impl opStart }

  /- Register the values for each result name. -/
  let ctx ← getContext
  let mut index := 0
  for (name, count, tokenPos) in results do
    let values := .ofFn <| fun (i : Fin count) => IR.opResult ctx op (index + i.val).toUInt64
    registerValueDefs name tokenPos values
    index := index + count
  return op

/--
  Parse a region.
-/
partial def parseRegion : MlirParserM IR.Region := do
  /- Ensure variables defined in this region do not leak out of it. -/
  inChildScope do

  /- Reset the block parsing state, as blocks are local to regions. -/
  let oldBlocks := (← get).blocks
  modify fun s => {s with blocks := Std.HashMap.emptyWithCapacity 1}

  /- Create the region and parse the open delimiter. -/
  parsePunctuation "{"
  let region ← modifyContextM' fun ctx => do
    match IR.createRegion ctx with
    | none => throwAtCurrentPos "internal error: failed to create region"
    | some (ctx', region) => pure (region, ctx')

  /- Case where there are no blocks inside the region. -/
  if (← parseOptionalPunctuation "}") then
    modify fun s => {s with blocks := oldBlocks}
    return region

  /- Parse the first block separately, as it may not have a label. -/
  let regionIp := BlockInsertPoint.atEnd ⟨region.impl.toNat⟩
  let _ ← parseEntryBlock regionIp
  /- Parse the following blocks. -/
  while true do
    if (← parseOptionalBlock regionIp).isNone then
      break

  /- Parse the closing delimiter. -/
  parsePunctuation "}"

  /- Check that all blocks in the regions that were forward declared were parsed. -/
  for (blockName, entry) in (← get).blocks do
    if let .ForwardDeclared _ forwardLoc := entry then
      throwAt forwardLoc s!"block %{String.fromUTF8! blockName} was used but never defined"

  /- Restore the previous block parsing state. -/
  modify fun s => {s with blocks := oldBlocks}
  return region

/--
  Parse the entry block and insert it into the given region.
  Compared to a normal block, the entry block does not need a label.
-/
partial def parseEntryBlock (ip : BlockInsertPoint) : MlirParserM IR.Block := do
  let block ← parseEntryBlockLabel ip
  let blockIp := InsertPoint.atEnd ⟨block.impl.toNat⟩
  while true do
    if (← parseOptionalOp (some blockIp)).isNone then
      break
  return block

/--
  Parse a block and insert it at the given block insert point.
-/
partial def parseOptionalBlock (ip : BlockInsertPoint) : MlirParserM (Option IR.Block) := do
  let some block ← parseOptionalBlockLabel ip
    | return none
  let blockIp := InsertPoint.atEnd ⟨block.impl.toNat⟩
  while true do
    if (← parseOptionalOp (some blockIp)).isNone then
      break
  return block

end

/--
  Parse an operation.
-/
private def parseOp (ip : Option InsertPoint) : MlirParserM IR.Op := do
  let some op ← parseOptionalOp ip | throwAtCurrentPos "operation expected"
  return op

/-- Check that all SSA values forward referenced while parsing were eventually defined. -/
def checkNoUnresolvedForwardValues : MlirParserM Unit := do
  for (valueName, fwd) in (← get).forwardValues do
    throwAt fwd.loc s!"use of undefined value %{String.fromUTF8! valueName}"

/--
  Parse the `!name = type` alias definitions preceding the top-level operation. As in MLIR, a
  definition may use earlier aliases, a name may not be redefined, and names containing a `.` are
  reserved for dialect types.
-/
def parseTypeAliasDefs : MlirParserM Unit := do
  repeat
    let startPos ← getPos
    let some name ← parseOptionalPrefixedKeyword .exclamationIdent | break
    if (← get).typeAliases.contains name then
      throwAt startPos s!"redefinition of type alias id '{String.fromUTF8! name}'"
    if name.toList.contains '.'.toUInt8 then
      throwAt startPos "type names with a '.' are reserved for dialect-defined names"
    parsePunctuation "=" "expected '=' in type alias definition"
    let type ← parseType
    modify fun state => { state with typeAliases := state.typeAliases.insert name type }

/--
  Parse the top-level alias definitions and operation, and report unresolved forward references.
  The top-level operation is left detached.
-/
partial def parseTopLevelOp : MlirParserM IR.Op := do
  parseTypeAliasDefs
  let op ← parseOp none
  checkNoUnresolvedForwardValues
  return op

/--
  The source input of a parsed program, along with the location of each parsed operation.
-/
structure SourceInfo where
  /-- The name of the source. -/
  sourceName : String
  /-- The content of the source. -/
  content : ByteArray
  /-- The location in `content` for each parsed operation, keyed by its buffer address. -/
  opLocations : Std.HashMap Buffed.OperationMPtr Location

/-- Look up an operation's source location without inspecting its erased specification. -/
def SourceInfo.opLocation? (info : SourceInfo) (op : IR.Op) : Option Location :=
  info.opLocations[op.impl]?

/-- Parse program bytes into a buffered IR context and its top-level operation, formatting
    parse errors caret-style against `sourceName`. -/
def parseSourceString (content : ByteArray) (sourceName : String := "<string>")
    (allowUnregisteredDialect : Bool := false) :
    Except String (IR.Context × IR.Op × SourceInfo) := do
  match ParserState.fromInput content with
  | .ok parser =>
    let state := MlirParserState.fromContext IR.empty allowUnregisteredDialect
    match parseTopLevelOp.run state parser with
    | .ok (op, state, _) =>
      return (state.ctx, op, { sourceName, content, opLocations := state.opLocations })
    | .error err =>
      throw (err.format sourceName content)
  | .error err =>
    throw (err.format sourceName content)

end Veir.Parser
