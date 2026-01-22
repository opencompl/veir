import Veir.Parser.Parser
import Veir.Parser.AttrParser
import Veir.IR.Basic
import Veir.Rewriter.InsertPoint
import Veir.Rewriter.Basic

open Veir.Parser.Lexer
open Veir.Parser
open Veir.AttrParser

namespace Veir.Parser

/--
  Map operation names to operation IDs.
  Unregistered operations are mapped to 42.
-/
def operationNameToOpId (name : String) : Nat :=
  match name with
  | "builtin.module" => 0
  | "arith.constant" => 1
  | "arith.addi" => 2
  | "return" => 3
  | "arith.muli" => 4
  | "arith.andi" => 5
  | "test.test" => 99
  | _ => 42

structure MlirParserState where
  /-- The current IR context. -/
  ctx : IRContext
  /-- The values that have been defined at that point in the parser. -/
  values : Std.HashMap ByteArray ValuePtr
  /--
    The blocks that have been already parsed.
    The Bool value indicates whether the block has already been parsed
    (true), or has been forward declared (false).
  -/
  blocks : Std.HashMap ByteArray (BlockPtr × Bool)

def MlirParserState.fromContext (ctx : IRContext) : MlirParserState :=
  { ctx := ctx, values := Std.HashMap.emptyWithCapacity 128, blocks := Std.HashMap.emptyWithCapacity 1 }

abbrev MlirParserM := StateT MlirParserState (EStateM String ParserState)

/--
  Execute the action with the given initial state.
  Returns the result along with the final state, or an error message.
-/
def MlirParserM.run (self : MlirParserM α)
  (mlirParserState : MlirParserState) (parserState: ParserState) : Except String (α × MlirParserState × ParserState) :=
  match (StateT.run self mlirParserState).run parserState with
  | .ok (a, mlirParserState) parserState => .ok (a, mlirParserState, parserState)
  | .error err _ => .error err

/--
  Execute the action with the given initial state.
  Returns the result or an error message.
-/
def MlirParserM.run' (self : MlirParserM α)
  (mlirParserState : MlirParserState) (parserState: ParserState) : Except String α :=
  match self.run mlirParserState parserState with
  | .ok (a, _, _) => .ok a
  | .error err => .error err

/--
  Get the current IR context that is stored in the parser state.
-/
def getContext : MlirParserM IRContext := do
  return (← get).ctx

/--
  Get a value that has previously been parsed given its name.
-/
def getValue? (name : ByteArray) : MlirParserM (Option ValuePtr) := do
  return (← get).values[name]?

/--
  Get the original input that is being parsed.
-/
def getInput : MlirParserM ByteArray := do
  return (← getThe ParserState).input

/--
  Register a parsed value with the given name.
  This is used to keep track of values that have been defined during parsing.
-/
def registerValueDef (name : ByteArray) (value : ValuePtr) : MlirParserM Unit := do
  modify fun s => { s with values := s.values.insert name value }

/--
  Set the current IR context.
  This should be called whenever any modifications have been made to the context
  outside of the parser monad.
-/
def setContext (ctx : IRContext) : MlirParserM Unit := do
  modify fun s => {s with ctx := ctx}

/--
  Create a block at the given insert point and register its name in the parsing context.
  If a block was already declared with the given name, use that block instead, and
  insert it at the given insert point.
-/
def defineBlock (name : ByteArray) (ip : BlockInsertPoint) : MlirParserM BlockPtr := do
  let state ← get
  match state.blocks[name]? with
  | some (block, true) => -- Case where a block of this name is already defined
    throw s!"block %{String.fromUTF8! name} has already been defined"
  | some (block, false) => -- Case where a block of this name was forward declared
    /- Insert the block at the given location. -/
    let ctx ← getContext
    let some ctx := Rewriter.insertBlock? ctx block ip (by sorry) (by sorry) (by sorry)
      | throw "internal error: failed to insert block"
    setContext ctx
    /- Notify the parsing context that the block is defined. -/
    modifyThe MlirParserState (fun state =>
    { state with
      blocks :=
        state.blocks.insert name (block, true)
    })
    return block
  | none => -- Case where the block has not yet been declared or referenced
    /- Create the block -/
    let ctx ← getContext
    let some (ctx, block) := Rewriter.createBlock ctx ip (by sorry) (by sorry)
      | throw "internal error: failed to create block"
    setContext ctx
    /- Notify the parsing context that the block is defined. -/
    modifyThe MlirParserState fun s =>
    { s with
      blocks :=
        s.blocks.insert name (block, true)
    }
    return block

/--
  Forward declare a block with the given name.
  If the block was already forward declared or defined, return the existing block.
  Otherwise, create a new block without inserting it in a region.
-/
def defineBlockUse (name : ByteArray) : MlirParserM BlockPtr := do
  let state ← get
  match state.blocks[name]? with
  | some (block, _) => -- Block already defined or forward declared
    return block
  | none => -- Block not yet encountered
    /- Create the block -/
    let ctx ← getContext
    let some (ctx, block) := Rewriter.createBlock ctx none (by sorry) (by sorry)
      | throw "internal error: failed to create block"
    setContext ctx
    /- Notify the parsing context that the block is forward declared. -/
    modifyThe MlirParserState fun s =>
    { s with
      blocks :=
        s.blocks.insert name (block, false)
    }
    return block

/--
  Parse an operation result.
-/
def parseOpResult : MlirParserM ByteArray := do
  let nameToken ← parseToken .percentIdent "operation result expected"
  let slice := { nameToken.slice with start := nameToken.slice.start + 1 } -- skip % character
  return slice.of (← getInput)

/--
  Parse the results before an operation definition,
  either as a list of values followed by '=', or nothing.
-/
def parseOpResults : MlirParserM (Array ByteArray) := do
  let .percentIdent := (← peekToken).kind | return #[]
  let results ← parseList parseOpResult
  parsePunctuation "=" "'=' expected after operation results"
  return results

/--
  An operand whose type has not yet been resolved.
  This is used during parsing to allow parsing operands before their types.
  Once the operation type is known, `resolveOperand` can be used to create an SSA value and
  check that the type matches with previous uses.
-/
structure UnresolvedOperand where
  name : ByteArray

/--
  Parse an operation operand.
-/
def parseOperand : MlirParserM UnresolvedOperand := do
  let nameToken ← parseToken .percentIdent "operand expected"
  return UnresolvedOperand.mk ({ nameToken.slice with start := nameToken.slice.start + 1 }.of (← getInput))

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
  let block ← defineBlockUse name
  return block

/--
  Parse a single block operand.
-/
def parseBlockOperands : MlirParserM (Array BlockPtr) := do
  parseOptionalDelimitedList .square parseBlockOperand

/--
  Resolve an operand to an SSA value of the expected type.
  Throw an error if the value is not defined or if the type does not match.
-/
def resolveOperand (operand : UnresolvedOperand) (expectedType : MlirType) : MlirParserM ValuePtr := do
  let some value := (← getValue? operand.name) | throw s!"use of undefined value %{String.fromUTF8! operand.name}"
  let parsedType := value.getType! (← getContext)
  if parsedType ≠ expectedType then
    throw s!"type mismatch for value %{String.fromUTF8! operand.name}: expected {expectedType}, got {parsedType}"
  return value

/--
  Parse a type, if present.
-/
def parseOptionalType : MlirParserM (Option MlirType) := do
  match AttrParser.parseOptionalType.run AttrParserState.mk (← getThe ParserState) with
  | .ok (ty, _, parserState) =>
    set parserState
    return ty
  | .error err => throw err

/--
  Parse a type, otherwise return an error.
-/
def parseType (errorMsg : String := "type expected") : MlirParserM MlirType := do
  match ← parseOptionalType with
  | some ty => return ty
  | none => throw errorMsg

/--
  Parse an operation type, consisting of a colon followed by a function type.
-/
def parseOperationType : MlirParserM (Array MlirType × Array MlirType) := do
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
-/
def parseTypedValue : MlirParserM (ByteArray × MlirType) := do
  let nameToken ← parseToken .percentIdent "value expected"
  let slice := { nameToken.slice with start := nameToken.slice.start + 1 } -- skip % character
  let name := slice.of (← getInput)
  parsePunctuation ":"
  let ty ← parseType
  return (name, ty)

/--
  Parse a block label, if present, and create and insert the block at the given insert point.
-/
def parseOptionalBlockLabel (ip : BlockInsertPoint) : MlirParserM (Option BlockPtr) := do
  /- Parse the block name -/
  let some labelToken ← parseOptionalToken .caretIdent
    | return none
  let slice := { labelToken.slice with start := labelToken.slice.start + 1 } -- skip ^ character
  let name := slice.of (← getInput)
  /- Parse the arguments -/
  let arguments ← parseOptionalDelimitedList .paren parseTypedValue
  parsePunctuation ":" "':' expected after block label"
  /- Create the block or get it if it was forward declared. -/
  let block ← defineBlock name ip
  /- Insert block arguments in the block. -/
  let blockArguments := arguments.mapIdx (fun index (_, type) => BlockArgument.mk (ValueImpl.mk type none) index () block)
  let ctx ← getContext
  let ctx := block.setArguments ctx blockArguments (by sorry)
  setContext ctx
  /- Register the block argument names in the parser state. -/
  for ((argName, argType), index) in arguments.zipIdx do
    registerValueDef argName (ValuePtr.blockArgument { block := block, index := index })
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
    let block ← defineBlock ByteArray.empty ip
    return block

set_option warn.sorry false in
mutual

/--
  Parse the regions of an operation.
-/
partial def parseOpRegions : MlirParserM (Array RegionPtr) := do
  parseOptionalDelimitedList .paren parseRegion

/--
  Parse an operation, if present, and insert it at the given insert point.
-/
partial def parseOptionalOp (ip : Option InsertPoint) : MlirParserM (Option OperationPtr) := do
  /- Parse the operation. -/
  let results ← parseOpResults
  let some opName ← parseOptionalStringLiteral | return none
  let operands ← parseOperands
  let blockOperands ← parseBlockOperands
  let regions ← parseOpRegions
  let (inputTypes, outputTypes) ← parseOperationType

  /- Check that the number of results matches with the operation type. -/
  if outputTypes.size ≠ results.size then
    throw s!"operation '{opName}' declares {outputTypes.size} result types, but {results.size} result names were provided"

  /- Check that the number and types of operands matches with the operation type. -/
  if inputTypes.size ≠ operands.size then
    throw s!"operation '{opName}' declares {inputTypes.size} operand types, but {operands.size} operands were provided"
  let operands ← operands.zip inputTypes |>.mapM (fun (operand, type) => resolveOperand operand type)

  /- Create the operation. -/
  let opId := operationNameToOpId opName
  let some (ctx, op) := Rewriter.createOp (← getContext) opId outputTypes operands blockOperands regions 0 ip (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
      | throw "internal error: failed to create operation"

  /- Update the parser context. -/
  setContext ctx

  /- Register the new operation results in the parser state. -/
  for index in 0...(op.getNumResults! ctx) do
    let resultValue := op.getResult index
    registerValueDef results[index]! resultValue
  return op

/--
  Parse an operation.
-/
partial def parseOp (ip : Option InsertPoint) : MlirParserM OperationPtr := do
  let some op ← parseOptionalOp ip | throw "operation expected"
  return op

/--
  Parse a region.
-/
partial def parseRegion : MlirParserM RegionPtr := do
  /- Reset the block parsing state, as blocks are local to regions. -/
  let oldBlocks := (← getThe MlirParserState).blocks
  modifyThe MlirParserState fun s => { s with blocks := Std.HashMap.emptyWithCapacity 1 }

  /- Create the region and parse the open delimiter. -/
  parsePunctuation "{"
  let ctx := ← getContext
  let some (ctx, region) := Rewriter.createRegion ctx
      | throw "internal error: failed to create region"
  setContext ctx

  /- Case where there is no blocks inside the region. -/
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
  for (blockName, (_, parsed)) in (← getThe MlirParserState).blocks do
    if !parsed then
      throw s!"block %{String.fromUTF8! blockName} was declared but not defined"

  /- Restore the previous block parsing state. -/
  modifyThe MlirParserState fun s => { s with blocks := oldBlocks }
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

end Veir.Parser
