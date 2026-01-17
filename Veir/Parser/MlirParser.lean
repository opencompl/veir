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
  ctx : IRContext

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
  Set the current IR context.
  This should be called whenever any modifications have been made to the context
  outside of the parser monad.
-/
def setContext (ctx : IRContext) : MlirParserM Unit := do
  modify fun s => {s with ctx := ctx}

/--
  Parse an operation result.
-/
def parseOpResult : MlirParserM Slice := do
  let nameToken ← parseToken .percentIdent "operation result expected"
  return { nameToken.slice with start := nameToken.slice.start + 1 } -- skip % character

/--
  Parse the results before an operation definition,
  either as a list of values followed by '=', or nothing.
-/
def parseOpResults : MlirParserM (Array Slice) := do
  let .percentIdent := (← peekToken).kind | return #[]
  let results ← parseList parseOpResult
  parsePunctuation "=" "'=' expected after operation results"
  return results

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
  let results ← parseOpResults
  let some opName ← parseOptionalStringLiteral | return none
  parsePunctuation "("
  parsePunctuation ")"
  let regions ← parseOpRegions
  let (inputTypes, outputTypes) ← parseOperationType
  if outputTypes.size ≠ results.size then
    throw s!"operation '{opName}' declares {outputTypes.size} result types, but {results.size} result names were provided"
  let opId := operationNameToOpId opName
  let some (ctx, op) := Rewriter.createOp (← getContext) opId results.size #[] regions 0 ip (by grind) (by sorry) (by sorry) (by sorry)
      | throw "internal error: failed to create operation"
    setContext ctx
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
  parsePunctuation "{"
  let ctx := ← getContext
  let some (ctx, region) := Rewriter.createRegion ctx
      | throw "internal error: failed to create region"
    setContext ctx
    let _ ← parseBlock (BlockInsertPoint.atEnd region)
    parsePunctuation "}"
    return region

/--
  Parse a block and insert it at the given block insert point.
-/
partial def parseBlock (ip : Option BlockInsertPoint) : MlirParserM BlockPtr := do
  let ctx := ← getContext
  let some (ctx, block) := Rewriter.createBlock ctx ip (by sorry) (by sorry)
      | throw "internal error: failed to create block"
    setContext ctx
    while true do
      if (← parseOptionalOp (InsertPoint.atEnd block)) == none then
        break
    return block

end

end Veir.Parser
