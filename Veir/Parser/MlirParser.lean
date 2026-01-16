import Veir.Parser.Parser
import Veir.IR.Basic
import Veir.Rewriter.InsertPoint
import Veir.Rewriter.Basic

open Veir.Parser.Lexer
open Veir.Parser

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

set_option warn.sorry false in
mutual

/--
  Parse the regions of an operation.
-/
partial def parseOpRegions : MlirParserM (Array RegionPtr) := do
  parseOptionalDelimitedList Delimiter.Paren parseRegion

/--
  Parse an operation, if present, and insert it at the given insert point.
-/
partial def parseOptionalOp (ip : Option InsertPoint) : MlirParserM (Option OperationPtr) := do
  let some opName ← parseOptionalStringLiteral | return none
  parsePunctuation "("
  parsePunctuation ")"
  let regions ← parseOpRegions
  parsePunctuation ":"
  parsePunctuation "("
  parsePunctuation ")"
  parsePunctuation "->"
  parsePunctuation "("
  parsePunctuation ")"
  let opId := operationNameToOpId opName
  let some (ctx, op) := Rewriter.createOp (← getContext) opId 0 #[] regions 0 ip (by grind) (by sorry) (by sorry) (by sorry)
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
