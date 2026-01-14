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
  if !(← parseOptionalPunctuation "(") then
    return #[]
  let region ← parseRegion
  parsePunctuation ")"
  return #[region]

/--
  Parse an operation, if present, and insert it at the given insert point.
-/
partial def parseOptionalOp (ip : Option InsertPoint) : MlirParserM (Option OperationPtr) := do
  match ← parseOptionalStringLiteral with
  | none => return none
  | some opName =>
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
    match Rewriter.createOp (← getContext) opId 0 #[] regions 0 ip (by grind) (by sorry) (by sorry) (by sorry) with
    | some (ctx, op) =>
      setContext ctx
      return op
    | none => throw "internal error: failed to create operation"

/--
  Parse an operation.
-/
partial def parseOp (ip : Option InsertPoint) : MlirParserM OperationPtr := do
  match ← parseOptionalOp ip with
  | some op => return op
  | none => throw "operation expected"

/--
  Parse a region.
-/
partial def parseRegion : MlirParserM RegionPtr := do
  parsePunctuation "{"
  let ctx := ← getContext
  match Rewriter.createRegion ctx with
  | some (ctx, region) =>
    setContext ctx
    let _ ← parseBlock (BlockInsertPoint.atEnd region)
    parsePunctuation "}"
    return region
  | none => throw "internal error: failed to create region"

/--
  Parse a block and insert it at the given block insert point.
-/
partial def parseBlock (ip : Option BlockInsertPoint) : MlirParserM BlockPtr := do
  let ctx := ← getContext
  match Rewriter.createBlock ctx ip (by sorry) (by sorry) with
  | some (ctx, block) =>
    setContext ctx
    while true do
      if (← parseOptionalOp (InsertPoint.atEnd block)) == none then
        break
    return block
  | none => throw "internal error: failed to create block"

end

end Veir.Parser
