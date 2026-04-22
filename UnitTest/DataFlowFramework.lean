import Veir.Analysis.DataFlowFramework 
import Veir.Parser.MlirParser

open Std (HashMap)
open Veir
open Veir.Parser

namespace UnitTest.DataFlowFramework

abbrev MismatchReport := Array String

def renderReport (report : MismatchReport) : String :=
  if report.isEmpty then
    "ok"
  else
    "mismatches:\n" ++ String.intercalate "\n" report.toList

def parseTopLevelOp (s : String) : Except String (OperationPtr × MlirParserState) := do
  let some (ctx, _) := IRContext.create OpCode
    | throw "internal error: failed to create IR context"
  let parserState ← ParserState.fromInput (s.toByteArray)
  let (op, mlirState, _) ← (parseOp none).run (MlirParserState.fromContext ctx) parserState
  pure (op, mlirState)

def labeledBlockNames (mlir : String) : Array String := Id.run do
  let mut names := #[]
  for line in mlir.splitOn "\n" do
    let trimmed := (line.trimAsciiStart).toString
    if trimmed.startsWith "^" then
      let name := ((trimmed.drop 1).takeWhile fun c => c != ':' && c != '(').toString
      names := names.push name
  names

partial def collectBlocksDepthFirst
    (op : OperationPtr)
    (irCtx : IRContext OpCode)
    (acc : Array BlockPtr := #[]) : Array BlockPtr := Id.run do
  let mut acc := acc
  for i in [0:op.getNumRegions! irCtx] do
    let region := (op.getRegion! irCtx i).get! irCtx
    let mut maybeBlock := region.firstBlock
    while h : maybeBlock.isSome do
      let block := maybeBlock.get h
      acc := acc.push block
      let mut maybeOp := (block.get! irCtx).firstOp
      while hOp : maybeOp.isSome do
        let nestedOp := maybeOp.get hOp
        acc := collectBlocksDepthFirst nestedOp irCtx acc
        maybeOp := (nestedOp.get! irCtx).next
      maybeBlock := (block.get! irCtx).next
  acc

def namedBlocks?
    (top : OperationPtr)
    (irCtx : IRContext OpCode)
    (mlir : String) : Option (HashMap String BlockPtr) :=
  let names := labeledBlockNames mlir
  let blocks := collectBlocksDepthFirst top irCtx
  if names.size != blocks.size then
    none
  else
    some <| Id.run do
      let mut blockMap : HashMap String BlockPtr := HashMap.emptyWithCapacity names.size
      for i in [0:names.size] do
        blockMap := blockMap.insert names[i]! blocks[i]!
      blockMap

def runWithAnalyses
    (mlir : String)
    (analyses : Array DataFlowAnalysis)
    (check : OperationPtr -> DataFlowContext -> MlirParserState -> MismatchReport) : String :=
  match parseTopLevelOp mlir with
  | .error err =>
    s!"parse failed: {err}"
  | .ok (top, parserState) =>
    let dfCtx := fixpointSolve top analyses parserState.ctx
    renderReport (check top dfCtx parserState)
