import Veir.GlobalOpInfo
import Veir.Input
import Veir.Printer
import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution

open Veir
open Veir.Input
open Veir.Puddle

structure ParsedModule where
  ctx : WfIRContext OpCode
  moduleOp : OperationPtr

def parseModule (source : String) : Option ParsedModule := do
  let (ctx, moduleOp, _) ← (parseSourceString source.toUTF8).toOption
  return ⟨ctx, moduleOp⟩

def rewriteAndPrint (source : String) (rule : Pattern OpCode) : IO Unit := do
  let some program := parseModule source | IO.println "parse failed"
  let pattern := Pattern.compile rule
  let some ctx := RewritePattern.applyInContext pattern.run program.ctx program.moduleOp
    | IO.println "rewrite failed"
  Printer.printModule ctx.raw program.moduleOp

def Veir.OperationPtr.body! (op : OperationPtr) (ctx : IRContext OpCode) : OperationPtr :=
  (((op.getRegion! ctx 0).getFirstBlock! ctx).get!.getFirstOp! ctx).get!

def Veir.OperationPtr.next! (op : OperationPtr) (ctx : IRContext OpCode) : OperationPtr :=
  (op.getNextOp! ctx).get!

def Veir.findOp (ctx : IRContext OpCode) (opType : OpCode) :
    Option { op : OperationPtr // op.InBounds ctx } := Id.run do
  for op in ctx.operations.keys do
    if op.getOpType! ctx = opType then
      if h : op.InBounds ctx then
        return some ⟨op, h⟩
  return none
