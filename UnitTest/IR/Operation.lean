import Veir.IR.Basic
import Veir.Parser.MlirParser

open Veir
open Veir.Parser

private def parse (s : String) : OperationPtr × IRContext OpCode :=
  match WfIRContext.create OpCode with
  | none => panic! "failed to create IR context"
  | some (ctx, _) =>
    match ParserState.fromInput s.toByteArray with
    | .error _ => panic! "lex error"
    | .ok parser =>
      match (parseOp none).run (MlirParserState.fromContext ctx) parser with
      | .error _ => panic! "parse error"
      | .ok (op, state, _) => (op, state.ctx.raw)

private def flattenOps (top : OperationPtr) (ctx : IRContext OpCode) :
    Array OperationPtr := Id.run do
  let mut ops := #[]
  for region in (top.get! ctx).regions do
    let region := region.get! ctx
    let mut currentBlock := region.firstBlock
    while let some block := currentBlock do
      let mut currentOp := (block.get! ctx).firstOp
      while let some op := currentOp do
        ops := ops.push op
        currentOp := (op.get! ctx).next
      currentBlock := (block.get! ctx).next
  ops

private def parsed := parse r#""builtin.module"() ({
  %a = "test.test"() : () -> i32
  %b = "test.test"() : () -> i32
  %c = "arith.muli"(%a, %b) : (i32, i32) -> i32
}) : () -> ()"#

private def ops := flattenOps parsed.1 parsed.2

#guard ops[0]!.getNumOperands! parsed.2 == 0
#guard (ops[0]!.getOpOperands! parsed.2).size == 0

#guard ops[2]!.getNumOperands! parsed.2 == 2
#guard (ops[2]!.getOpOperands! parsed.2).size == ops[2]!.getNumOperands! parsed.2
#guard (ops[2]!.getOpOperands! parsed.2)[0]! == ops[2]!.getOpOperand 0
#guard (ops[2]!.getOpOperands! parsed.2)[1]! == ops[2]!.getOpOperand 1

#guard (ops[2]!.getOpOperands! parsed.2)[0]!.op == ops[2]!
#guard (ops[2]!.getOpOperands! parsed.2)[0]!.index == 0
#guard (ops[2]!.getOpOperands! parsed.2)[1]!.index == 1

#guard ops[2]!.getOperand! parsed.2 0 == (ops[0]!.getResult 0 : ValuePtr)
#guard ops[2]!.getOperand! parsed.2 1 == (ops[1]!.getResult 0 : ValuePtr)
