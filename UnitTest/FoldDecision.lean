import UnitTest.DataFlowFramework.Helpers

import Veir.Interfaces.FoldInterfaces

open Veir

/-- Find the first operation with the given opcode. -/
private def findOp (ctx : IRContext OpCode) (opType : OpCode) : Option OperationPtr := Id.run do
  for op in ctx.operations.keys do
    if op.getOpType! ctx = opType then
      return some op
  return none

private def foldDecisionTestModule : String :=
  "\"builtin.module\"() ({
    \"func.func\"() <{function_type = () -> i32, sym_name = \"main\"}> ({
      %c7 = \"arith.constant\"() <{ \"value\" = 7 : i32 }> : () -> i32
      %c8 = \"arith.constant\"() <{ \"value\" = 8 : i32 }> : () -> i32
      %sum = \"arith.addi\"(%c7, %c8) : (i32, i32) -> i32
      \"func.return\"(%sum) : (i32) -> ()
    }) : () -> ()
  }) : () -> ()"

private def testFoldDecisionForOp : String := Id.run do
  match parseTopLevelOp foldDecisionTestModule with
  | .error e => return s!"parse error: {e}"
  | .ok (_, parserState) =>
    let ctx := parserState.ctx.raw
    let some add := findOp ctx (.arith .addi) | return "missing arith.addi"
    let constants : Array (Option RuntimeValue) :=
      #[some (.int 32 (.val 7)), some (.int 32 (.val 8))]
    match foldDecisionForOp add constants ctx with
    | .useConstant (.int 32 (.val value)) =>
      if value ≠ 15 then
        return "foldDecisionForOp produced the wrong constant"
    | _ => return "foldDecisionForOp did not evaluate arith.addi"
    match foldDecisionForOp add #[some (.int 32 (.val 7))] ctx with
    | .noFold => return "ok"
    | _ => return "foldDecisionForOp accepted the wrong operand count"

/--
info: "ok"
-/
#guard_msgs in
#eval! testFoldDecisionForOp
