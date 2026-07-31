import UnitTest.DataFlowFramework.Helpers

import Veir.Interfaces.FoldInterfaces

open Veir

/-- Find the first in-bounds operation with the given opcode. -/
private def findOp (ctx : IRContext OpCode) (opType : OpCode) :
    Option { op : OperationPtr // op.InBounds ctx } := Id.run do
  for op in ctx.operations.keys do
    if op.getOpType! ctx = opType then
      if h : op.InBounds ctx then
        return some ⟨op, h⟩
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

/-- One case per outcome of `foldDecision`. -/
private def testFoldDecision : String := Id.run do
  match parseTopLevelOp foldDecisionTestModule with
  | .error e => return s!"parse error: {e}"
  | .ok (_, parserState) =>
    let ctx := parserState.ctx
    let some ⟨add, addInBounds⟩ := findOp ctx.raw (.arith .addi)
      | return "missing arith.addi"
    let some ⟨constant, constantInBounds⟩ := findOp ctx.raw (.arith .constant)
      | return "missing arith.constant"
    let constants : Array (Option RuntimeValue) :=
      #[some (.int 32 (.val 7)), some (.int 32 (.val 8))]
    let i32Types := add.getResultTypes ctx.raw addInBounds

    -- All operands known: the interpreter supplies the constant.
    match foldDecisionForOp add ctx addInBounds constants with
    | .useConstant (.int 32 (.val value)) =>
      if value ≠ 15 then
        return s!"arith.addi folded to the wrong constant: {value}"
    | _ => return "arith.addi did not evaluate"

    -- An unknown operand defeats folding; there are no partial folds.
    match foldDecisionForOp add ctx addInBounds #[none, some (.int 32 (.val 8))] with
    | .noFold => pure ()
    | _ => return "arith.addi folded with an unknown operand"

    -- Interpreter UB becomes poison.
    match foldDecision (.arith .ceildivui) default i32Types
        #[some (.int 32 (.val 5)), some (.int 32 (.val 0))] with
    | .useConstant (.int 32 .poison) => pure ()
    | _ => return "arith.ceildivui by zero did not fold UB to poison"

    -- The interpreter declines operations that read memory.
    match foldDecision (.llvm .load) default i32Types #[some (.addr 0)] with
    | .noFold => pure ()
    | _ => return "llvm.load folded despite reading memory"

    -- Guards ahead of the interpreter: operand count, arity, constant-likeness.
    match foldDecisionForOp add ctx addInBounds #[some (.int 32 (.val 7))] with
    | .noFold => pure ()
    | _ => return "foldDecisionForOp accepted the wrong operand count"

    match foldDecision (.arith .addi) default (i32Types ++ i32Types) constants with
    | .noFold => pure ()
    | _ => return "foldDecision accepted a multi-result operation"

    match foldDecisionForOp constant ctx constantInBounds #[] with
    | .noFold => pure ()
    | _ => return "arith.constant folded despite already being constant-like"
    return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testFoldDecision
