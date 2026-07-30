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

private def testFoldDecisionForOp : String := Id.run do
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
    match foldDecisionForOp add ctx addInBounds constants with
    | .useConstant (.int 32 (.val value)) =>
      if value ≠ 15 then
        return "foldDecisionForOp produced the wrong constant"
    | _ => return "foldDecisionForOp did not evaluate arith.addi"
    match foldDecisionForOp add ctx addInBounds #[some (.int 32 (.val 7))] with
    | .noFold => pure ()
    | _ => return "foldDecisionForOp accepted the wrong operand count"
    let i32Types := add.getResultTypes ctx.raw addInBounds

    match foldDecisionForOp constant ctx constantInBounds #[] with
    | .noFold => pure ()
    | _ => return "arith.constant folded despite already being constant-like"
    match foldDecision (.arith .addi) default (i32Types ++ i32Types) constants with
    | .noFold => pure ()
    | _ => return "foldDecision accepted a multi-result operation"
    match foldDecision (.arith .divsi) default i32Types
        #[some (.int 32 (.val 5)), some (.int 32 (.val 0))] with
    | .useConstant (.int 32 .poison) => pure ()
    | _ => return "arith.divsi by zero did not fold interpreter UB to poison"
    match foldDecision (.llvm .load) default i32Types #[some (.addr 0)] with
    | .noFold => pure ()
    | _ => return "llvm.load folded despite reading memory"
    match foldDecision (.llvm .sdiv) default i32Types
        #[none, some (.int 32 (.val 1))] with
    | .useOperand 0 => pure ()
    | _ => return "llvm.sdiv by one did not fold"

    match foldDecision (.arith .divsi) default i32Types
        #[none, some (.int 32 (.val 1))] with
    | .useOperand 0 => pure ()
    | _ => return "arith.divsi by one did not fold"
    match foldDecision (.arith .remsi) () i32Types
        #[none, some (.int 32 (.val (BitVec.allOnes 32)))] with
    | .useConstant (.int 32 (.val value)) =>
      if value ≠ 0 then return "arith.remsi by minus one produced a nonzero value"
    | _ => return "arith.remsi by minus one did not fold"
    match foldDecision (.arith .select) () i32Types
        #[none, some (.int 32 .poison), none] with
    | .useOperand 2 => pure ()
    | _ => return "arith.select with a poison true arm did not fold to the false arm"
    return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testFoldDecisionForOp

private def foldDecisionRiscvModule : String :=
  "\"builtin.module\"() ({
    \"func.func\"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg,
                     sym_name = \"main\"}> ({
      ^bb0(%x : !riscv.reg, %y : !riscv.reg):
        %diff = \"riscv.sub\"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        \"func.return\"(%diff) : (!riscv.reg) -> ()
    }) : () -> ()
  }) : () -> ()"

/--
  `riscv.sub` is interpreted as `RISCV.sub rs2 rs1`, so the subtrahend is
  operand 1: a zero there folds to operand 0, and a zero minuend does not fold.
-/
private def testRiscvFoldDecision : String := Id.run do
  match parseTopLevelOp foldDecisionRiscvModule with
  | .error e => return s!"parse error: {e}"
  | .ok (_, parserState) =>
    let ctx := parserState.ctx
    let some ⟨sub, subInBounds⟩ := findOp ctx.raw (.riscv .sub)
      | return "missing riscv.sub"
    match foldDecisionForOp sub ctx subInBounds #[none, some (.reg ⟨0⟩)] with
    | .useOperand 0 => pure ()
    | _ => return "riscv.sub with a zero subtrahend did not fold to operand 0"
    match foldDecisionForOp sub ctx subInBounds #[some (.reg ⟨0⟩), none] with
    | .noFold => return "ok"
    | _ => return "riscv.sub with a zero minuend folded, but sub is not commutative"

/--
info: "ok"
-/
#guard_msgs in
#eval! testRiscvFoldDecision

private def foldDecisionModArithModule : String :=
  "\"builtin.module\"() ({
    \"func.func\"() <{function_type = (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>)
                       -> !mod_arith.int<17 : i32>,
                     sym_name = \"main\"}> ({
      ^bb0(%x : !mod_arith.int<17 : i32>, %y : !mod_arith.int<17 : i32>):
        %prod = \"mod_arith.mul\"(%x, %y)
          : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
        \"func.return\"(%prod) : (!mod_arith.int<17 : i32>) -> ()
    }) : () -> ()
  }) : () -> ()"

/--
  Multiplying by any zero residue folds to zero even with the other operand
  unknown. A nonzero residue does not fold, because the unknown operand is not
  guaranteed to be a canonical residue.
-/
private def testModArithFoldDecision : String := Id.run do
  match parseTopLevelOp foldDecisionModArithModule with
  | .error e => return s!"parse error: {e}"
  | .ok (_, parserState) =>
    let ctx := parserState.ctx
    let some ⟨mul, mulInBounds⟩ := findOp ctx.raw (.mod_arith .mul)
      | return "missing mod_arith.mul"
    -- 34 is not zero, but it is zero modulo 17.
    match foldDecisionForOp mul ctx mulInBounds #[none, some (.int 32 (.val 34))] with
    | .useConstant (.int 32 (.val value)) =>
      if value ≠ 0 then
        return "mod_arith.mul by a zero residue produced the wrong constant"
    | _ => return "mod_arith.mul by a zero residue did not fold"
    match foldDecisionForOp mul ctx mulInBounds #[none, some (.int 32 (.val 3))] with
    | .noFold => return "ok"
    | _ => return "mod_arith.mul by a nonzero residue folded"

/--
info: "ok"
-/
#guard_msgs in
#eval! testModArithFoldDecision
