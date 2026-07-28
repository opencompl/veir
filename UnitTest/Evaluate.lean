import UnitTest.DataFlowFramework.Helpers

import Veir.Interfaces.SideEffectInterfaces
import Veir.Interpreter.Evaluate

/-! Tests for compile-time evaluation of operations with the interpreter. -/

open Veir

private def i32 : TypeAttr := IntegerType.mk 32

private def testEvaluateAddi : String := Id.run do
  let operands : Array RuntimeValue := #[.int 32 (.val 7), .int 32 (.val 8)]
  let some (.ok results) :=
    (foldEvaluate (.arith .addi) default #[i32] operands : Option (UBOr (Array RuntimeValue)))
    | return "arith.addi did not evaluate"
  let result? : Option RuntimeValue := results[0]?
  let some (.int 32 (.val value)) := result?
    | return "arith.addi produced no i32 result"
  if value ≠ 15 then
    return "arith.addi produced the wrong value"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testEvaluateAddi

/-- Division by zero is immediate UB, which the interpreter reports as `.ub`
    rather than as a value: a client must not read a result out of it. Turning
    UB into poison is the client's policy decision, not this layer's. -/
private def testEvaluateUB : String := Id.run do
  let operands : Array RuntimeValue := #[.int 32 (.val 5), .int 32 (.val 0)]
  let some .ub :=
    (foldEvaluate (.arith .divsi) default #[i32] operands : Option (UBOr (Array RuntimeValue)))
    | return "arith.divsi by zero did not report UB"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testEvaluateUB

/-- An operation the interpreter does not implement evaluates to `none`. The
    `mod_arith` dialect is lowered to `arith` before interpretation, so it has
    no runtime semantics of its own to evaluate against. -/
private def testEvaluateUninterpreted : String := Id.run do
  let m17 : TypeAttr := ModArithType.mk (IntegerAttr.mk 17 (IntegerType.mk 32))
  let operands : Array RuntimeValue := #[.int 32 (.val 13), .int 32 (.val 7)]
  let none := (foldEvaluate (.mod_arith .add) () #[m17] operands : Option (UBOr (Array RuntimeValue)))
    | return "an uninterpreted operation was evaluated"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testEvaluateUninterpreted

/-! ## Which operations may be evaluated -/

/-- Find the first operation with the given opcode. -/
private def findOp (ctx : IRContext OpCode) (opType : OpCode) : Option OperationPtr := Id.run do
  for op in ctx.operations.keys do
    if op.getOpType! ctx = opType then
      return some op
  return none

private def loadModule (volatileFlag : String) : String :=
  "\"builtin.module\"() ({
    \"func.func\"() <{function_type = (!llvm.ptr) -> i32, sym_name = \"main\"}> ({
    ^bb0(%p : !llvm.ptr):
      %v = \"llvm.load\"(%p) " ++ volatileFlag ++ " : (!llvm.ptr) -> i32
      \"func.return\"(%v) : (i32) -> ()
    }) : () -> ()
  }) : () -> ()"

/--
  A non-volatile load is the case that separates the two questions: it is
  removable when its result is unused, so `hasSideEffects` reports `false`,
  and it must still never be executed at compile time.
-/
private def testNonVolatileLoadIsNotFoldEvaluable : String := Id.run do
  let .ok (_, state) := parseTopLevelOp (loadModule "") | return "parse error"
  let ctx := state.ctx.raw
  let some load := findOp ctx (.llvm .load) | return "missing llvm.load"
  if load.hasSideEffects ctx then
    return "a non-volatile llvm.load was reported as side-effecting"
  -- The guard inside `foldEvaluate` is what makes this hold, whatever the
  -- interpreter would have done with the empty memory.
  let props := load.getProperties! ctx (.llvm .load)
  let none := (foldEvaluate (.llvm .load) props (load.getResultTypes! ctx) #[.addr 0]
    : Option (UBOr (Array RuntimeValue)))
    | return "a non-volatile llvm.load was evaluated"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testNonVolatileLoadIsNotFoldEvaluable

/-- A volatile load is excluded twice over: it is side-effecting and reads
    memory. -/
private def testVolatileLoadIsNotFoldEvaluable : String := Id.run do
  let .ok (_, state) := parseTopLevelOp (loadModule "<{volatile_}>") | return "parse error"
  let ctx := state.ctx.raw
  let some load := findOp ctx (.llvm .load) | return "missing llvm.load"
  if ¬ load.hasSideEffects ctx then
    return "a volatile llvm.load was reported as free of side effects"
  let props := load.getProperties! ctx (.llvm .load)
  let none := (foldEvaluate (.llvm .load) props (load.getResultTypes! ctx) #[.addr 0]
    : Option (UBOr (Array RuntimeValue)))
    | return "a volatile llvm.load was evaluated"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testVolatileLoadIsNotFoldEvaluable
