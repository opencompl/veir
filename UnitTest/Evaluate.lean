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
