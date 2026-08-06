import UnitTest.DataFlowFramework.Helpers

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
    `datapath` dialect models hardware structures with no runtime semantics of
    their own to evaluate against. -/
private def testEvaluateUninterpreted : String := Id.run do
  let operands : Array RuntimeValue := #[.int 32 (.val 13), .int 32 (.val 7)]
  let none := (foldEvaluate (.datapath .compress) () #[i32, i32] operands : Option (UBOr (Array RuntimeValue)))
    | return "an uninterpreted operation was evaluated"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testEvaluateUninterpreted

/-- `mod_arith` operations have interpreter semantics and fold modulo the
    modulus of their result type: (13 + 7) mod 17 = 3. -/
private def testEvaluateModArithAdd : String := Id.run do
  let m17 : TypeAttr := ModArithType.mk (IntegerAttr.mk 17 (IntegerType.mk 32))
  let operands : Array RuntimeValue := #[.int 32 (.val 13), .int 32 (.val 7)]
  let some (.ok results) :=
    (foldEvaluate (.mod_arith .add) () #[m17] operands : Option (UBOr (Array RuntimeValue)))
    | return "mod_arith.add did not evaluate"
  let result? : Option RuntimeValue := results[0]?
  let some (.int 32 (.val value)) := result?
    | return "mod_arith.add produced no i32 result"
  if value ≠ 3 then
    return "mod_arith.add produced the wrong value"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testEvaluateModArithAdd
