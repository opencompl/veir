import UnitTest.DataFlowFramework.Helpers
import Veir.Interfaces.ConstantLikeInterfaces

/-! Tests for reading constant-like IR values as interpreter runtime values. -/

open Veir

private def constantValueOf (text : String) : Except String (Option RuntimeValue) := do
  let (op, state) ← parseTopLevelOp text
  return (op.getResult 0 : ValuePtr).constantValue state.ctx.raw

private def testArithConstant : String := Id.run do
  let .ok (some (.int 8 (.val value))) :=
    constantValueOf r#"%x = "arith.constant"() <{"value" = -1 : i8}> : () -> i8"#
    | return "failed to read arith.constant"
  if value ≠ BitVec.ofInt 8 (-1) then
    return "arith.constant produced the wrong value"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testArithConstant

private def testLlvmPoison : String := Id.run do
  let .ok (some (.int 16 .poison)) :=
    constantValueOf r#"%x = "llvm.mlir.poison"() : () -> i16"#
    | return "failed to read llvm.mlir.poison"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testLlvmPoison

private def testRiscvLi : String := Id.run do
  let .ok (some (.reg value)) :=
    constantValueOf r#"%x = "riscv.li"() <{"value" = -77 : i32}> : () -> !riscv.reg"#
    | return "failed to read riscv.li"
  if value.val ≠ BitVec.ofInt 64 (-77) then
    return "riscv.li produced the wrong register value"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testRiscvLi

private def testRiscvLui : String := Id.run do
  let .ok (some (.reg value)) :=
    constantValueOf r#"%x = "riscv.lui"() <{"value" = 5 : i20}> : () -> !riscv.reg"#
    | return "failed to read riscv.lui"
  if value.val ≠ (BitVec.ofInt 20 5 ++ (0 : BitVec 12)).signExtend 64 then
    return "riscv.lui produced the wrong register value"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testRiscvLui

private def testHwConstant : String := Id.run do
  let .ok (some (.int 32 (.val value))) :=
    constantValueOf r#"%x = "hw.constant"() <{"value" = 42 : i32}> : () -> i32"#
    | return "failed to read hw.constant"
  if value ≠ BitVec.ofInt 32 42 then
    return "hw.constant produced the wrong value"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testHwConstant
