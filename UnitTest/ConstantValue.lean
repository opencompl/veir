import UnitTest.DataFlowFramework.Helpers
import Veir.Fold.ConstantValue

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

/-- The attribute is wider than the result, so the result type wins. -/
private def testLlvmConstantUsesResultBitwidth : String := Id.run do
  let .ok (some (.int 8 (.val value))) :=
    constantValueOf r#"%x = "llvm.mlir.constant"() <{"value" = 257 : i16}> : () -> i8"#
    | return "failed to read llvm.mlir.constant"
  if value ≠ BitVec.ofInt 8 257 then
    return "llvm.mlir.constant did not use the result bitwidth"
  return "ok"

private def testLlvmPoison : String := Id.run do
  let .ok (some (.int 16 .poison)) :=
    constantValueOf r#"%x = "llvm.mlir.poison"() : () -> i16"#
    | return "failed to read llvm.mlir.poison"
  return "ok"

private def testRiscvLi : String := Id.run do
  let .ok (some (.reg value)) :=
    constantValueOf r#"%x = "riscv.li"() <{"value" = -1 : i32}> : () -> !riscv.reg"#
    | return "failed to read riscv.li"
  if value.val ≠ BitVec.ofInt 64 (-1) then
    return "riscv.li produced the wrong register value"
  return "ok"

private def testHwConstant : String := Id.run do
  let .ok (some (.int 32 (.val value))) :=
    constantValueOf r#"%x = "hw.constant"() <{"value" = 42 : i32}> : () -> i32"#
    | return "failed to read hw.constant"
  if value ≠ BitVec.ofInt 32 42 then
    return "hw.constant produced the wrong value"
  return "ok"

/--
  `mod_arith.constant` is constant-like, but the interpreter does not model
  the dialect, so there is no value to report.
-/
private def testUnmodeledConstant : String := Id.run do
  let .ok value := constantValueOf
    r#"%x = "mod_arith.constant"() <{"value" = 13 : i32}> : () -> !mod_arith.int<17 : i32>"#
    | return "failed to parse mod_arith.constant"
  if value.isSome then
    return "read a constant the interpreter does not model"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testArithConstant

/--
info: "ok"
-/
#guard_msgs in
#eval! testLlvmConstantUsesResultBitwidth

/--
info: "ok"
-/
#guard_msgs in
#eval! testLlvmPoison

/--
info: "ok"
-/
#guard_msgs in
#eval! testRiscvLi

/--
info: "ok"
-/
#guard_msgs in
#eval! testHwConstant

/--
info: "ok"
-/
#guard_msgs in
#eval! testUnmodeledConstant
