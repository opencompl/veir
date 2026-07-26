import UnitTest.DataFlowFramework.Helpers
import Veir.Fold.ConstantValue

/-! Tests for reading constant-like IR values as interpreter runtime values. -/

open Veir

private def constantValueOf (text : String) : Except String (Option RuntimeValue) := do
  let (op, state) ← parseTopLevelOp text
  return (op.getResult 0).constantValue state.ctx.raw

private def testConstantValue : String := Id.run do
  let .ok (some (.int 8 (.val arith))) :=
    constantValueOf r#""arith.constant"() <{"value" = -1 : i8}> : () -> i8"#
    | return "failed to read arith.constant"
  if arith ≠ BitVec.ofInt 8 (-1) then
    return "arith.constant produced the wrong value"

  let .ok (some (.int 8 (.val llvm))) :=
    constantValueOf r#""llvm.mlir.constant"() <{"value" = 257 : i16}> : () -> i8"#
    | return "failed to read llvm.mlir.constant"
  if llvm ≠ BitVec.ofInt 8 257 then
    return "llvm.mlir.constant did not use the result bitwidth"

  let .ok (some (.int 16 .poison)) :=
    constantValueOf r#""llvm.mlir.poison"() : () -> i16"#
    | return "failed to read llvm.mlir.poison"

  let .ok (some (.reg li)) :=
    constantValueOf r#""riscv.li"() <{"value" = -1 : i32}> : () -> !riscv.reg"#
    | return "failed to read riscv.li"
  if li.val ≠ BitVec.ofInt 64 (-1) then
    return "riscv.li produced the wrong register value"

  let .ok (some (.int 32 (.val mod13))) := constantValueOf
    r#""mod_arith.constant"() <{"value" = 13 : i32}> : () -> !mod_arith.int<17 : i32>"#
    | return "failed to read canonical mod_arith.constant"
  if mod13 ≠ BitVec.ofInt 32 13 then
    return "mod_arith.constant produced the wrong residue"

  let .ok mod20 := constantValueOf
    r#""mod_arith.constant"() <{"value" = 20 : i32}> : () -> !mod_arith.int<17 : i32>"#
    | return "failed to parse noncanonical mod_arith.constant"
  if mod20.isSome then
    return "accepted a noncanonical mod_arith.constant"

  let .ok modNeg := constantValueOf
    r#""mod_arith.constant"() <{"value" = -1 : i32}> : () -> !mod_arith.int<17 : i32>"#
    | return "failed to parse negative mod_arith.constant"
  if modNeg.isSome then
    return "accepted a negative mod_arith.constant"

  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testConstantValue
