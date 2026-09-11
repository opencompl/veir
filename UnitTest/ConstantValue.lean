import UnitTest.DataFlowFramework.Helpers
import Veir.Interfaces.ConstantLikeInterfaces
import Veir.Passes.Matching.LLVM.Basic

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

/-- Check both constant APIs against explicit expected bit patterns, including
extension from the attribute width and truncation to the result width. -/
private def testLlvmIntegerConstants : Except String Unit := do
  let cases : Array (Int × Nat × Nat × Int) := #[
    (255, 8, 64, -1), (128, 8, 32, -128), (-1, 1, 64, 1),
    (2, 1, 64, 0), (3, 1, 1, 1), (256, 16, 8, 0),
    (257, 16, 8, 1), (511, 16, 8, -1), (255, 8, 1, 1),
    (4294967295, 32, 64, -1), (18446744073709551617, 128, 64, 1),
    (7, 3, 64, -1), (1, 1, 1, -1)]
  for (literal, attrWidth, resultWidth, expected) in cases do
    let source := "%x = \"llvm.mlir.constant\"() <{value = " ++
      s!"{literal} : i{attrWidth}" ++ "}> : () -> " ++ s!"i{resultWidth}"
    let (op, state) ← parseTopLevelOp source
    let val : ValuePtr := op.getResult 0
    let some signed := matchConstantIntVal val state.ctx.raw
      | throw s!"failed to match {source}"
    let expectedBits := BitVec.ofInt resultWidth expected
    if signed ≠ expectedBits.toInt then
      throw s!"incorrect signed value for {source}"
    if matchConstantUIntVal val state.ctx.raw ≠ some expectedBits.toNat then
      throw s!"incorrect unsigned value for {source}"
    if isConstantOne val state.ctx.raw ≠ (expectedBits.toNat == 1) then
      throw s!"incorrect one predicate for {source}"
    let some (.int width (.val bits)) := val.constantValue state.ctx.raw
      | throw s!"failed to interpret {source}"
    if width ≠ resultWidth ∨ bits.toNat ≠ (BitVec.ofInt resultWidth expected).toNat then
      throw s!"incorrect interpreted value for {source}"

/-- info: Except.ok () -/
#guard_msgs in
#eval! testLlvmIntegerConstants

/-- The shared decoder agrees with LLVM's extension rules, including literals
outside the attribute's range and results narrower than the attribute. -/
private def testLlvmIntegerExtension : Bool := Id.run do
  for attrWidth in [1, 2, 3, 8, 16, 32, 64, 65, 128] do
    for resultWidth in [1, 2, 8, 32, 64, 128] do
      for literal in ([-1, 0, 1, 2, 127, 128, 255, 256, 257,
          2 ^ attrWidth - 1, 2 ^ attrWidth, 2 ^ attrWidth + 1] : List Int) do
        let raw := BitVec.ofInt attrWidth literal
        let expected := if attrWidth = 1 then raw.zeroExtend resultWidth
          else raw.signExtend resultWidth
        let actual := BitVec.ofInt resultWidth
          (decodeLLVMIntegerConstant (IntegerAttr.mk literal (IntegerType.mk attrWidth)))
        if actual ≠ expected then return false
  return true

/-- info: true -/
#guard_msgs in
#eval! testLlvmIntegerExtension
