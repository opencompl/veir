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

private def testFoldDecision : String := Id.run do
  match parseTopLevelOp foldDecisionTestModule with
  | .error e => return s!"parse error: {e}"
  | .ok (_, parserState) =>
    let ctx := parserState.ctx
    let some ⟨add, addInBounds⟩ := findOp ctx.raw (.arith .addi)
      | return "missing arith.addi"
    let constants : Array (Option RuntimeValue) :=
      #[some (.int 32 (.val 7)), some (.int 32 (.val 8))]
    let i32Types := add.getResultTypes ctx.raw addInBounds

    -- All operands known: the interpreter supplies the constant.
    match add.foldsTo ctx addInBounds constants with
    | some #[.useConstant (.int 32 (.val value))] =>
      if value ≠ 15 then
        return s!"arith.addi folded to the wrong constant: {value}"
    | _ => return "arith.addi did not evaluate"

    -- An unknown operand defeats folding.
    match add.foldsTo ctx addInBounds #[none, some (.int 32 (.val 8))] with
    | none => pure ()
    | _ => return "arith.addi folded with an unknown operand"

    -- Interpreter UB becomes poison.
    match OpCode.foldsTo (.arith .ceildivui) default i32Types
        #[some (.int 32 (.val 5)), some (.int 32 (.val 0))] with
    | some #[.useConstant (.int 32 .poison)] => pure ()
    | _ => return "arith.ceildivui by zero did not fold UB to poison"

    return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testFoldDecision

private def testArithConstantMaterialization : String := Id.run do
  let i32 : TypeAttr := IntegerType.mk 32
  match (.arith .addi : OpCode).materializeConstant (.int 32 (.val 15)) i32 with
  | some ⟨.arith .constant, props⟩ =>
    if props.value ≠ IntegerAttr.mk 15 (IntegerType.mk 32) then
      return "arith materialized the wrong constant"
    return "ok"
  | _ => return "arith did not materialize arith.constant"

/--
info: "ok"
-/
#guard_msgs in
#eval! testArithConstantMaterialization

private def testRiscvConstantMaterialization : String := Id.run do
  let regType : TypeAttr := RegisterType.mk
  let value : RuntimeValue := .reg ⟨BitVec.ofInt 64 (-77)⟩
  match (.riscv .add : OpCode).materializeConstant value regType with
  | some ⟨.riscv .li, props⟩ =>
    if props.value ≠ IntegerAttr.mk (-77) (IntegerType.mk 64) then
      return "RISC-V materialized the wrong immediate"
    return "ok"
  | _ => return "RISC-V did not materialize riscv.li"

/--
info: "ok"
-/
#guard_msgs in
#eval! testRiscvConstantMaterialization

private def testModArithConstantMaterialization : String := Id.run do
  let type : TypeAttr := ModArithType.mk (IntegerAttr.mk 251 (IntegerType.mk 8))
  match (.mod_arith .add : OpCode).materializeConstant (.int 8 (.val 250)) type with
  | some ⟨.mod_arith .constant, props⟩ =>
    if props.value ≠ IntegerAttr.mk 250 (IntegerType.mk 8) then
      return "mod_arith materialized the wrong constant"
    return "ok"
  | _ => return "mod_arith did not materialize mod_arith.constant"

/--
info: "ok"
-/
#guard_msgs in
#eval! testModArithConstantMaterialization

/-- Comb has no constant of its own, so it materializes an HW operation. -/
private def testCombConstantMaterialization : String := Id.run do
  let i32 : TypeAttr := IntegerType.mk 32
  match (.comb .add : OpCode).materializeConstant (.int 32 (.val 7)) i32 with
  | some ⟨.hw .constant, props⟩ =>
    if props.value ≠ IntegerAttr.mk 7 (IntegerType.mk 32) then
      return "comb materialized the wrong constant"
    return "ok"
  | _ => return "comb did not materialize hw.constant"

/--
info: "ok"
-/
#guard_msgs in
#eval! testCombConstantMaterialization

private def testHWConstantMaterialization : String := Id.run do
  let i16 : TypeAttr := IntegerType.mk 16
  match (.hw .output : OpCode).materializeConstant (.int 16 (.val 9)) i16 with
  | some ⟨.hw .constant, props⟩ =>
    if props.value ≠ IntegerAttr.mk 9 (IntegerType.mk 16) then
      return "hw materialized the wrong constant"
    return "ok"
  | _ => return "hw did not materialize hw.constant"

/--
info: "ok"
-/
#guard_msgs in
#eval! testHWConstantMaterialization

private def testLlvmConstantMaterialization : String := Id.run do
  let i32 : TypeAttr := IntegerType.mk 32
  match (.llvm .add : OpCode).materializeConstant (.int 32 (.val 21)) i32 with
  | some ⟨.llvm .mlir__constant, props⟩ =>
    if props.value ≠ .integer (IntegerAttr.mk 21 (IntegerType.mk 32)) then
      return "LLVM materialized the wrong constant"
    return "ok"
  | _ => return "LLVM did not materialize llvm.mlir.constant"

/--
info: "ok"
-/
#guard_msgs in
#eval! testLlvmConstantMaterialization

/-- LLVM can spell poison; the fold decision for `nsw` overflow reaches it. -/
private def testLlvmPoisonMaterialization : String := Id.run do
  let i32 : TypeAttr := IntegerType.mk 32
  match (.llvm .add : OpCode).materializeConstant (.int 32 .poison) i32 with
  | some ⟨.llvm .mlir__poison, _⟩ => return "ok"
  | _ => return "LLVM did not materialize llvm.mlir.poison"

/--
info: "ok"
-/
#guard_msgs in
#eval! testLlvmPoisonMaterialization

/-- Arith has no poison operation of its own, so it reaches for LLVM's. -/
private def testArithPoisonMaterialization : String := Id.run do
  let i32 : TypeAttr := IntegerType.mk 32
  match (.arith .addi : OpCode).materializeConstant (.int 32 .poison) i32 with
  | some ⟨.llvm .mlir__poison, _⟩ => return "ok"
  | _ => return "arith did not materialize llvm.mlir.poison"

/--
info: "ok"
-/
#guard_msgs in
#eval! testArithPoisonMaterialization

/--
The whole way there: an `arith.addi` with `nsw` that overflows evaluates to
poison, the fold decision carries it, and materialization spells it.
-/
private def testNswOverflowFoldsToPoison : String := Id.run do
  let i32 : TypeAttr := IntegerType.mk 32
  let props : propertiesOf (.arith .addi : OpCode) :=
    ArithIntegerOverflowFlagsProperties.mk { nsw := true, nuw := false }
  let operands : Array (Option RuntimeValue) :=
    #[some (.int 32 (.val (BitVec.ofInt 32 2147483647))), some (.int 32 (.val 1))]
  match OpCode.foldsTo (.arith .addi) props #[i32] operands with
  | some #[.useConstant value] =>
    match (.arith .addi : OpCode).materializeConstant value i32 with
    | some ⟨.llvm .mlir__poison, _⟩ => return "ok"
    | _ => return "nsw overflow did not materialize llvm.mlir.poison"
  | _ => return "nsw overflow did not fold"

/--
info: "ok"
-/
#guard_msgs in
#eval! testNswOverflowFoldsToPoison

/--
The dialects with no materializer decline rather than materializing something
from a neighbouring dialect. One representative per dialect; the dispatch in
`OpCode.materializeConstant` lists them all explicitly, so a newly added
dialect cannot silently join this set.
-/
private def testDialectsWithoutMaterializerDecline : String := Id.run do
  let i32 : TypeAttr := IntegerType.mk 32
  let value : RuntimeValue := .int 32 (.val 3)
  let cases : Array (String × OpCode) := #[
    ("riscv_cf", .riscv_cf .branch), ("riscv_stack", .riscv_stack .alloca),
    ("rv64", .rv64 .get_register), ("cf", .cf .br), ("builtin", .builtin .module),
    ("func", .func .call), ("datapath", .datapath .compress),
    ("pdl", .pdl .operation), ("io", .io .send), ("test", .test .test)
  ]
  for (name, opCode) in cases do
    if (opCode.materializeConstant value i32).isSome then
      return s!"{name} materialized a constant but has no materializer"
  return "ok"

/--
info: "ok"
-/
#guard_msgs in
#eval! testDialectsWithoutMaterializerDecline

/-- A value whose width disagrees with the result type is never materialized. -/
private def testBitwidthMismatchIsRejected : String := Id.run do
  let i32 : TypeAttr := IntegerType.mk 32
  match (.arith .addi : OpCode).materializeConstant (.int 16 (.val 7)) i32 with
  | none => return "ok"
  | some _ => return "arith materialized a constant of the wrong width"

/--
info: "ok"
-/
#guard_msgs in
#eval! testBitwidthMismatchIsRejected
