import UnitTest.DataFlowFramework.Helpers
import Veir.Fold.ConstantValue

/-! Tests for reading constant-like IR values as interpreter runtime values. -/

open Veir

/-- Find the first operation with the given opcode. -/
private def findOp (ctx : IRContext OpCode) (opType : OpCode) : Option OperationPtr := Id.run do
  for op in ctx.operations.keys do
    if op.getOpType! ctx = opType then
      return some op
  return none

/-- Find a `mod_arith.constant` with the given integer property. -/
private def findModArithConstant (ctx : IRContext OpCode) (value : Int) : Option OperationPtr :=
  Id.run do
    for op in ctx.operations.keys do
      if op.getOpType! ctx = .mod_arith .constant then
        if (op.getProperties! ctx (.mod_arith .constant)).value.value = value then
          return some op
    return none

private def constantValueModule : String :=
  "\"builtin.module\"() ({
    \"func.func\"() <{function_type = () -> i8, sym_name = \"main\"}> ({
      %arith = \"arith.constant\"() <{ \"value\" = -1 : i8 }> : () -> i8
      %llvm = \"llvm.mlir.constant\"() <{ \"value\" = 257 : i16 }> : () -> i8
      %poison = \"llvm.mlir.poison\"() : () -> i16
      %li = \"riscv.li\"() <{ \"value\" = -1 : i32 }> : () -> !riscv.reg
      %mod13 = \"mod_arith.constant\"() <{ \"value\" = 13 : i32 }> : () -> !mod_arith.int<17 : i32>
      %mod20 = \"mod_arith.constant\"() <{ \"value\" = 20 : i32 }> : () -> !mod_arith.int<17 : i32>
      %modNeg = \"mod_arith.constant\"() <{ \"value\" = -1 : i32 }> : () -> !mod_arith.int<17 : i32>
      %sum = \"arith.addi\"(%arith, %arith) : (i8, i8) -> i8
      \"func.return\"(%sum) : (i8) -> ()
    }) : () -> ()
  }) : () -> ()"

private def testConstantValue : String := Id.run do
  let .ok (_, parserState) := parseTopLevelOp constantValueModule
    | return "failed to parse test module"
  let ctx := parserState.ctx.raw
  let mut errors : Array String := #[]

  let some arithOp := findOp ctx (.arith .constant)
    | return "missing arith.constant"
  match (arithOp.getResult 0).constantValue ctx with
  | some (.int 8 (.val value)) =>
    if value ≠ BitVec.ofInt 8 (-1) then
      errors := errors.push "arith.constant produced the wrong value"
  | _ => errors := errors.push "failed to read arith.constant"

  let some llvmOp := findOp ctx (.llvm .mlir__constant)
    | return "missing llvm.mlir.constant"
  match (llvmOp.getResult 0).constantValue ctx with
  | some (.int 8 (.val value)) =>
    if value ≠ BitVec.ofInt 8 257 then
      errors := errors.push "llvm.mlir.constant did not use the result bitwidth"
  | _ => errors := errors.push "failed to read llvm.mlir.constant"

  let some poisonOp := findOp ctx (.llvm .mlir__poison)
    | return "missing llvm.mlir.poison"
  match (poisonOp.getResult 0).constantValue ctx with
  | some (.int 16 .poison) => pure ()
  | _ => errors := errors.push "failed to read llvm.mlir.poison"

  let some liOp := findOp ctx (.riscv .li)
    | return "missing riscv.li"
  match (liOp.getResult 0).constantValue ctx with
  | some (.reg value) =>
    if value.val ≠ BitVec.ofInt 64 (-1) then
      errors := errors.push "riscv.li produced the wrong register value"
  | _ => errors := errors.push "failed to read riscv.li"

  let some mod13Op := findModArithConstant ctx 13
    | return "missing canonical mod_arith.constant"
  match (mod13Op.getResult 0).constantValue ctx with
  | some (.int 32 (.val value)) =>
    if value ≠ BitVec.ofInt 32 13 then
      errors := errors.push "mod_arith.constant produced the wrong residue"
  | _ => errors := errors.push "failed to read canonical mod_arith.constant"

  let some mod20Op := findModArithConstant ctx 20
    | return "missing noncanonical mod_arith.constant"
  if ((mod20Op.getResult 0).constantValue ctx).isSome then
    errors := errors.push "accepted a noncanonical mod_arith.constant"

  let some modNegOp := findModArithConstant ctx (-1)
    | return "missing negative mod_arith.constant"
  if ((modNegOp.getResult 0).constantValue ctx).isSome then
    errors := errors.push "accepted a negative mod_arith.constant"

  let some addOp := findOp ctx (.arith .addi)
    | return "missing non-constant operation"
  if ((addOp.getResult 0).constantValue ctx).isSome then
    errors := errors.push "accepted a value not defined by a constant-like operation"

  if errors.isEmpty then "ok" else String.intercalate "\n" errors.toList

/--
info: "ok"
-/
#guard_msgs in
#eval! testConstantValue
