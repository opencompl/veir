import UnitTest.DataFlowFramework.Helpers

import Veir.Fold

/-! Tests for `PatternRewriter.createOrFoldOp!`. -/

open Veir

/-- Find all operations with the given opcode. -/
private def findOps (ctx : IRContext OpCode) (opType : OpCode) : Array OperationPtr := Id.run do
  let mut result := #[]
  for op in ctx.operations.keys do
    if op.getOpType! ctx = opType then
      result := result.push op
  return result

/-- Find the `arith.constant` operation with the given value. -/
private def constWithValue (ctx : IRContext OpCode) (v : Int) : Option OperationPtr := Id.run do
  for op in ctx.operations.keys do
    if op.getOpType! ctx = .arith .constant then
      if (op.getProperties! ctx (.arith .constant)).value.value = v then
        return some op
  return none

private def foldTestModule : String :=
  "\"builtin.module\"() ({
    \"func.func\"() <{function_type = (i32) -> i32, sym_name = \"main\"}> ({
    ^bb0(%x : i32):
      %c0 = \"arith.constant\"() <{ \"value\" = 0 : i32 }> : () -> i32
      %c7 = \"arith.constant\"() <{ \"value\" = 7 : i32 }> : () -> i32
      %c8 = \"arith.constant\"() <{ \"value\" = 8 : i32 }> : () -> i32
      \"func.return\"(%x) : (i32) -> ()
    }) : () -> ()
  }) : () -> ()"

private def testCreateOrFold : String := Id.run do
  match parseTopLevelOp foldTestModule with
  | .error e => return s!"parse error: {e}"
  | .ok (_, parserState) =>
    let wfCtx := parserState.ctx
    let ctx := wfCtx.raw
    let some retOp := (findOps ctx (.func .return))[0]? | return "missing func.return"
    let some c0 := constWithValue ctx 0 | return "missing constant 0"
    let some c7 := constWithValue ctx 7 | return "missing constant 7"
    let some c8 := constWithValue ctx 8 | return "missing constant 8"
    let x := (retOp.getOperands! ctx)[0]!
    let c0v := (c0.getResults! ctx)[0]!
    let c7v := (c7.getResults! ctx)[0]!
    let c8v := (c8.getResults! ctx)[0]!
    let i32 := x.getType! ctx
    let rewriter : PatternRewriter OpCode :=
      { ctx := wfCtx, hasDoneAction := false, worklist := .empty }
    let mut errors : Array String := #[]

    -- addi(7, 8) is evaluated to a constant 15; no addi is created.
    match rewriter.createOrFoldOp! (.arith .addi) #[i32] #[c7v, c8v] default (.before retOp) with
    | none => errors := errors.push "evaluate: createOrFoldOp! failed"
    | some (rw, vals) =>
      let ctx' := rw.ctx.raw
      match vals[0]?.bind (·.getDefiningOp! ctx') with
      | none => errors := errors.push "evaluate: expected an op result"
      | some defOp =>
        if defOp.getOpType! ctx' ≠ .arith .constant then
          errors := errors.push "evaluate: expected an arith.constant"
        else if (defOp.getProperties! ctx' (.arith .constant)).value.value ≠ 15 then
          errors := errors.push "evaluate: expected the value 15"
      if (findOps ctx' (.arith .addi)).size ≠ 0 then
        errors := errors.push "evaluate: an arith.addi was created"

    -- addi(x, 0) folds to x; no operation is created at all.
    match rewriter.createOrFoldOp! (.arith .addi) #[i32] #[x, c0v] default (.before retOp) with
    | none => errors := errors.push "identity: createOrFoldOp! failed"
    | some (rw, vals) =>
      if vals[0]? ≠ some x then
        errors := errors.push "identity: expected the operand x"
      if rw.ctx.raw.operations.size ≠ ctx.operations.size then
        errors := errors.push "identity: an operation was created"

    -- divsi(x, 0) is immediate UB and folds to poison.
    match rewriter.createOrFoldOp! (.arith .divsi) #[i32] #[x, c0v] default (.before retOp) with
    | none => errors := errors.push "ub: createOrFoldOp! failed"
    | some (rw, vals) =>
      let ctx' := rw.ctx.raw
      match vals[0]?.bind (·.getDefiningOp! ctx') with
      | none => errors := errors.push "ub: expected an op result"
      | some defOp =>
        if defOp.getOpType! ctx' ≠ .llvm .mlir__poison then
          errors := errors.push "ub: expected an llvm.mlir.poison"

    -- addi(x, 7) does not fold: a regular addi is created.
    match rewriter.createOrFoldOp! (.arith .addi) #[i32] #[x, c7v] default (.before retOp) with
    | none => errors := errors.push "no-fold: createOrFoldOp! failed"
    | some (rw, vals) =>
      let ctx' := rw.ctx.raw
      match vals[0]?.bind (·.getDefiningOp! ctx') with
      | none => errors := errors.push "no-fold: expected an op result"
      | some defOp =>
        if defOp.getOpType! ctx' ≠ .arith .addi then
          errors := errors.push "no-fold: expected an arith.addi"

    if errors.isEmpty then return "ok"
    return String.intercalate "\n" errors.toList

/--
info: "ok"
-/
#guard_msgs in
#eval! testCreateOrFold
