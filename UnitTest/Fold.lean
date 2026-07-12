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

/-! ## `mod_arith`: uninterpreted dialect, table-computed folds -/

/-- Find the `mod_arith.constant` operation with the given value. -/
private def modArithConstWithValue (ctx : IRContext OpCode) (v : Int) : Option OperationPtr :=
  Id.run do
    for op in ctx.operations.keys do
      if op.getOpType! ctx = .mod_arith .constant then
        if (op.getProperties! ctx (.mod_arith .constant)).value.value = v then
          return some op
    return none

private def modArithTestModule : String :=
  "\"builtin.module\"() ({
    \"func.func\"() <{function_type = (!mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>, sym_name = \"main\"}> ({
    ^bb0(%x : !mod_arith.int<17 : i32>):
      %c0 = \"mod_arith.constant\"() <{ \"value\" = 0 : i32 }> : () -> !mod_arith.int<17 : i32>
      %c13 = \"mod_arith.constant\"() <{ \"value\" = 13 : i32 }> : () -> !mod_arith.int<17 : i32>
      %c7 = \"mod_arith.constant\"() <{ \"value\" = 7 : i32 }> : () -> !mod_arith.int<17 : i32>
      \"func.return\"(%x) : (!mod_arith.int<17 : i32>) -> ()
    }) : () -> ()
  }) : () -> ()"

private def testCreateOrFoldModArith : String := Id.run do
  match parseTopLevelOp modArithTestModule with
  | .error e => return s!"parse error: {e}"
  | .ok (_, parserState) =>
    let wfCtx := parserState.ctx
    let ctx := wfCtx.raw
    let some retOp := (findOps ctx (.func .return))[0]? | return "missing func.return"
    let some c0 := modArithConstWithValue ctx 0 | return "missing constant 0"
    let some c13 := modArithConstWithValue ctx 13 | return "missing constant 13"
    let some c7 := modArithConstWithValue ctx 7 | return "missing constant 7"
    let x := (retOp.getOperands! ctx)[0]!
    let c0v := (c0.getResults! ctx)[0]!
    let c13v := (c13.getResults! ctx)[0]!
    let c7v := (c7.getResults! ctx)[0]!
    let mty := x.getType! ctx
    let rewriter : PatternRewriter OpCode :=
      { ctx := wfCtx, hasDoneAction := false, worklist := .empty }
    let mut errors : Array String := #[]

    -- add(13, 7) is computed in the fold table: 20 = 3 (mod 17).
    match rewriter.createOrFoldOp! (.mod_arith .add) #[mty] #[c13v, c7v] default
        (.before retOp) with
    | none => errors := errors.push "table-fold: createOrFoldOp! failed"
    | some (rw, vals) =>
      let ctx' := rw.ctx.raw
      match vals[0]?.bind (·.getDefiningOp! ctx') with
      | none => errors := errors.push "table-fold: expected an op result"
      | some defOp =>
        if defOp.getOpType! ctx' ≠ .mod_arith .constant then
          errors := errors.push "table-fold: expected a mod_arith.constant"
        else if (defOp.getProperties! ctx' (.mod_arith .constant)).value.value ≠ 3 then
          errors := errors.push "table-fold: expected the value 3"
      if (findOps ctx' (.mod_arith .add)).size ≠ 0 then
        errors := errors.push "table-fold: a mod_arith.add was created"

    -- add(x, 0) folds to x; no operation is created.
    match rewriter.createOrFoldOp! (.mod_arith .add) #[mty] #[x, c0v] default
        (.before retOp) with
    | none => errors := errors.push "identity: createOrFoldOp! failed"
    | some (rw, vals) =>
      if vals[0]? ≠ some x then
        errors := errors.push "identity: expected the operand x"
      if rw.ctx.raw.operations.size ≠ ctx.operations.size then
        errors := errors.push "identity: an operation was created"

    -- sub(x, 0) folds to x.
    match rewriter.createOrFoldOp! (.mod_arith .sub) #[mty] #[x, c0v] default
        (.before retOp) with
    | none => errors := errors.push "sub-identity: createOrFoldOp! failed"
    | some (_, vals) =>
      if vals[0]? ≠ some x then
        errors := errors.push "sub-identity: expected the operand x"

    -- mul(x, 13) does not fold: a regular mod_arith.mul is created.
    match rewriter.createOrFoldOp! (.mod_arith .mul) #[mty] #[x, c13v] default
        (.before retOp) with
    | none => errors := errors.push "no-fold: createOrFoldOp! failed"
    | some (rw, vals) =>
      let ctx' := rw.ctx.raw
      match vals[0]?.bind (·.getDefiningOp! ctx') with
      | none => errors := errors.push "no-fold: expected an op result"
      | some defOp =>
        if defOp.getOpType! ctx' ≠ .mod_arith .mul then
          errors := errors.push "no-fold: expected a mod_arith.mul"

    if errors.isEmpty then return "ok"
    return String.intercalate "\n" errors.toList

/--
info: "ok"
-/
#guard_msgs in
#eval! testCreateOrFoldModArith
