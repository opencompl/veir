import Veir.Input
import Veir.Verifier
import Veir.PatternRewriter.Puddle.Execution
import Veir.Passes.InstCombineLLVM.GEPConstantOffsetToPtrAdd
import Veir.Passes.InstCombineLLVM.GEPSplitAddIndex
import Veir.Passes.InstCombineLLVM.GEPSelectConstantIndex
import Veir.Passes.InstCombineLLVM.GEPExactDivToByteIndex
import Veir.Passes.InstCombineLLVM.GEPFoldExactDivisor

open Veir Veir.Input Veir.Puddle Veir.Data

private def constantOffsetSource := r#""builtin.module"() ({
  "func.func"() <{function_type = (!llvm.ptr) -> (), sym_name = "f"}> ({
  ^entry(%base : !llvm.ptr):
    %idx = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %root = "llvm.getelementptr"(%base, %idx) <{
      rawConstantIndices = array<i32: -2147483648>,
      elem_type = i32,
      noWrapFlags = 0 : i32
    }> : (!llvm.ptr, i64) -> !llvm.ptr
    "test.test"(%root) : (!llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#

private def findOp (ctx : IRContext OpCode) (opcode : OpCode) : Option OperationPtr := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = opcode then return some op
  return none

private def testConsumesI8GepBy (ctx : IRContext OpCode) (expected : Int) : Bool := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = (.test .test) then
        match op.getOperand! ctx 0 with
        | .blockArgument _ => return false
        | .opResult gepResult =>
          if gepResult.op.getOpType! ctx != (.llvm .getelementptr) then return false
          let props : GetelementptrProperties :=
            gepResult.op.getProperties! ctx (OpCode.llvm .getelementptr)
          if props.elem_type != (IntegerType.signless 8 : TypeAttr) then return false
          match gepResult.op.getOperand! ctx 0, gepResult.op.getOperand! ctx 1 with
          | .blockArgument _, .opResult constantResult =>
            if constantResult.op.getOpType! ctx != (.llvm .mlir__constant) then return false
            let constantProps : LLVMConstantProperties :=
              constantResult.op.getProperties! ctx (OpCode.llvm .mlir__constant)
            return constantProps.value = LLVMConstantValue.integer
              (IntegerAttr.ofInt expected (IntegerType.signless 64))
          | _, _ => return false
  return false

private def constantOffsetRegression : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString constantOffsetSource.toUTF8
  let some originalRoot := findOp ctx.raw (.llvm .getelementptr)
    | throw "constant-offset fixture has no llvm.getelementptr root"
  let some rewritten := RewritePattern.applyInContext
      (Pattern.compile
        Veir.Passes.InstCombineLLVM.GEPConstantOffsetToPtrAdd.gepConstantOffsetToPtrAdd).run ctx
    | throw "constant-offset GEP rewrite driver failed"
  if originalRoot.InBounds rewritten.raw then
    throw "constant-offset GEP pattern did not replace the matched root"
  if !testConsumesI8GepBy rewritten.raw 12 then
    throw "replacement is not an i8 GEP from the original base by i64 byte offset 12"
  rewritten.verify moduleOp

#guard constantOffsetRegression = .ok ()

private def negativeConstantOffsetSource := r#""builtin.module"() ({
  "func.func"() <{function_type = (!llvm.ptr) -> (), sym_name = "f"}> ({
  ^entry(%base : !llvm.ptr):
    %idx = "llvm.mlir.constant"() <{value = -3 : i64}> : () -> i64
    %root = "llvm.getelementptr"(%base, %idx) <{
      rawConstantIndices = array<i32: -2147483648>,
      elem_type = i32,
      noWrapFlags = 0 : i32
    }> : (!llvm.ptr, i64) -> !llvm.ptr
    "test.test"(%root) : (!llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#

private def negativeConstantOffsetRegression : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString negativeConstantOffsetSource.toUTF8
  let some originalRoot := findOp ctx.raw (.llvm .getelementptr)
    | throw "negative constant-offset fixture has no llvm.getelementptr root"
  let some rewritten := RewritePattern.applyInContext
      (Pattern.compile
        Veir.Passes.InstCombineLLVM.GEPConstantOffsetToPtrAdd.gepConstantOffsetToPtrAdd).run ctx
    | throw "negative constant-offset GEP rewrite driver failed"
  if originalRoot.InBounds rewritten.raw then
    throw "negative constant-offset GEP pattern did not replace the matched root"
  if !testConsumesI8GepBy rewritten.raw (-12) then
    throw "replacement does not use the normalized i64 byte offset -12"
  rewritten.verify moduleOp

#guard negativeConstantOffsetRegression = .ok ()

private def splitAddSource := r#""builtin.module"() ({
  "func.func"() <{function_type = (!llvm.ptr, i64, i64) -> (), sym_name = "f"}> ({
  ^entry(%base : !llvm.ptr, %x : i64, %y : i64):
    %sum = "llvm.add"(%x, %y) : (i64, i64) -> i64
    %root = "llvm.getelementptr"(%base, %sum) <{
      rawConstantIndices = array<i32: -2147483648>,
      elem_type = i32,
      noWrapFlags = 0 : i32
    }> : (!llvm.ptr, i64) -> !llvm.ptr
    "test.test"(%root) : (!llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#

private def testConsumesNestedI32Geps (ctx : IRContext OpCode) : Bool := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = (.test .test) then
        match op.getOperand! ctx 0 with
        | .blockArgument _ => return false
        | .opResult outer =>
          if outer.op.getOpType! ctx != (.llvm .getelementptr) then return false
          match outer.op.getOperand! ctx 0, outer.op.getOperand! ctx 1 with
          | .opResult inner, .blockArgument _ =>
            if inner.op.getOpType! ctx != (.llvm .getelementptr) then return false
            match inner.op.getOperand! ctx 0, inner.op.getOperand! ctx 1 with
            | .blockArgument _, .blockArgument _ => return true
            | _, _ => return false
          | _, _ => return false
  return false

private def splitAddRegression : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString splitAddSource.toUTF8
  let some originalRoot := findOp ctx.raw (.llvm .getelementptr)
    | throw "split-add fixture has no llvm.getelementptr root"
  let some rewritten := RewritePattern.applyInContext
      (Pattern.compile
        Veir.Passes.InstCombineLLVM.GEPSplitAddIndex.gepSplitAddIndex).run ctx
    | throw "split-add GEP rewrite driver failed"
  if originalRoot.InBounds rewritten.raw then
    throw "split-add GEP pattern did not replace the matched root"
  if !testConsumesNestedI32Geps rewritten.raw then
    throw "replacement is not two nested i32 GEPs over the original block arguments"
  rewritten.verify moduleOp

#guard splitAddRegression = .ok ()

private def selectIndexSource := r#""builtin.module"() ({
  "func.func"() <{function_type = (!llvm.ptr, i1) -> (), sym_name = "f"}> ({
  ^entry(%base : !llvm.ptr, %cond : i1):
    %three = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %five = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %seven = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %selected = "llvm.select"(%cond, %five, %seven) : (i1, i64, i64) -> i64
    %inner = "llvm.getelementptr"(%base, %three) <{
      rawConstantIndices = array<i32: -2147483648>, elem_type = i32,
      noWrapFlags = 0 : i32
    }> : (!llvm.ptr, i64) -> !llvm.ptr
    %root = "llvm.getelementptr"(%inner, %selected) <{
      rawConstantIndices = array<i32: -2147483648>, elem_type = i32,
      noWrapFlags = 0 : i32
    }> : (!llvm.ptr, i64) -> !llvm.ptr
    "test.test"(%root) : (!llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#

private def testInputProducer? (ctx : IRContext OpCode) : Option OperationPtr := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = (.test .test) then
        match op.getOperand! ctx 0 with
        | .opResult result => return some result.op
        | .blockArgument _ => return none
  return none

private def integerConstantValue? (ctx : IRContext OpCode)
    (value : ValuePtr) : Option Int :=
  match value with
  | .blockArgument _ => none
  | .opResult result =>
    if result.op.getOpType! ctx != (.llvm .mlir__constant) then none
    else
      let props : LLVMConstantProperties :=
        result.op.getProperties! ctx (OpCode.llvm .mlir__constant)
      match props.value with
      | .integer attr => some attr.value
      | _ => none

private def testConsumesGepOfSelect8And10 (ctx : IRContext OpCode) : Bool := Id.run do
  let some root := testInputProducer? ctx | return false
  if root.getOpType! ctx != (.llvm .getelementptr) then return false
  match root.getOperand! ctx 0, root.getOperand! ctx 1 with
  | .blockArgument _, .opResult selected =>
    if selected.op.getOpType! ctx != (.llvm .select) then return false
    match selected.op.getOperand! ctx 0 with
    | .blockArgument _ =>
      return integerConstantValue? ctx (selected.op.getOperand! ctx 1) = some 8 &&
        integerConstantValue? ctx (selected.op.getOperand! ctx 2) = some 10
    | .opResult _ => return false
  | _, _ => return false

private def selectIndexRegression : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString selectIndexSource.toUTF8
  let some originalRoot := testInputProducer? ctx.raw
    | throw "select-index fixture has no tested defining root"
  let some rewritten := RewritePattern.applyInContext
      (Pattern.compile
        Veir.Passes.InstCombineLLVM.GEPSelectConstantIndex.gepSelectConstantIndex).run ctx
    | throw "select-index GEP rewrite driver failed"
  if originalRoot.InBounds rewritten.raw then
    throw "select-index GEP pattern did not replace the matched root"
  if !testConsumesGepOfSelect8And10 rewritten.raw then
    throw "replacement is not a GEP from the original base by select(cond, 8, 10)"
  rewritten.verify moduleOp

#guard selectIndexRegression = .ok ()

private def exactDivSource := r#""builtin.module"() ({
  "func.func"() <{function_type = (!llvm.ptr, i64) -> (), sym_name = "f"}> ({
  ^entry(%base : !llvm.ptr, %bytes : i64):
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %divided = "llvm.lshr"(%bytes, %two) <{isExact}> : (i64, i64) -> i64
    %root = "llvm.getelementptr"(%base, %divided) <{
      rawConstantIndices = array<i32: -2147483648>, elem_type = i32,
      noWrapFlags = 0 : i32
    }> : (!llvm.ptr, i64) -> !llvm.ptr
    "test.test"(%root) : (!llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#

private def testConsumesDirectI8GepOfArguments (ctx : IRContext OpCode) : Bool := Id.run do
  let some root := testInputProducer? ctx | return false
  if root.getOpType! ctx != (.llvm .getelementptr) then return false
  let props : GetelementptrProperties :=
    root.getProperties! ctx (OpCode.llvm .getelementptr)
  if props.elem_type != (IntegerType.signless 8 : TypeAttr) then return false
  match root.getOperand! ctx 0, root.getOperand! ctx 1 with
  | .blockArgument _, .blockArgument _ => return true
  | _, _ => return false

private def exactDivRegression : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString exactDivSource.toUTF8
  let some originalRoot := testInputProducer? ctx.raw
    | throw "exact-div fixture has no tested defining root"
  let some rewritten := RewritePattern.applyInContext
      (Pattern.compile
        Veir.Passes.InstCombineLLVM.GEPExactDivToByteIndex.gepExactDivToByteIndex).run ctx
    | throw "exact-div GEP rewrite driver failed"
  if originalRoot.InBounds rewritten.raw then
    throw "exact-div GEP pattern did not replace the matched root"
  if !testConsumesDirectI8GepOfArguments rewritten.raw then
    throw "replacement is not an i8 GEP of the original base and byte index"
  rewritten.verify moduleOp

#guard exactDivRegression = .ok ()

private def foldExactDivisorSource := r#""builtin.module"() ({
  "func.func"() <{function_type = (!llvm.ptr, i64) -> (), sym_name = "f"}> ({
  ^entry(%base : !llvm.ptr, %bytes : i64):
    %three = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %divided = "llvm.lshr"(%bytes, %three) <{isExact}> : (i64, i64) -> i64
    %root = "llvm.getelementptr"(%base, %divided) <{
      rawConstantIndices = array<i32: -2147483648>, elem_type = i32,
      noWrapFlags = 0 : i32
    }> : (!llvm.ptr, i64) -> !llvm.ptr
    "test.test"(%root) : (!llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#

private def testConsumesI8GepOfExactShiftByOne (ctx : IRContext OpCode) : Bool := Id.run do
  let some root := testInputProducer? ctx | return false
  if root.getOpType! ctx != (.llvm .getelementptr) then return false
  let gepProps : GetelementptrProperties :=
    root.getProperties! ctx (OpCode.llvm .getelementptr)
  if gepProps.elem_type != (IntegerType.signless 8 : TypeAttr) then return false
  match root.getOperand! ctx 0, root.getOperand! ctx 1 with
  | .blockArgument _, .opResult shifted =>
    if shifted.op.getOpType! ctx != (.llvm .lshr) then return false
    let shiftProps := shifted.op.getProperties! ctx (OpCode.llvm .lshr)
    if !shiftProps.exact then return false
    match shifted.op.getOperand! ctx 0 with
    | .blockArgument _ =>
      return integerConstantValue? ctx (shifted.op.getOperand! ctx 1) = some 1
    | .opResult _ => return false
  | _, _ => return false

private def foldExactDivisorRegression : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString foldExactDivisorSource.toUTF8
  let some originalRoot := testInputProducer? ctx.raw
    | throw "fold-exact-divisor fixture has no tested defining root"
  let some rewritten := RewritePattern.applyInContext
      (Pattern.compile
        Veir.Passes.InstCombineLLVM.GEPFoldExactDivisor.gepFoldExactDivisor).run ctx
    | throw "fold-exact-divisor GEP rewrite driver failed"
  if originalRoot.InBounds rewritten.raw then
    throw "fold-exact-divisor GEP pattern did not replace the matched root"
  if !testConsumesI8GepOfExactShiftByOne rewritten.raw then
    throw "replacement is not an i8 GEP by an exact lshr of the byte index by one"
  rewritten.verify moduleOp

#guard foldExactDivisorRegression = .ok ()
