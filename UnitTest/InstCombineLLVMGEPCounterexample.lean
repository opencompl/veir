import Veir.Input
import Veir.Verifier
import Veir.PatternRewriter.Puddle.Execution
import Veir.Passes.InstCombineLLVM.GEPIndexNormalizationCounterexample

open Veir Veir.Input Veir.Puddle Veir.Data

private def source := r#""builtin.module"() ({
  "func.func"() <{function_type = (!llvm.ptr, i8) -> (), sym_name = "f"}> ({
  ^entry(%base : !llvm.ptr, %idx : i8):
    %root = "llvm.getelementptr"(%base, %idx) <{
      rawConstantIndices = array<i32: -2147483648>,
      elem_type = i8,
      noWrapFlags = 0 : i32
    }> : (!llvm.ptr, i8) -> !llvm.ptr
    "test.test"(%root) : (!llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#

private def findOp (ctx : IRContext OpCode) (opcode : OpCode) : Option OperationPtr := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = opcode then return some op
  return none

private def testConsumesGepWithSextIndex (ctx : IRContext OpCode) : Bool := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = (.test .test) then
        match op.getOperand! ctx 0 with
        | .opResult gepResult =>
            if gepResult.op.getOpType! ctx = (.llvm .getelementptr) then
              match gepResult.op.getOperand! ctx 0, gepResult.op.getOperand! ctx 1 with
              | .blockArgument _, .opResult sextResult =>
                  if sextResult.op.getOpType! ctx = (.llvm .sext) then
                    match sextResult.op.getOperand! ctx 0 with
                    | .blockArgument _ => return true
                    | .opResult _ => pure ()
              | _, _ => pure ()
        | .blockArgument _ => pure ()
  return false

private def regression : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString source.toUTF8
  let some originalRoot := findOp ctx.raw (.llvm .getelementptr)
    | throw "counterexample fixture has no llvm.getelementptr root"
  let some rewritten := RewritePattern.applyInContext
      (Pattern.compile
        Veir.Passes.InstCombineLLVM.GEPIndexNormalizationCounterexample.normalizeNarrowGepIndex).run ctx
    | throw "GEP index-normalization rewrite driver failed"
  if originalRoot.InBounds rewritten.raw then
    throw "GEP index-normalization pattern did not replace the matched root"
  if !testConsumesGepWithSextIndex rewritten.raw then
    throw "replacement GEP does not consume a sext of the original i8 index"
  rewritten.verify moduleOp

#guard regression = .ok ()
