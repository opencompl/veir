import Veir.Input
import Veir.Verifier
import Veir.PatternRewriter.Puddle.Execution
import Veir.Passes.InstCombineLLVM.FreezePushThroughAddCounterexample
import Veir.Passes.InstCombineLLVM.FreezeUndefUseChoiceCounterexample

open Veir Veir.Input Veir.Puddle Veir.Data

private def source := r#""builtin.module"() ({
  %x = "llvm.mlir.poison"() : () -> i2
  %one = "llvm.mlir.constant"() <{value = 1 : i2}> : () -> i2
  %sum = "llvm.add"(%x, %one) : (i2, i2) -> i2
  %root = "llvm.freeze"(%sum) : (i2) -> i2
  "test.test"(%root) : (i2) -> ()
}) : () -> ()"#

private def findOp (ctx : IRContext OpCode) (opcode : OpCode) : Option OperationPtr := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = opcode then return some op
  return none

private def modelSource : LLVM.Int 2 :=
  LLVM.Int.freeze (LLVM.Int.add .poison (.val (BitVec.ofInt 2 1)) false false)

private def modelTarget : LLVM.Int 2 :=
  LLVM.Int.add (LLVM.Int.freeze .poison) (.val (BitVec.ofInt 2 1)) false false

private def regression : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString source.toUTF8
  let some originalRoot := findOp ctx.raw (.llvm .freeze)
    | throw "counterexample fixture has no llvm.freeze root"
  let some sourceAdd := findOp ctx.raw (.llvm .add)
    | throw "counterexample fixture has no llvm.add operand"
  let addProps : NswNuwProperties := sourceAdd.getProperties! ctx.raw (OpCode.llvm .add)
  if addProps.nsw || addProps.nuw then
    throw "counterexample fixture add unexpectedly has poison-generating flags"
  let some rewritten := RewritePattern.applyInContext
      (Pattern.compile Veir.Passes.InstCombineLLVM.FreezePushThroughAddCounterexample.freezePushThroughAdd).run ctx
    | throw "counterexample rewrite driver failed"
  if originalRoot.InBounds rewritten.raw then
    throw "counterexample pattern did not replace the matched freeze root"
  if modelSource != .val 0 then
    throw "Puddle source evaluation was not freeze(poison) = 0"
  if modelTarget != .val 1 then
    throw "Puddle target evaluation was not freeze(poison) + 1 = 1"
  if modelSource = modelTarget then
    throw "Puddle source and target unexpectedly agree"
  rewritten.verify moduleOp

#guard regression = .ok ()

private def freezePoisonOrSource := r#""builtin.module"() ({
  %poison = "llvm.mlir.poison"() : () -> i2
  %frozen = "llvm.freeze"(%poison) : (i2) -> i2
  %zero = "llvm.mlir.constant"() <{value = 0 : i2}> : () -> i2
  %root = "llvm.or"(%frozen, %zero) : (i2, i2) -> i2
  "test.test"(%root) : (i2) -> ()
}) : () -> ()"#

private def freezePoisonOrModelSource : LLVM.Int 2 :=
  LLVM.Int.or (LLVM.Int.freeze .poison) (.val 0) false

private def freezePoisonOrModelTarget : LLVM.Int 2 :=
  LLVM.Int.or (.val (BitVec.ofInt 2 (-1))) (.val 0) false

private def freezePoisonOrRegression : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString freezePoisonOrSource.toUTF8
  let some originalRoot := findOp ctx.raw (.llvm .or)
    | throw "counterexample fixture has no llvm.or root"
  let some sourceFreeze := findOp ctx.raw (.llvm .freeze)
    | throw "counterexample fixture has no llvm.freeze operand"
  let sourceOrProps : DisjointProperties :=
    originalRoot.getProperties! ctx.raw (OpCode.llvm .or)
  if sourceOrProps.disjoint then
    throw "counterexample fixture OR unexpectedly has the disjoint flag"
  let some freezeResult := (sourceFreeze.getResults! ctx.raw)[0]?
    | throw "counterexample fixture freeze has no result"
  let some firstUse := freezeResult.getFirstUse! ctx.raw
    | throw "counterexample fixture freeze has no use"
  if (firstUse.getNextUse! ctx.raw).isSome then
    throw "counterexample fixture freeze does not have exactly one use"
  let some rewritten := RewritePattern.applyInContext
      (Pattern.compile
        Veir.Passes.InstCombineLLVM.FreezeUndefUseChoiceCounterexample.freezePoisonOrAllOnes).run ctx
    | throw "counterexample rewrite driver failed"
  if originalRoot.InBounds rewritten.raw then
    throw "counterexample pattern did not replace the matched OR root"
  if freezePoisonOrModelSource != .val 0 then
    throw "Puddle source evaluation was not freeze(poison) OR 0 = 0"
  if freezePoisonOrModelTarget != .val (BitVec.ofInt 2 (-1)) then
    throw "Puddle target evaluation was not allones OR 0 = allones"
  if freezePoisonOrModelSource = freezePoisonOrModelTarget then
    throw "Puddle source and target unexpectedly agree"
  rewritten.verify moduleOp

#guard freezePoisonOrRegression = .ok ()
