import Mlir.Prelude
import Mlir.Core.Basic
import Mlir.Builder
import Mlir.Printer
import Mlir.PatternRewriter
import Mlir.Rewriter

namespace Mlir.Benchmarks

abbrev OpCode.module := 0
abbrev OpCode.constant := 1
abbrev OpCode.addi := 2
abbrev OpCode.muli := 4
abbrev OpCode.andi := 5
abbrev OpCode.test := 99

namespace Pattern

def addIConstantFolding (rewriter: PatternRewriter) (op: OperationPtr) : Option PatternRewriter := do
  -- Check that the operation is an arith.addi operation
  if op.getOpType rewriter.ctx sorry ≠ OpCode.addi then
    return rewriter

  -- Get the lhs and check that it is a constant
  let lhsValuePtr := op.getOperand rewriter.ctx 0 (by sorry) (by sorry)
  let lhsOp ← match lhsValuePtr with
  | ValuePtr.opResult lhsOpResultPtr => some lhsOpResultPtr.op
  | _ => none
  let lhsOpStruct := lhsOp.get rewriter.ctx (by sorry)
  if lhsOpStruct.opType ≠ OpCode.constant then
    return rewriter

  -- Get the rhs and check that it is a constant
  let rhsValuePtr := op.getOperand rewriter.ctx 1 (by sorry) (by sorry)
  let rhsOp ← match rhsValuePtr with
  | ValuePtr.opResult rhsOpResultPtr => some rhsOpResultPtr.op
  | _ => none
  let rhsOpStruct := rhsOp.get rewriter.ctx (by sorry)
  if rhsOpStruct.opType ≠ OpCode.constant then
    return rewriter

  -- Sum both constant values
  let newVal := lhsOpStruct.properties + rhsOpStruct.properties
  let (rewriter, newOp) ← rewriter.createOp OpCode.constant 1 #[] 0 newVal (InsertPoint.Before op) sorry sorry
  let mut rewriter ← rewriter.replaceOp op newOp sorry sorry sorry

  if (lhsValuePtr.getFirstUse rewriter.ctx (by sorry)).isNone then
    rewriter ← rewriter.eraseOp lhsOp sorry sorry
  if (rhsValuePtr.getFirstUse rewriter.ctx (by sorry)).isNone then
    rewriter ← rewriter.eraseOp rhsOp sorry sorry
  return rewriter

def addIZeroFolding (rewriter: PatternRewriter) (op: OperationPtr) : Option PatternRewriter := do
  if op.getOpType rewriter.ctx sorry ≠ OpCode.addi then
    return rewriter

  -- Get the rhs and check that it is the constant 0
  let rhsValuePtr := op.getOperand rewriter.ctx 1 (by sorry) (by sorry)
  let rhsOp ← match rhsValuePtr with
  | ValuePtr.opResult rhsOpResultPtr => some rhsOpResultPtr.op
  | _ => none
  let rhsOpStruct := rhsOp.get rewriter.ctx (by sorry)
  if rhsOpStruct.opType ≠ OpCode.constant then
    return rewriter
  if rhsOpStruct.properties ≠ 0 then
    return rewriter

  -- Get the lhs value
  let lhsValuePtr := op.getOperand rewriter.ctx 0 (by sorry) (by sorry)

  let opValuePtr := op.getResult 0
  let mut rewriter ← rewriter.replaceValue opValuePtr lhsValuePtr sorry sorry
  rewriter ← rewriter.eraseOp op sorry sorry

  if (rhsValuePtr.getFirstUse rewriter.ctx (by sorry)).isNone then
    rewriter ← rewriter.eraseOp rhsOp sorry sorry
  return rewriter

def mulITwoReduce (rewriter: PatternRewriter) (op: OperationPtr) : Option PatternRewriter := do
  if op.getOpType rewriter.ctx sorry ≠ OpCode.muli then
    return rewriter

  -- Get the rhs and check that it is the constant 2
  let rhsValuePtr := op.getOperand rewriter.ctx 1 (by sorry) (by sorry)
  let rhsOp ← match rhsValuePtr with
  | ValuePtr.opResult rhsOpResultPtr => some rhsOpResultPtr.op
  | _ => none
  let rhsOpStruct := rhsOp.get rewriter.ctx (by sorry)
  if rhsOpStruct.opType ≠ OpCode.constant then
    return rewriter
  if rhsOpStruct.properties ≠ 2 then
    return rewriter

  -- Get the lhs value
  let lhsValuePtr := op.getOperand rewriter.ctx 0 (by sorry) (by sorry)

  let (rewriter, newOp) ← rewriter.createOp OpCode.addi 1 #[lhsValuePtr, lhsValuePtr] 0 0 (InsertPoint.Before op) sorry sorry
  let mut rewriter ← rewriter.replaceOp op newOp sorry sorry sorry

  if (rhsValuePtr.getFirstUse rewriter.ctx (by sorry)).isNone then
    rewriter ← rewriter.eraseOp rhsOp sorry sorry
  return rewriter

end Pattern

-- Rewrites as above but without using the PatternRewriter interface, instead
-- applying the rewrites in custom locations
namespace Custom

abbrev Pattern := IRContext → OperationPtr → Option IRContext

def addIConstantFolding (ctx: IRContext) (op: OperationPtr) : Option IRContext := do
  -- Check that the operation is an arith.addi operation
  if op.getOpType ctx sorry ≠ OpCode.addi then
    return ctx

  -- Get the lhs and check that it is a constant
  let lhsValuePtr := op.getOperand ctx 0 (by sorry) (by sorry)
  let lhsOp ← match lhsValuePtr with
  | ValuePtr.opResult lhsOpResultPtr => some lhsOpResultPtr.op
  | _ => none
  let lhsOpStruct := lhsOp.get ctx (by sorry)
  if lhsOpStruct.opType ≠ OpCode.constant then
    return ctx

  -- Get the rhs and check that it is a constant
  let rhsValuePtr := op.getOperand ctx 1 (by sorry) (by sorry)
  let rhsOp ← match rhsValuePtr with
  | ValuePtr.opResult rhsOpResultPtr => some rhsOpResultPtr.op
  | _ => none
  let rhsOpStruct := rhsOp.get ctx (by sorry)
  if rhsOpStruct.opType ≠ OpCode.constant then
    return ctx

  -- Sum both constant values
  let newVal := lhsOpStruct.properties + rhsOpStruct.properties
  let (ctx, newOp) ← Builder.createOp ctx OpCode.constant 1 #[] 0 newVal (InsertPoint.Before op) sorry sorry sorry
  let mut ctx ← Rewriter.replaceOp? ctx op newOp sorry sorry sorry sorry

  if (lhsValuePtr.getFirstUse ctx (by sorry)).isNone then
    ctx ← Rewriter.eraseOp ctx lhsOp sorry sorry sorry
  if (rhsValuePtr.getFirstUse ctx (by sorry)).isNone then
    ctx ← Rewriter.eraseOp ctx rhsOp sorry sorry sorry
  return ctx

def addIZeroFolding (ctx: IRContext) (op: OperationPtr) : Option IRContext := do
  if op.getOpType ctx sorry ≠ OpCode.addi then
    return ctx

  -- Get the rhs and check that it is the constant 0
  let rhsValuePtr := op.getOperand ctx 1 (by sorry) (by sorry)
  let rhsOp ← match rhsValuePtr with
  | ValuePtr.opResult rhsOpResultPtr => some rhsOpResultPtr.op
  | _ => none
  let rhsOpStruct := rhsOp.get ctx (by sorry)
  if rhsOpStruct.opType ≠ OpCode.constant then
    return ctx
  if rhsOpStruct.properties ≠ 0 then
    return ctx

  -- Get the lhs value
  let lhsValuePtr := op.getOperand ctx 0 (by sorry) (by sorry)

  let oldVal := op.getResult 0
  let mut ctx ← Rewriter.replaceValue? ctx oldVal lhsValuePtr sorry sorry sorry
  ctx ← Rewriter.eraseOp ctx op sorry sorry sorry

  if (rhsValuePtr.getFirstUse ctx (by sorry)).isNone then
    ctx ← Rewriter.eraseOp ctx rhsOp sorry sorry sorry
  return ctx

def mulITwoReduce (ctx: IRContext) (op: OperationPtr) : Option IRContext := do
  if op.getOpType ctx sorry ≠ OpCode.muli then
    return ctx

  -- Get the rhs and check that it is the constant 2
  let rhsValuePtr := op.getOperand ctx 1 (by sorry) (by sorry)
  let rhsOp ← match rhsValuePtr with
  | ValuePtr.opResult rhsOpResultPtr => some rhsOpResultPtr.op
  | _ => none
  let rhsOpStruct := rhsOp.get ctx (by sorry)
  if rhsOpStruct.opType ≠ OpCode.constant then
    return ctx
  if rhsOpStruct.properties ≠ 2 then
    return ctx

  -- Get the lhs value
  let lhsValuePtr := op.getOperand ctx 0 (by sorry) (by sorry)

  let (ctx, newOp) ← Builder.createOp ctx OpCode.addi 1 #[lhsValuePtr, lhsValuePtr] 0 0 (InsertPoint.Before op) sorry sorry sorry
  let mut ctx ← Rewriter.replaceOp? ctx op newOp sorry sorry sorry sorry

  if (rhsValuePtr.getFirstUse ctx (by sorry)).isNone then
    ctx ← Rewriter.eraseOp ctx rhsOp sorry sorry sorry
  return ctx

-- Rewrites the first instance of an opcode in the program with the given pattern,
-- within a program consisting of one region/block
def rewriteFirst (ctx: IRContext) (opcode: Nat) (rewrite: Pattern) : Option IRContext := do
  let topLevelOp := ctx.topLevelOp
  let region := topLevelOp.getRegion! ctx 0
  let block := (region.get ctx (by sorry)).firstBlock.get!
  let mut op ← (block.get! ctx).firstOp

  while op.getOpType ctx sorry ≠ opcode do
    op ← (op.get! ctx).next

  rewrite ctx op

def rewriteFirstAddI (ctx: IRContext) (rewrite: Pattern) : Option IRContext :=
  rewriteFirst ctx OpCode.addi rewrite

def rewriteForwards (ctx: IRContext) (rewrite: Pattern) : Option IRContext := do
  let topLevelOp := ctx.topLevelOp
  let region := topLevelOp.getRegion! ctx 0
  let block := (region.get ctx (by sorry)).firstBlock.get!

  let mut maybeOp := (block.get! ctx).firstOp
  let mut ctx := ctx
  while h : maybeOp.isSome do
    let op := maybeOp.get h
    let next := (op.get! ctx).next
    -- TODO: This should be work but for some reason is not unique
    -- ctx := dbgTraceIfShared "rewriteForwards" ctx
    -- ctx ← rewrite ctx op
    ctx := rewrite ctx op |>.get!
    maybeOp := next

  ctx

end Custom

namespace Program

def empty : Option (IRContext × InsertPoint) := do
  let (ctx, topLevelOp) ← IRContext.create
  let region := topLevelOp.getRegion! ctx 0
  let block := (region.get ctx (by sorry)).firstBlock.get!
  let insertPoint := InsertPoint.AtEnd block
  (ctx, insertPoint)


-- Create a program that looks like:
-- func @main() -> u64 {
--   %0 = arith.constant [root] : u64
--   %1 = arith.constant [inc] : u64
--   %2 = [opcode] %0, %1 : u64
--   %3 = arith.constant [inc] : u64
--   %4 = [opcode] %2, %3 : u64
--   ...
def constFoldTree (opcode: Nat) (size pc: Nat) (root inc: UInt64) : Option IRContext := do
  let (gctx, insertPoint) ← empty
  let mut (gctx, gacc) ← Builder.createOp gctx OpCode.constant 1 #[] 0 root insertPoint sorry sorry sorry
  for i in [0:size] do
    let thisOp := if (i % 100 < pc) then opcode else OpCode.andi

    let (ctx, acc) := (gctx, gacc)
    let (ctx, rhsOp) ← Builder.createOp ctx OpCode.constant 1 #[] 0 inc insertPoint sorry sorry sorry
    let lhsVal := acc.getResult 0
    let rhsVal := rhsOp.getResult 0
    let (ctx, acc) ← Builder.createOp ctx thisOp 1 #[lhsVal, rhsVal] 0 0 insertPoint sorry sorry sorry
    (gctx, gacc) := (ctx, acc)

  let accRes := gacc.getResult 0
  let (ctx, op) ← Builder.createOp gctx OpCode.test 0 #[accRes] 0 0 insertPoint sorry sorry sorry
  ctx

def addZeroTree (size pc: Nat) : Option IRContext :=
  constFoldTree OpCode.addi size pc 42 0

def addOneTree (size pc: Nat) : Option IRContext :=
  constFoldTree OpCode.addi size pc 42 1

def mulTwoTree (size pc: Nat) : Option IRContext :=
  constFoldTree OpCode.muli size pc 42 2


-- Create a program that looks like:
-- func @main() -> u64 {
--   %0 = arith.constant [root] : u64
--   %reuse = arith.constant [inc]: u64
--   %2 = [opcode] %0, %reuse : u64
--   %3 = [opcode] %2, %reuse : u64
--   ...
def constReuseTree (opcode: Nat) (size pc: Nat) (root inc: UInt64) : Option IRContext := do
  let (ctx, insertPoint) ← empty
  let (ctx, acc) ← Builder.createOp ctx OpCode.constant 1 #[] 0 root insertPoint sorry sorry sorry
  let (ctx, reuse) ← Builder.createOp ctx OpCode.constant 1 #[] 0 inc insertPoint sorry sorry sorry

  let mut (gctx, gacc) := (ctx, acc)
  for i in [0:size] do
    let thisOp := if (i % 100 < pc) then opcode else OpCode.andi

    let (ctx, acc) := (gctx, gacc)
    let lhsVal := acc.getResult 0
    let rhsVal := reuse.getResult 0
    let (ctx, acc) ← Builder.createOp ctx thisOp 1 #[lhsVal, rhsVal] 0 0 insertPoint sorry sorry sorry
    (gctx, gacc) := (ctx, acc)
  let (ctx, acc) := (gctx, gacc)

  let accRes := acc.getResult 0
  let (ctx, op) ← Builder.createOp ctx OpCode.test 0 #[accRes] 0 0 insertPoint sorry sorry sorry
  ctx

def addZeroReuseTree (size pc: Nat) : Option IRContext :=
  constReuseTree OpCode.addi size pc 42 0

-- Create a program that looks like:
-- func @main() -> u64 {
--   %0 = arith.constant [lhs] : u64
--   %1 = arith.constant [rhs] : u64
--   %reuse = [opcode] %0, %1 : u64
--   %3 = [opcode] %reuse, %reuse : u64
--   %4 = [opcode] %3, %reuse : u64
--   %5 = [opcode] %4, %reuse : u64
--   ...
def constLotsOfReuseTree (opcode: Nat) (size pc: Nat) (lhs rhs: UInt64) : Option IRContext := do
  let (ctx, insertPoint) ← empty
  let (ctx, lhsOp) ← Builder.createOp ctx OpCode.constant 1 #[] 0 lhs insertPoint sorry sorry sorry
  let (ctx, rhsOp) ← Builder.createOp ctx OpCode.constant 1 #[] 0 rhs insertPoint sorry sorry sorry
  let lhsVal := lhsOp.getResult 0
  let rhsVal := rhsOp.getResult 0
  let (ctx, reuse) ← Builder.createOp ctx opcode 1 #[lhsVal, rhsVal] 0 0 insertPoint sorry sorry sorry

  let mut (gctx, gacc) := (ctx, reuse)
  for i in [0:size] do
    let thisOp := if (i % 100 < pc) then opcode else OpCode.andi

    let (ctx, acc) := (gctx, gacc)
    let lhsVal := acc.getResult 0
    let rhsVal := reuse.getResult 0
    let (ctx, acc) ← Builder.createOp ctx thisOp 1 #[lhsVal, rhsVal] 0 0 insertPoint sorry sorry sorry
    (gctx, gacc) := (ctx, acc)
  let (ctx, acc) := (gctx, gacc)

  let accRes := acc.getResult 0
  let (ctx, op) ← Builder.createOp ctx OpCode.test 0 #[accRes] 0 0 insertPoint sorry sorry sorry
  ctx

def addZeroLotsOfReuseTree (size pc: Nat) : Option IRContext :=
  constLotsOfReuseTree OpCode.addi size pc 42 0

end Program

def rewriteWorklist (program: IRContext) (rewriter: RewritePattern) : Option IRContext :=
  RewritePattern.applyInContext rewriter program sorry

def print (program: Option IRContext) : IO Unit := do
  if let some ctx := program then
    Printer.printModule ctx ctx.topLevelOp

def time {α : Type} (name: String) (f: Unit → IO α) (quiet: Bool) : IO α := do
  let startTime ← IO.monoNanosNow
  let res ← f ()
  let endTime ← IO.monoNanosNow
  let elapsedTime := endTime - startTime
  if not quiet then
    IO.println s!"{name} time (s): {elapsedTime.toFloat / 1000000000}"
  return res

def run {pattern : Type} (size pc: Nat) (create: Nat → Nat → Option IRContext)
    (rewriteDriver: IRContext → pattern → Option IRContext)
    (rewritePattern: pattern)
    (doPrint: Bool) (quiet: Bool := false) : OptionT IO IRContext := do
  let ctx ← time "create" (fun () => return create size pc) quiet
  let ctx ← time "rewrite" (fun () => return rewriteDriver ctx rewritePattern) quiet
  if doPrint && !quiet then
    print ctx
  return ctx

def runBenchmarkWithResult (benchmark: String) (n pc: Nat) (quiet: Bool := false) : OptionT IO IRContext :=
  open Program in
  open Custom in

  let print := pc = 100

  match benchmark with
  | "add-fold-worklist" =>            run n pc addOneTree              rewriteWorklist  Pattern.addIConstantFolding print quiet
  | "add-zero-worklist" =>            run n pc addZeroTree             rewriteWorklist  Pattern.addIZeroFolding     print quiet
  | "add-zero-reuse-worklist" =>      run n pc addZeroReuseTree        rewriteWorklist  Pattern.addIZeroFolding     print quiet
  | "mul-two-worklist" =>             run n pc mulTwoTree              rewriteWorklist  Pattern.mulITwoReduce       false quiet

  | "add-fold-forwards" =>            run n pc addOneTree              rewriteForwards  Custom.addIConstantFolding  print quiet
  | "add-zero-forwards" =>            run n pc addZeroTree             rewriteForwards  Custom.addIZeroFolding      print quiet
  | "add-zero-reuse-forwards" =>      run n pc addZeroReuseTree        rewriteForwards  Custom.addIZeroFolding      print quiet
  | "mul-two-forwards" =>             run n pc mulTwoTree              rewriteForwards  Custom.mulITwoReduce        false quiet

  | "add-zero-reuse-first" =>         run n pc addZeroReuseTree        rewriteFirstAddI Custom.addIZeroFolding      false quiet
  | "add-zero-lots-of-reuse-first" => run n pc addZeroLotsOfReuseTree  rewriteFirstAddI Custom.addIZeroFolding      false quiet

  | _ => panic! "Unsupported benchmark"

def runBenchmark (benchmark: String) (n pc: Nat) : IO Unit := do
  let _ ← runBenchmarkWithResult benchmark n pc
  return ()

def testBench (benchmark: String) (n: Nat) : IO Unit := do
  let ctx ← runBenchmarkWithResult benchmark n 100 (quiet := true)
  print ctx

/--
info:
builtin.module() {
  ^2:
    %34 = arith.constant 52 ⏎
    test.test(%34)
}
-/
#guard_msgs in
#eval! testBench "add-fold-worklist" 10

/--
info:
builtin.module() {
  ^2:
    %34 = arith.constant 52 ⏎
    test.test(%34)
}
-/
#guard_msgs in
#eval! testBench "add-fold-forwards" 10

/--
info:
builtin.module() {
  ^2:
    %3 = arith.constant 42 ⏎
    test.test(%3)
}
-/
#guard_msgs in
#eval! testBench "add-zero-worklist" 10

/--
info:
builtin.module() {
  ^2:
    %3 = arith.constant 42 ⏎
    test.test(%3)
}
-/
#guard_msgs in
#eval! testBench "add-zero-forwards" 10

/--
info:
builtin.module() {
  ^2:
    %3 = arith.constant 42 ⏎
    %34 = arith.addi(%3, %3)
    %33 = arith.addi(%34, %34)
    %32 = arith.addi(%33, %33)
    %31 = arith.addi(%32, %32)
    %30 = arith.addi(%31, %31)
    %29 = arith.addi(%30, %30)
    %28 = arith.addi(%29, %29)
    %27 = arith.addi(%28, %28)
    %26 = arith.addi(%27, %27)
    %25 = arith.addi(%26, %26)
    test.test(%25)
}
-/
#guard_msgs in
#eval! testBench "mul-two-worklist" 10

/--
info:
builtin.module() {
  ^2:
    %3 = arith.constant 42 ⏎
    %25 = arith.addi(%3, %3)
    %26 = arith.addi(%25, %25)
    %27 = arith.addi(%26, %26)
    %28 = arith.addi(%27, %27)
    %29 = arith.addi(%28, %28)
    %30 = arith.addi(%29, %29)
    %31 = arith.addi(%30, %30)
    %32 = arith.addi(%31, %31)
    %33 = arith.addi(%32, %32)
    %34 = arith.addi(%33, %33)
    test.test(%34)
}
-/
#guard_msgs in
#eval! testBench "mul-two-forwards" 10

/--
info:
builtin.module() {
  ^2:
    %3 = arith.constant 42 ⏎
    %4 = arith.constant 0 ⏎
    %5 = arith.addi(%3, %4)
    %6 = arith.addi(%5, %4)
    %7 = arith.addi(%6, %4)
    %8 = arith.addi(%7, %4)
    %9 = arith.addi(%8, %4)
    test.test(%9)
}
-/
#guard_msgs in
#eval! Program.addZeroReuseTree 5 100 |> print

/--
info:
builtin.module() {
  ^2:
    %3 = arith.constant 42 ⏎
    test.test(%3)
}
-/
#guard_msgs in
#eval! testBench "add-zero-reuse-worklist" 10

/--
info:
builtin.module() {
  ^2:
    %3 = arith.constant 42 ⏎
    test.test(%3)
}
-/
#guard_msgs in
#eval! testBench "add-zero-reuse-forwards" 10

/--
info:
builtin.module() {
  ^2:
    %3 = arith.constant 42 ⏎
    %4 = arith.constant 0 ⏎
    %6 = arith.addi(%3, %4)
    %7 = arith.addi(%6, %4)
    %8 = arith.addi(%7, %4)
    %9 = arith.addi(%8, %4)
    test.test(%9)
}
-/
#guard_msgs in
#eval! testBench "add-zero-reuse-first" 5

/--
info:
builtin.module() {
  ^2:
    %3 = arith.constant 42 ⏎
    %4 = arith.constant 0 ⏎
    %5 = arith.addi(%3, %4)
    %6 = arith.addi(%5, %5)
    %7 = arith.addi(%6, %5)
    %8 = arith.addi(%7, %5)
    %9 = arith.addi(%8, %5)
    %10 = arith.addi(%9, %5)
    test.test(%10)
}
-/
#guard_msgs in
#eval! Program.addZeroLotsOfReuseTree 5 100 |> print

/--
info:
builtin.module() {
  ^2:
    %3 = arith.constant 42 ⏎
    %6 = arith.addi(%3, %3)
    %7 = arith.addi(%6, %3)
    %8 = arith.addi(%7, %3)
    %9 = arith.addi(%8, %3)
    %10 = arith.addi(%9, %3)
    test.test(%10)
}
-/
#guard_msgs in
#eval! testBench "add-zero-lots-of-reuse-first" 5

end Mlir.Benchmarks
