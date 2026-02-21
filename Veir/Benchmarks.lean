import Veir.Prelude
import Veir.IR.Basic
import Veir.Rewriter.Basic
import Veir.Printer
import Veir.PatternRewriter.Basic
import Veir.Rewriter.Basic

open Veir.Attribute

set_option warn.sorry false

namespace Veir.Benchmarks

namespace Pattern

def addIConstantFolding (rewriter: PatternRewriter) (op: OperationPtr) : Option PatternRewriter := do
  -- Check that the operation is an arith.addi operation
  if op.getOpType rewriter.ctx sorry ≠ .arith .addi then
    return rewriter

  -- Get the lhs and check that it is a constant
  let lhsValuePtr := op.getOperand rewriter.ctx 0 (by sorry) (by sorry)
  let lhsOp ← match lhsValuePtr with
  | ValuePtr.opResult lhsOpResultPtr => some lhsOpResultPtr.op
  | _ => none
  let lhsOpStruct := lhsOp.get rewriter.ctx (by sorry)
  if lhsOpStruct.opType ≠ .arith .constant then
    return rewriter

  -- Get the rhs and check that it is a constant
  let rhsValuePtr := op.getOperand rewriter.ctx 1 (by sorry) (by sorry)
  let rhsOp ← match rhsValuePtr with
  | ValuePtr.opResult rhsOpResultPtr => some rhsOpResultPtr.op
  | _ => none
  let rhsOpStruct := rhsOp.get rewriter.ctx (by sorry)
  if rhsOpStruct.opType ≠ .arith .constant then
    return rewriter

  -- Sum both constant values
  let lhsVal := (lhsOp.getProperties! rewriter.ctx (.arith .constant)).value.value
  let rhsVal := (rhsOp.getProperties! rewriter.ctx (.arith .constant)).value.value
  let newVal := ArithConstantProperties.mk (IntegerAttr.mk (lhsVal + rhsVal) (IntegerType.mk 32))
  let (rewriter, newOp) ← rewriter.createOp (.arith .constant) #[IntegerType.mk 32] #[] #[] #[] newVal (some $ .before op) sorry sorry sorry sorry
  let mut rewriter ← rewriter.replaceOp op newOp sorry sorry sorry

  if (lhsValuePtr.getFirstUse rewriter.ctx (by sorry)).isNone then
    rewriter ← rewriter.eraseOp lhsOp sorry
  if (rhsValuePtr.getFirstUse rewriter.ctx (by sorry)).isNone then
    rewriter ← rewriter.eraseOp rhsOp sorry
  return rewriter

def addIConstantFoldingLocal (ctx: IRContext) (op: OperationPtr) :
    Option (IRContext × Option (Array OperationPtr × Array ValuePtr)) := do
  -- Check that the operation is an `arith.addi` operation
  let .arith .addi := op.getOpType ctx sorry
    | some (ctx, none)
  -- Get the lhs and check that it is a constant
  let lhsValuePtr := op.getOperand ctx 0 (by sorry) (by sorry)
  let .opResult lhsOpResultPtr := lhsValuePtr
    | some (ctx, none)
  let lhsOp := lhsOpResultPtr.op
  let lhsOpStruct := lhsOp.get ctx (by sorry)
  let .arith .constant := lhsOpStruct.opType
    | some (ctx, none)

  -- Get the rhs and check that it is a constant
  let rhsValuePtr := op.getOperand ctx 1 (by sorry) (by sorry)
  let .opResult rhsOpResultPtr := rhsValuePtr
    | some (ctx, none)
  let rhsOp := rhsOpResultPtr.op
  let rhsOpStruct := rhsOp.get ctx (by sorry)
  let .arith .constant := rhsOpStruct.opType
    | some (ctx, none)

  -- Sum both constant values
  let lhsVal := (lhsOp.getProperties! ctx (.arith .constant)).value.value
  let rhsVal := (rhsOp.getProperties! ctx (.arith .constant)).value.value
  let newVal := ArithConstantProperties.mk (IntegerAttr.mk (lhsVal + rhsVal) (IntegerType.mk 32))
  let (ctx, newOp) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] #[] #[] #[] newVal none sorry sorry sorry sorry sorry
  return (ctx, some (#[newOp], #[newOp.getResult 0]))

def addIZeroFolding (rewriter: PatternRewriter) (op: OperationPtr) : Option PatternRewriter := do
  if op.getOpType rewriter.ctx sorry ≠ .arith .addi then
    return rewriter

  -- Get the rhs and check that it is the constant 0
  let rhsValuePtr := op.getOperand rewriter.ctx 1 (by sorry) (by sorry)
  let rhsOp ← match rhsValuePtr with
  | ValuePtr.opResult rhsOpResultPtr => some rhsOpResultPtr.op
  | _ => none
  let rhsOpStruct := rhsOp.get rewriter.ctx (by sorry)
  if rhsOpStruct.opType ≠ .arith .constant then
    return rewriter
  if (rhsOp.getProperties! rewriter.ctx (.arith .constant)).value.value ≠ 0 then
    return rewriter

  -- Get the lhs value
  let lhsValuePtr := op.getOperand rewriter.ctx 0 (by sorry) (by sorry)

  let opValuePtr := op.getResult 0
  let mut rewriter ← rewriter.replaceValue opValuePtr lhsValuePtr sorry sorry
  rewriter ← rewriter.eraseOp op sorry

  if (rhsValuePtr.getFirstUse rewriter.ctx (by sorry)).isNone then
    rewriter ← rewriter.eraseOp rhsOp sorry
  return rewriter

def mulITwoReduce (rewriter: PatternRewriter) (op: OperationPtr) : Option PatternRewriter := do
  if op.getOpType rewriter.ctx sorry ≠ .arith .muli then
    return rewriter

  -- Get the rhs and check that it is the constant 2
  let rhsValuePtr := op.getOperand rewriter.ctx 1 (by sorry) (by sorry)
  let rhsOp ← match rhsValuePtr with
  | ValuePtr.opResult rhsOpResultPtr => some rhsOpResultPtr.op
  | _ => none
  let rhsOpStruct := rhsOp.get rewriter.ctx (by sorry)
  if rhsOpStruct.opType ≠ .arith .constant then
    return rewriter
  if (rhsOp.getProperties! rewriter.ctx (.arith .constant)).value.value ≠ 2 then
    return rewriter

  -- Get the lhs value
  let lhsValuePtr := op.getOperand rewriter.ctx 0 (by sorry) (by sorry)

  let (rewriter, newOp) ← rewriter.createOp (.arith .addi) #[IntegerType.mk 32] #[lhsValuePtr, lhsValuePtr] #[] #[] () (some $ .before op) sorry sorry sorry sorry
  let mut rewriter ← rewriter.replaceOp op newOp sorry sorry sorry

  if (rhsValuePtr.getFirstUse rewriter.ctx (by sorry)).isNone then
    rewriter ← rewriter.eraseOp rhsOp sorry
  return rewriter

end Pattern

-- Rewrites as above but without using the PatternRewriter interface, instead
-- applying the rewrites in custom locations
namespace Custom

abbrev Pattern := IRContext → OperationPtr → Option IRContext

def addIConstantFolding (ctx: IRContext) (op: OperationPtr) : Option IRContext := do
  -- Check that the operation is an arith.addi operation
  if op.getOpType ctx sorry ≠ .arith .addi then
    return ctx

  -- Get the lhs and check that it is a constant
  let lhsValuePtr := op.getOperand ctx 0 (by sorry) (by sorry)
  let lhsOp ← match lhsValuePtr with
  | ValuePtr.opResult lhsOpResultPtr => some lhsOpResultPtr.op
  | _ => none
  let lhsOpStruct := lhsOp.get ctx (by sorry)
  if lhsOpStruct.opType ≠ .arith .constant then
    return ctx

  -- Get the rhs and check that it is a constant
  let rhsValuePtr := op.getOperand ctx 1 (by sorry) (by sorry)
  let rhsOp ← match rhsValuePtr with
  | ValuePtr.opResult rhsOpResultPtr => some rhsOpResultPtr.op
  | _ => none
  let rhsOpStruct := rhsOp.get ctx (by sorry)
  if rhsOpStruct.opType ≠ .arith .constant then
    return ctx

  -- Sum both constant values
  let lhsVal := (lhsOp.getProperties! ctx (.arith .constant)).value.value
  let rhsVal := (rhsOp.getProperties! ctx (.arith .constant)).value.value
  let newVal := ArithConstantProperties.mk (IntegerAttr.mk (lhsVal + rhsVal) (IntegerType.mk 32))
  let (ctx, newOp) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] #[] #[] #[] newVal (some $ .before op) sorry sorry sorry sorry sorry
  let mut ctx ← Rewriter.replaceOp? ctx op newOp sorry sorry sorry sorry

  if (lhsValuePtr.getFirstUse ctx (by sorry)).isNone then
    ctx ← Rewriter.eraseOp ctx lhsOp sorry sorry
  if (rhsValuePtr.getFirstUse ctx (by sorry)).isNone then
    ctx ← Rewriter.eraseOp ctx rhsOp sorry sorry
  return ctx

def addIZeroFolding (ctx: IRContext) (op: OperationPtr) : Option IRContext := do
  if op.getOpType ctx sorry ≠ .arith .addi then
    return ctx

  -- Get the rhs and check that it is the constant 0
  let rhsValuePtr := op.getOperand ctx 1 (by sorry) (by sorry)
  let rhsOp ← match rhsValuePtr with
  | ValuePtr.opResult rhsOpResultPtr => some rhsOpResultPtr.op
  | _ => none
  let rhsOpStruct := rhsOp.get ctx (by sorry)
  if rhsOpStruct.opType ≠ .arith .constant then
    return ctx
  if (rhsOp.getProperties! ctx (.arith .constant)).value.value ≠ 0 then
    return ctx

  -- Get the lhs value
  let lhsValuePtr := op.getOperand ctx 0 (by sorry) (by sorry)

  let oldVal := op.getResult 0
  let mut ctx ← Rewriter.replaceValue? ctx oldVal lhsValuePtr sorry sorry sorry
  ctx ← Rewriter.eraseOp ctx op sorry sorry

  if (rhsValuePtr.getFirstUse ctx (by sorry)).isNone then
    ctx ← Rewriter.eraseOp ctx rhsOp sorry sorry
  return ctx

def mulITwoReduce (ctx: IRContext) (op: OperationPtr) : Option IRContext := do
  if op.getOpType ctx sorry ≠ .arith .muli then
    return ctx

  -- Get the rhs and check that it is the constant 2
  let rhsValuePtr := op.getOperand ctx 1 (by sorry) (by sorry)
  let rhsOp ← match rhsValuePtr with
  | ValuePtr.opResult rhsOpResultPtr => some rhsOpResultPtr.op
  | _ => none
  let rhsOpStruct := rhsOp.get ctx (by sorry)
  if rhsOpStruct.opType ≠ .arith .constant then
    return ctx
  if (rhsOp.getProperties! ctx (.arith .constant)).value.value ≠ 2 then
    return ctx

  -- Get the lhs value
  let lhsValuePtr := op.getOperand ctx 0 (by sorry) (by sorry)

  let (ctx, newOp) ← Rewriter.createOp ctx (.arith .addi) #[IntegerType.mk 32] #[lhsValuePtr, lhsValuePtr] #[] #[] () (some $ .before op) sorry sorry sorry sorry sorry
  let mut ctx ← Rewriter.replaceOp? ctx op newOp sorry sorry sorry sorry

  if (rhsValuePtr.getFirstUse ctx (by sorry)).isNone then
    ctx ← Rewriter.eraseOp ctx rhsOp sorry sorry
  return ctx

-- Rewrites the first instance of an opcode in the program with the given pattern,
-- within a program consisting of one region/block
def rewriteFirst (ctx: IRContext) (topOp : OperationPtr) (opcode: OpCode) (rewrite: Pattern) : Option IRContext := do
  let region := topOp.getRegion! ctx 0
  let block := (region.get ctx (by sorry)).firstBlock.get!
  let mut op ← (block.get! ctx).firstOp

  while op.getOpType ctx sorry ≠ opcode do
    op ← (op.get! ctx).next

  rewrite ctx op

def rewriteFirstAddI (ctx: IRContext) (topOp : OperationPtr) (rewrite: Pattern) : Option IRContext :=
  rewriteFirst ctx topOp (.arith .addi) rewrite

def rewriteForwards (ctx: IRContext) (topOp : OperationPtr) (rewrite: Pattern) : Option IRContext := do
  let region := topOp.getRegion! ctx 0
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

def empty : Option (IRContext × OperationPtr × InsertPoint) := do
  let (ctx, topLevelOp) ← IRContext.create
  let region := topLevelOp.getRegion! ctx 0
  let block := (region.get ctx (by sorry)).firstBlock.get!
  let insertPoint := InsertPoint.atEnd block
  (ctx, topLevelOp, insertPoint)


-- Create a program that looks like:
-- func @main() -> u64 {
--   %0 = arith.constant [root] : u64
--   %1 = arith.constant [inc] : u64
--   %2 = [opcode] %0, %1 : u64
--   %3 = arith.constant [inc] : u64
--   %4 = [opcode] %2, %3 : u64
--   ...
def constFoldTree (opcode: OpCode) (prop : propertiesOf opcode) (size pc: Nat) (root inc: Int) : Option (IRContext × OperationPtr) := do
  let root := ArithConstantProperties.mk (IntegerAttr.mk root (IntegerType.mk 32))
  let inc := ArithConstantProperties.mk (IntegerAttr.mk inc (IntegerType.mk 32))
  let (gctx, topOp, insertPoint) ← empty
  let mut (gctx, gacc) ← Rewriter.createOp gctx (.arith .constant) #[IntegerType.mk 32] #[] #[] #[] root insertPoint sorry sorry sorry sorry sorry
  for i in [0:size] do
    let ⟨thisOp, prop⟩ : (op : OpCode) × propertiesOf op := if (i % 100 < pc) then ⟨opcode, prop⟩ else ⟨.arith .andi, ()⟩
    let (ctx, acc) := (gctx, gacc)
    let (ctx, rhsOp) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] #[] #[] #[] inc insertPoint sorry sorry sorry sorry sorry
    let lhsVal := acc.getResult 0
    let rhsVal := rhsOp.getResult 0
    let (ctx, acc) ← Rewriter.createOp ctx thisOp #[IntegerType.mk 32] #[lhsVal, rhsVal] #[] #[] prop insertPoint sorry sorry sorry sorry sorry
    (gctx, gacc) := (ctx, acc)

  let accRes := gacc.getResult 0
  let (ctx, op) ← Rewriter.createOp gctx (.test .test) #[] #[accRes] #[] #[] () insertPoint sorry sorry sorry sorry sorry
  (ctx, topOp)

def addZeroTree (size pc: Nat) : Option (IRContext × OperationPtr) :=
  constFoldTree (.arith .addi) () size pc 42 0

def addOneTree (size pc: Nat) : Option (IRContext × OperationPtr) :=
  constFoldTree (.arith .addi) () size pc 42 1

def mulTwoTree (size pc: Nat) : Option (IRContext × OperationPtr) :=
  constFoldTree (.arith .muli) () size pc 42 2


-- Create a program that looks like:
-- func @main() -> u64 {
--   %0 = arith.constant [root] : u64
--   %reuse = arith.constant [inc]: u64
--   %2 = [opcode] %0, %reuse : u64
--   %3 = [opcode] %2, %reuse : u64
--   ...
def constReuseTree (opcode: OpCode) (prop : propertiesOf opcode) (size pc: Nat) (root inc: Int) : Option (IRContext × OperationPtr) := do
  let root := ArithConstantProperties.mk (IntegerAttr.mk root (IntegerType.mk 32))
  let inc := ArithConstantProperties.mk (IntegerAttr.mk inc (IntegerType.mk 32))
  let (ctx, topOp, insertPoint) ← empty
  let (ctx, acc) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] #[] #[] #[] root insertPoint sorry sorry sorry sorry sorry
  let (ctx, reuse) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] #[] #[] #[] inc insertPoint sorry sorry sorry sorry sorry

  let mut (gctx, gacc) := (ctx, acc)
  for i in [0:size] do
    let ⟨thisOp, prop⟩ : (op : OpCode) × propertiesOf op := if (i % 100 < pc) then ⟨opcode, prop⟩ else ⟨.arith .andi, ()⟩

    let (ctx, acc) := (gctx, gacc)
    let lhsVal := acc.getResult 0
    let rhsVal := reuse.getResult 0
    let (ctx, acc) ← Rewriter.createOp ctx thisOp #[IntegerType.mk 32] #[lhsVal, rhsVal] #[] #[] prop insertPoint sorry sorry sorry sorry sorry
    (gctx, gacc) := (ctx, acc)
  let (ctx, acc) := (gctx, gacc)

  let accRes := acc.getResult 0
  let (ctx, op) ← Rewriter.createOp ctx (.test .test) #[] #[accRes] #[] #[] () insertPoint sorry sorry sorry sorry sorry
  (ctx, topOp)

def addZeroReuseTree (size pc: Nat) : Option (IRContext × OperationPtr) :=
  constReuseTree (.arith .addi) () size pc 42 0

-- Create a program that looks like:
-- func @main() -> u64 {
--   %0 = arith.constant [lhs] : u64
--   %1 = arith.constant [rhs] : u64
--   %reuse = [opcode] %0, %1 : u64
--   %3 = [opcode] %reuse, %reuse : u64
--   %4 = [opcode] %3, %reuse : u64
--   %5 = [opcode] %4, %reuse : u64
--   ...
def constLotsOfReuseTree (opcode: OpCode) (prop : propertiesOf opcode) (size pc: Nat) (lhs rhs: Int) : Option (IRContext × OperationPtr) := do
  let lhs := ArithConstantProperties.mk (IntegerAttr.mk lhs (IntegerType.mk 32))
  let rhs := ArithConstantProperties.mk (IntegerAttr.mk rhs (IntegerType.mk 32))
  let (ctx, topOp, insertPoint) ← empty
  let (ctx, lhsOp) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] #[] #[] #[] lhs insertPoint sorry sorry sorry sorry sorry
  let (ctx, rhsOp) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] #[] #[] #[] rhs insertPoint sorry sorry sorry sorry sorry
  let lhsVal := lhsOp.getResult 0
  let rhsVal := rhsOp.getResult 0
  let (ctx, reuse) ← Rewriter.createOp ctx opcode #[IntegerType.mk 32] #[lhsVal, rhsVal] #[] #[] prop insertPoint sorry sorry sorry sorry sorry

  let mut (gctx, gacc) := (ctx, reuse)
  for i in [0:size] do
    let ⟨thisOp, prop⟩ : (op : OpCode) × propertiesOf op := if (i % 100 < pc) then ⟨opcode, prop⟩ else ⟨.arith .andi, ()⟩

    let (ctx, acc) := (gctx, gacc)
    let lhsVal := acc.getResult 0
    let rhsVal := reuse.getResult 0
    let (ctx, acc) ← Rewriter.createOp ctx thisOp #[IntegerType.mk 32] #[lhsVal, rhsVal] #[] #[] prop insertPoint sorry sorry sorry sorry sorry
    (gctx, gacc) := (ctx, acc)
  let (ctx, acc) := (gctx, gacc)

  let accRes := acc.getResult 0
  let (ctx, op) ← Rewriter.createOp ctx (.test .test) #[] #[accRes] #[] #[] () insertPoint sorry sorry sorry sorry sorry
  (ctx, topOp)

def addZeroLotsOfReuseTree (size pc: Nat) : Option (IRContext × OperationPtr) :=
  constLotsOfReuseTree (.arith .addi) () size pc 42 0

end Program

def rewriteWorklist (program: IRContext) (topOp : OperationPtr) (rewriter: RewritePattern) : Option IRContext :=
  RewritePattern.applyInContext rewriter program sorry

def print (program: Option (IRContext × OperationPtr)) : IO Unit := do
  if let some (ctx, topOp) := program then
    Printer.printModule ctx topOp

def time {α : Type} (name: String) (f: Unit → IO α) (quiet: Bool) : IO α := do
  let startTime ← IO.monoNanosNow
  let res ← f ()
  let endTime ← IO.monoNanosNow
  let elapsedTime := endTime - startTime
  if not quiet then
    IO.println s!"{name} time (s): {elapsedTime.toFloat / 1000000000}"
  return res

def run {pattern : Type} (size pc: Nat) (create: Nat → Nat → Option (IRContext × OperationPtr))
    (rewriteDriver: IRContext → OperationPtr → pattern → Option IRContext)
    (rewritePattern: pattern)
    (doPrint: Bool) (quiet: Bool := false) : OptionT IO (IRContext × OperationPtr) := do
  let (ctx, topOp) ← time "create" (fun () => return create size pc) quiet
  let ctx ← time "rewrite" (fun () => return rewriteDriver ctx topOp rewritePattern) quiet
  if doPrint && !quiet then
    print (ctx, topOp)
  return (ctx, topOp)

def runBenchmarkWithResult (benchmark: String) (n pc: Nat) (quiet: Bool := false) : OptionT IO (IRContext × OperationPtr) :=
  open Program in
  open Custom in

  let print := pc = 100

  match benchmark with
  | "add-fold-worklist" =>            run n pc addOneTree              rewriteWorklist  Pattern.addIConstantFolding print quiet
  | "add-fold-worklist-local" =>      run n pc addOneTree              rewriteWorklist  (RewritePattern.fromLocalRewrite Pattern.addIConstantFoldingLocal) print quiet
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
info: "builtin.module"() ({
  ^2():
    %34 = "arith.constant"() <{"value" = 52 : i32}> : () -> i32
    "test.test"(%34) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! testBench "add-fold-worklist" 10

/--
info: "builtin.module"() ({
  ^2():
    %3 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    %4 = "arith.constant"() <{"value" = 1 : i32}> : () -> i32
    %9 = "arith.constant"() <{"value" = 43 : i32}> : () -> i32
    %6 = "arith.constant"() <{"value" = 1 : i32}> : () -> i32
    %10 = "arith.constant"() <{"value" = 44 : i32}> : () -> i32
    "test.test"(%10) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! testBench "add-fold-worklist-local" 2

/--
info: "builtin.module"() ({
  ^2():
    %34 = "arith.constant"() <{"value" = 52 : i32}> : () -> i32
    "test.test"(%34) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! testBench "add-fold-forwards" 10

/--
info: "builtin.module"() ({
  ^2():
    %3 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    "test.test"(%3) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! testBench "add-zero-worklist" 10

/--
info: "builtin.module"() ({
  ^2():
    %3 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    "test.test"(%3) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! testBench "add-zero-forwards" 10

/--
info: "builtin.module"() ({
  ^2():
    %3 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    %34 = "arith.addi"(%3, %3) : (i32, i32) -> i32
    %33 = "arith.addi"(%34, %34) : (i32, i32) -> i32
    %32 = "arith.addi"(%33, %33) : (i32, i32) -> i32
    %31 = "arith.addi"(%32, %32) : (i32, i32) -> i32
    %30 = "arith.addi"(%31, %31) : (i32, i32) -> i32
    %29 = "arith.addi"(%30, %30) : (i32, i32) -> i32
    %28 = "arith.addi"(%29, %29) : (i32, i32) -> i32
    %27 = "arith.addi"(%28, %28) : (i32, i32) -> i32
    %26 = "arith.addi"(%27, %27) : (i32, i32) -> i32
    %25 = "arith.addi"(%26, %26) : (i32, i32) -> i32
    "test.test"(%25) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! testBench "mul-two-worklist" 10

/--
info: "builtin.module"() ({
  ^2():
    %3 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    %25 = "arith.addi"(%3, %3) : (i32, i32) -> i32
    %26 = "arith.addi"(%25, %25) : (i32, i32) -> i32
    %27 = "arith.addi"(%26, %26) : (i32, i32) -> i32
    %28 = "arith.addi"(%27, %27) : (i32, i32) -> i32
    %29 = "arith.addi"(%28, %28) : (i32, i32) -> i32
    %30 = "arith.addi"(%29, %29) : (i32, i32) -> i32
    %31 = "arith.addi"(%30, %30) : (i32, i32) -> i32
    %32 = "arith.addi"(%31, %31) : (i32, i32) -> i32
    %33 = "arith.addi"(%32, %32) : (i32, i32) -> i32
    %34 = "arith.addi"(%33, %33) : (i32, i32) -> i32
    "test.test"(%34) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! testBench "mul-two-forwards" 10

/--
info: "builtin.module"() ({
  ^2():
    %3 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    %4 = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
    %5 = "arith.addi"(%3, %4) : (i32, i32) -> i32
    %6 = "arith.addi"(%5, %4) : (i32, i32) -> i32
    %7 = "arith.addi"(%6, %4) : (i32, i32) -> i32
    %8 = "arith.addi"(%7, %4) : (i32, i32) -> i32
    %9 = "arith.addi"(%8, %4) : (i32, i32) -> i32
    "test.test"(%9) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! Program.addZeroReuseTree 5 100 |> print

/--
info: "builtin.module"() ({
  ^2():
    %3 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    "test.test"(%3) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! testBench "add-zero-reuse-worklist" 10

/--
info: "builtin.module"() ({
  ^2():
    %3 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    "test.test"(%3) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! testBench "add-zero-reuse-forwards" 10

/--
info: "builtin.module"() ({
  ^2():
    %3 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    %4 = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
    %6 = "arith.addi"(%3, %4) : (i32, i32) -> i32
    %7 = "arith.addi"(%6, %4) : (i32, i32) -> i32
    %8 = "arith.addi"(%7, %4) : (i32, i32) -> i32
    %9 = "arith.addi"(%8, %4) : (i32, i32) -> i32
    "test.test"(%9) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! testBench "add-zero-reuse-first" 5

/--
info: "builtin.module"() ({
  ^2():
    %3 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    %4 = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
    %5 = "arith.addi"(%3, %4) : (i32, i32) -> i32
    %6 = "arith.addi"(%5, %5) : (i32, i32) -> i32
    %7 = "arith.addi"(%6, %5) : (i32, i32) -> i32
    %8 = "arith.addi"(%7, %5) : (i32, i32) -> i32
    %9 = "arith.addi"(%8, %5) : (i32, i32) -> i32
    %10 = "arith.addi"(%9, %5) : (i32, i32) -> i32
    "test.test"(%10) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! Program.addZeroLotsOfReuseTree 5 100 |> print

/--
info: "builtin.module"() ({
  ^2():
    %3 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    %6 = "arith.addi"(%3, %3) : (i32, i32) -> i32
    %7 = "arith.addi"(%6, %3) : (i32, i32) -> i32
    %8 = "arith.addi"(%7, %3) : (i32, i32) -> i32
    %9 = "arith.addi"(%8, %3) : (i32, i32) -> i32
    %10 = "arith.addi"(%9, %3) : (i32, i32) -> i32
    "test.test"(%10) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! testBench "add-zero-lots-of-reuse-first" 5

end Veir.Benchmarks
