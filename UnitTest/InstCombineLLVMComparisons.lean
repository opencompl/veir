import Veir.Input
import Veir.Verifier
import Veir.PatternRewriter.Puddle.Execution
import Veir.Passes.InstCombineLLVM.AndUltToNe
import Veir.Passes.InstCombineLLVM.AndUgeToEq
import Veir.Passes.InstCombineLLVM.OrUleToEq
import Veir.Passes.InstCombineLLVM.OrUgtToNe
import Veir.Passes.InstCombineLLVM.XorCompareCancellation
import Veir.Passes.InstCombineLLVM.XorCompareCancellationRight
import Veir.Passes.InstCombineLLVM.XorCompareCancellationCross
import Veir.Passes.InstCombineLLVM.XorCompareCancellationSecond
import Veir.Passes.InstCombineLLVM.AddCompareSelf
import Veir.Passes.InstCombineLLVM.SelfCompareAdd
import Veir.Passes.InstCombineLLVM.AddCompareAdd
import Veir.Passes.InstCombineLLVM.SubCompareSelf
import Veir.Passes.InstCombineLLVM.SubCompareSub
import Veir.Passes.InstCombineLLVM.XorCompareSelf
import Veir.Passes.InstCombineLLVM.XorMoveConstant

open Veir Veir.Input Veir.Puddle Veir.Data

private def comparisonSource (binop : String) (predicate : Nat) : String :=
  "\"builtin.module\"() ({\n" ++
  "  %x = \"llvm.mlir.constant\"() <{value = 42 : i32}> : () -> i32\n" ++
  "  %y = \"llvm.mlir.constant\"() <{value = 15 : i32}> : () -> i32\n" ++
  "  %combined = \"llvm." ++ binop ++ "\"(%x, %y) : (i32, i32) -> i32\n" ++
  "  %root = \"llvm.icmp\"(%combined, %x) <{predicate = " ++ toString predicate ++
    " : i64}> : (i32, i32) -> i1\n" ++
  "  \"test.test\"(%root) : (i1) -> ()\n}) : () -> ()"

private def comparisonSourceSwapped (binop : String) (predicate : Nat) : String :=
  (comparisonSource binop predicate).replace
    "\"llvm.icmp\"(%combined, %x)" "\"llvm.icmp\"(%x, %combined)"

private def comparisonSourceDisjoint (predicate : Nat) (swapped : Bool := false) : String :=
  let source := if swapped then comparisonSourceSwapped "or" predicate else comparisonSource "or" predicate
  source.replace
    "\"llvm.or\"(%x, %y) : (i32, i32) -> i32"
    "\"llvm.or\"(%x, %y) <{isDisjoint}> : (i32, i32) -> i32"

private def xorCancellationSource (right0 right1 : String) (predicate : Nat := 0) : String :=
  "\"builtin.module\"() ({\n" ++
  "  %a = \"llvm.mlir.constant\"() <{value = 42 : i32}> : () -> i32\n" ++
  "  %b = \"llvm.mlir.constant\"() <{value = 15 : i32}> : () -> i32\n" ++
  "  %c = \"llvm.mlir.constant\"() <{value = 7 : i32}> : () -> i32\n" ++
  "  %l = \"llvm.xor\"(%a, %b) : (i32, i32) -> i32\n" ++
  "  %r = \"llvm.xor\"(%" ++ right0 ++ ", %" ++ right1 ++ ") : (i32, i32) -> i32\n" ++
  "  %root = \"llvm.icmp\"(%l, %r) <{predicate = " ++ toString predicate ++
    " : i64}> : (i32, i32) -> i1\n" ++
  "  \"test.test\"(%root) : (i1) -> ()\n}) : () -> ()"

private def oneBinCompareSource (opcode x0 x1 cmp0 cmp1 : String) (predicate : Nat)
    (flags : String := "") : String :=
  "\"builtin.module\"() ({\n" ++
  "  %a = \"llvm.mlir.constant\"() <{value = 42 : i32}> : () -> i32\n" ++
  "  %b = \"llvm.mlir.constant\"() <{value = 15 : i32}> : () -> i32\n" ++
  "  %x = \"llvm." ++ opcode ++ "\"(%" ++ x0 ++ ", %" ++ x1 ++ ")" ++ flags ++
    " : (i32, i32) -> i32\n" ++
  "  %root = \"llvm.icmp\"(%" ++ cmp0 ++ ", %" ++ cmp1 ++ ") <{predicate = " ++
    toString predicate ++ " : i64}> : (i32, i32) -> i1\n" ++
  "  \"test.test\"(%root) : (i1) -> ()\n}) : () -> ()"

private def twoBinCompareSource (opcode l0 l1 r0 r1 : String) (predicate : Nat)
    (flags : String := "") : String :=
  "\"builtin.module\"() ({\n" ++
  "  %a = \"llvm.mlir.constant\"() <{value = 42 : i32}> : () -> i32\n" ++
  "  %b = \"llvm.mlir.constant\"() <{value = 15 : i32}> : () -> i32\n" ++
  "  %c = \"llvm.mlir.constant\"() <{value = 7 : i32}> : () -> i32\n" ++
  "  %l = \"llvm." ++ opcode ++ "\"(%" ++ l0 ++ ", %" ++ l1 ++ ")" ++ flags ++
    " : (i32, i32) -> i32\n" ++
  "  %r = \"llvm." ++ opcode ++ "\"(%" ++ r0 ++ ", %" ++ r1 ++ ")" ++ flags ++
    " : (i32, i32) -> i32\n" ++
  "  %root = \"llvm.icmp\"(%l, %r) <{predicate = " ++ toString predicate ++
    " : i64}> : (i32, i32) -> i1\n" ++
  "  \"test.test\"(%root) : (i1) -> ()\n}) : () -> ()"

private def twoLikeCompareSource (leftOpcode rightOpcode l0 l1 r0 r1 : String)
    (predicate : Nat) (leftFlags : String := "") (rightFlags : String := "") : String :=
  "\"builtin.module\"() ({\n" ++
  "  %a = \"llvm.mlir.constant\"() <{value = 42 : i32}> : () -> i32\n" ++
  "  %b = \"llvm.mlir.constant\"() <{value = 15 : i32}> : () -> i32\n" ++
  "  %c = \"llvm.mlir.constant\"() <{value = 7 : i32}> : () -> i32\n" ++
  "  %l = \"llvm." ++ leftOpcode ++ "\"(%" ++ l0 ++ ", %" ++ l1 ++ ")" ++ leftFlags ++
    " : (i32, i32) -> i32\n" ++
  "  %r = \"llvm." ++ rightOpcode ++ "\"(%" ++ r0 ++ ", %" ++ r1 ++ ")" ++ rightFlags ++
    " : (i32, i32) -> i32\n" ++
  "  %root = \"llvm.icmp\"(%l, %r) <{predicate = " ++ toString predicate ++
    " : i64}> : (i32, i32) -> i1\n" ++
  "  \"test.test\"(%root) : (i1) -> ()\n}) : () -> ()"

private def xorMoveConstantSource (predicate : Nat) (swapped : Bool := false)
    (constantB : Bool := false) : String :=
  "\"builtin.module\"() ({\n" ++
  "  %a = \"llvm.mlir.constant\"() <{value = 42 : i32}> : () -> i32\n" ++
  "  %k = \"llvm.mlir.constant\"() <{value = 7 : i32}> : () -> i32\n" ++
  (if constantB then
    "  %b = \"llvm.mlir.constant\"() <{value = 15 : i32}> : () -> i32\n"
   else
    "  %b = \"llvm.add\"(%a, %k) : (i32, i32) -> i32\n") ++
  "  %x = \"llvm.xor\"(%a, %k) : (i32, i32) -> i32\n" ++
  "  %root = \"llvm.icmp\"(" ++ (if swapped then "%b, %x" else "%x, %b") ++
    ") <{predicate = " ++ toString predicate ++
    " : i64}> : (i32, i32) -> i1\n" ++
  "  \"test.test\"(%root) : (i1) -> ()\n}) : () -> ()"

private def hasIcmpPredicate (ctx : IRContext OpCode) (predicate : LLVM.IntPred) : Bool := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = (OpCode.llvm .icmp) then
        let props : IcmpProperties := op.getProperties! ctx (OpCode.llvm .icmp)
        if props.predicate = predicate then return true
  return false

private def findIcmp (ctx : IRContext OpCode) : Option OperationPtr := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = (OpCode.llvm .icmp) then return some op
  return none

private def hasNswNuwBinop (ctx : IRContext OpCode) : Bool := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = (OpCode.llvm .add) then
        let props : NswNuwProperties := op.getProperties! ctx (OpCode.llvm .add)
        if props.nsw && props.nuw then return true
      else if op.getOpType ctx h = (OpCode.llvm .sub) then
        let props : NswNuwProperties := op.getProperties! ctx (OpCode.llvm .sub)
        if props.nsw && props.nuw then return true
  return false

private def hasRequiredBinopFlags (ctx : IRContext OpCode)
    (expectNsw expectNuw : Bool) : Bool := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = (OpCode.llvm .add) then
        let props : NswNuwProperties := op.getProperties! ctx (OpCode.llvm .add)
        if (!expectNsw || props.nsw) && (!expectNuw || props.nuw) then return true
      else if op.getOpType ctx h = (OpCode.llvm .sub) then
        let props : NswNuwProperties := op.getProperties! ctx (OpCode.llvm .sub)
        if (!expectNsw || props.nsw) && (!expectNuw || props.nuw) then return true
  return false

private def runComparison (source : String) (rule : Pattern OpCode)
    (expected : LLVM.IntPred) (expectNswNuw : Bool := false) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString source.toUTF8
  let some originalRoot := findIcmp ctx.raw
    | throw "comparison fixture has no llvm.icmp root"
  if expectNswNuw && !hasNswNuwBinop ctx.raw then
    throw "comparison fixture did not parse nsw+nuw overflow flags"
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw "comparison rewrite driver failed"
  if originalRoot.InBounds rewritten.raw then
    throw "matched llvm.icmp root was not replaced"
  if !hasIcmpPredicate rewritten.raw expected then
    throw "replacement llvm.icmp predicate was not created"
  rewritten.verify moduleOp

private def runComparisonNoMatch (source : String) (rule : Pattern OpCode) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString source.toUTF8
  let some originalRoot := findIcmp ctx.raw
    | throw "comparison fixture has no llvm.icmp root"
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw "comparison rewrite driver failed"
  if !originalRoot.InBounds rewritten.raw then
    throw "guarded comparison unexpectedly rewrote the llvm.icmp root"
  rewritten.verify moduleOp

private def runComparisonWithFlags (source : String) (rule : Pattern OpCode)
    (expected : LLVM.IntPred) (expectNsw expectNuw : Bool) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString source.toUTF8
  let some originalRoot := findIcmp ctx.raw
    | throw "comparison fixture has no llvm.icmp root"
  if !hasRequiredBinopFlags ctx.raw expectNsw expectNuw then
    throw "comparison fixture did not parse the required overflow flags"
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw "comparison rewrite driver failed"
  if originalRoot.InBounds rewritten.raw then
    throw "matched llvm.icmp root was not replaced"
  if !hasIcmpPredicate rewritten.raw expected then
    throw "replacement llvm.icmp predicate was not created"
  rewritten.verify moduleOp

private def regressionExisting : Except String Unit := do
  runComparison (comparisonSource "and" 6)
    Veir.Passes.InstCombineLLVM.AndUltToNe.andUltToNe .ne
  runComparison (comparisonSource "and" 9)
    Veir.Passes.InstCombineLLVM.AndUgeToEq.andUgeToEq .eq
  runComparison (comparisonSource "or" 7)
    Veir.Passes.InstCombineLLVM.OrUleToEq.orUleToEq .eq
  runComparison (comparisonSource "or" 8)
    Veir.Passes.InstCombineLLVM.OrUgtToNe.orUgtToNe .ne
  runComparison (comparisonSourceSwapped "and" 8)
    Veir.Passes.InstCombineLLVM.AndUltToNe.andUltToNeSwapped .ne
  runComparison (comparisonSourceSwapped "and" 7)
    Veir.Passes.InstCombineLLVM.AndUgeToEq.andUgeToEqSwapped .eq
  runComparison (comparisonSourceSwapped "or" 9)
    Veir.Passes.InstCombineLLVM.OrUleToEq.orUleToEqSwapped .eq
  runComparison (comparisonSourceSwapped "or" 6)
    Veir.Passes.InstCombineLLVM.OrUgtToNe.orUgtToNeSwapped .ne
  runComparison (comparisonSourceDisjoint 7)
    Veir.Passes.InstCombineLLVM.OrUleToEq.orUleToEqDisjoint .eq
  runComparison (comparisonSourceDisjoint 9 true)
    Veir.Passes.InstCombineLLVM.OrUleToEq.orUleToEqSwappedDisjoint .eq
  runComparison (comparisonSourceDisjoint 8)
    Veir.Passes.InstCombineLLVM.OrUgtToNe.orUgtToNeDisjoint .ne
  runComparison (comparisonSourceDisjoint 6 true)
    Veir.Passes.InstCombineLLVM.OrUgtToNe.orUgtToNeSwappedDisjoint .ne
  runComparison (xorCancellationSource "a" "c")
    Veir.Passes.InstCombineLLVM.XorCompareCancellation.xorCompareCancellation .eq
  runComparison (xorCancellationSource "c" "a")
    Veir.Passes.InstCombineLLVM.XorCompareCancellationRight.xorCompareCancellationRight .eq
  runComparison (xorCancellationSource "b" "c")
    Veir.Passes.InstCombineLLVM.XorCompareCancellationCross.xorCompareCancellationCross .eq
  runComparison (xorCancellationSource "c" "b")
    Veir.Passes.InstCombineLLVM.XorCompareCancellationSecond.xorCompareCancellationSecond .eq
  runComparison (xorCancellationSource "a" "c" 1)
    Veir.Passes.InstCombineLLVM.XorCompareCancellation.xorCompareCancellationNe .ne
  runComparison (xorCancellationSource "c" "a" 1)
    Veir.Passes.InstCombineLLVM.XorCompareCancellationRight.xorCompareCancellationRightNe .ne
  runComparison (xorCancellationSource "b" "c" 1)
    Veir.Passes.InstCombineLLVM.XorCompareCancellationCross.xorCompareCancellationCrossNe .ne
  runComparison (xorCancellationSource "c" "b" 1)
    Veir.Passes.InstCombineLLVM.XorCompareCancellationSecond.xorCompareCancellationSecondNe .ne

private def regressionAdd : Except String Unit := do
  let flags := " <{\"overflowFlags\" = 3 : i32}>"
  let nsw := " <{\"overflowFlags\" = 1 : i32}>"
  let nuw := " <{\"overflowFlags\" = 2 : i32}>"
  runComparison (oneBinCompareSource "add" "a" "b" "x" "a" 0 flags)
    Veir.Passes.InstCombineLLVM.AddCompareSelf.addCompareSelfEq .eq true
  runComparison (oneBinCompareSource "add" "b" "a" "x" "a" 0 flags)
    Veir.Passes.InstCombineLLVM.AddCompareSelf.addCompareSelfEqCommuted .eq true
  runComparison (oneBinCompareSource "add" "a" "b" "x" "a" 1 flags)
    Veir.Passes.InstCombineLLVM.AddCompareSelf.addCompareSelfNe .ne true
  runComparison (oneBinCompareSource "add" "b" "a" "x" "a" 1 flags)
    Veir.Passes.InstCombineLLVM.AddCompareSelf.addCompareSelfNeCommuted .ne true
  runComparison (oneBinCompareSource "add" "a" "b" "a" "x" 0 flags)
    Veir.Passes.InstCombineLLVM.SelfCompareAdd.selfCompareAddEq .eq true
  runComparison (oneBinCompareSource "add" "b" "a" "a" "x" 0 flags)
    Veir.Passes.InstCombineLLVM.SelfCompareAdd.selfCompareAddEqCommuted .eq true
  runComparison (oneBinCompareSource "add" "a" "b" "a" "x" 1 flags)
    Veir.Passes.InstCombineLLVM.SelfCompareAdd.selfCompareAddNe .ne true
  runComparison (oneBinCompareSource "add" "b" "a" "a" "x" 1 flags)
    Veir.Passes.InstCombineLLVM.SelfCompareAdd.selfCompareAddNeCommuted .ne true
  runComparison (twoBinCompareSource "add" "a" "b" "a" "c" 0 flags)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addCompareAddEq .eq true
  runComparison (twoBinCompareSource "add" "a" "b" "c" "a" 0 flags)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addCompareAddEqRightCommuted .eq true
  runComparison (twoBinCompareSource "add" "b" "a" "a" "c" 0 flags)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addCompareAddEqLeftCommuted .eq true
  runComparison (twoBinCompareSource "add" "b" "a" "c" "a" 0 flags)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addCompareAddEqBothCommuted .eq true
  runComparison (twoBinCompareSource "add" "a" "b" "a" "c" 1 flags)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addCompareAddNe .ne true
  runComparison (twoBinCompareSource "add" "a" "b" "c" "a" 1 flags)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addCompareAddNeRightCommuted .ne true
  runComparison (twoBinCompareSource "add" "b" "a" "a" "c" 1 flags)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addCompareAddNeLeftCommuted .ne true
  runComparison (twoBinCompareSource "add" "b" "a" "c" "a" 1 flags)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addCompareAddNeBothCommuted .ne true
  runComparisonWithFlags (oneBinCompareSource "add" "a" "b" "x" "a" 6 nuw)
    Veir.Passes.InstCombineLLVM.AddCompareSelf.addCompareSelfUnsigned .ult false true
  runComparisonWithFlags (oneBinCompareSource "add" "b" "a" "x" "a" 8 nuw)
    Veir.Passes.InstCombineLLVM.AddCompareSelf.addCompareSelfUnsignedCommuted .ugt false true
  runComparisonWithFlags (oneBinCompareSource "add" "a" "b" "x" "a" 2 nsw)
    Veir.Passes.InstCombineLLVM.AddCompareSelf.addCompareSelfSigned .slt true false
  runComparisonWithFlags (oneBinCompareSource "add" "b" "a" "x" "a" 4 nsw)
    Veir.Passes.InstCombineLLVM.AddCompareSelf.addCompareSelfSignedCommuted .sgt true false
  runComparisonWithFlags (oneBinCompareSource "add" "a" "b" "a" "x" 7 nuw)
    Veir.Passes.InstCombineLLVM.SelfCompareAdd.selfCompareAddUnsigned .ule false true
  runComparisonWithFlags (oneBinCompareSource "add" "b" "a" "a" "x" 9 nuw)
    Veir.Passes.InstCombineLLVM.SelfCompareAdd.selfCompareAddUnsignedCommuted .uge false true
  runComparisonWithFlags (oneBinCompareSource "add" "a" "b" "a" "x" 3 nsw)
    Veir.Passes.InstCombineLLVM.SelfCompareAdd.selfCompareAddSigned .sle true false
  runComparisonWithFlags (oneBinCompareSource "add" "b" "a" "a" "x" 5 nsw)
    Veir.Passes.InstCombineLLVM.SelfCompareAdd.selfCompareAddSignedCommuted .sge true false
  runComparisonWithFlags (twoBinCompareSource "add" "a" "b" "a" "c" 6 nuw)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addCompareAddUnsigned .ult false true
  runComparisonWithFlags (twoBinCompareSource "add" "a" "b" "c" "a" 7 nuw)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addCompareAddUnsignedRightCommuted .ule false true
  runComparisonWithFlags (twoBinCompareSource "add" "b" "a" "a" "c" 8 nuw)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addCompareAddUnsignedLeftCommuted .ugt false true
  runComparisonWithFlags (twoBinCompareSource "add" "b" "a" "c" "a" 9 nuw)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addCompareAddUnsignedBothCommuted .uge false true
  runComparisonWithFlags (twoBinCompareSource "add" "a" "b" "a" "c" 2 nsw)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addCompareAddSigned .slt true false
  runComparisonWithFlags (twoBinCompareSource "add" "a" "b" "c" "a" 3 nsw)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addCompareAddSignedRightCommuted .sle true false
  runComparisonWithFlags (twoBinCompareSource "add" "b" "a" "a" "c" 4 nsw)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addCompareAddSignedLeftCommuted .sgt true false
  runComparisonWithFlags (twoBinCompareSource "add" "b" "a" "c" "a" 5 nsw)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addCompareAddSignedBothCommuted .sge true false
  runComparisonNoMatch (oneBinCompareSource "add" "a" "b" "x" "a" 2 nuw)
    Veir.Passes.InstCombineLLVM.AddCompareSelf.addCompareSelfSigned
  runComparisonNoMatch (twoBinCompareSource "add" "a" "b" "a" "c" 6 nsw)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addCompareAddUnsigned
  let disjoint := " <{isDisjoint}>"
  runComparison (oneBinCompareSource "or" "a" "b" "x" "a" 2 disjoint)
    Veir.Passes.InstCombineLLVM.AddCompareSelf.orDisjointCompareSelf .slt
  runComparison (oneBinCompareSource "or" "b" "a" "x" "a" 9 disjoint)
    Veir.Passes.InstCombineLLVM.AddCompareSelf.orDisjointCompareSelfCommuted .uge
  runComparison (oneBinCompareSource "or" "a" "b" "a" "x" 4 disjoint)
    Veir.Passes.InstCombineLLVM.SelfCompareAdd.selfCompareOrDisjoint .sgt
  runComparison (oneBinCompareSource "or" "b" "a" "a" "x" 7 disjoint)
    Veir.Passes.InstCombineLLVM.SelfCompareAdd.selfCompareOrDisjointCommuted .ule
  runComparison (twoLikeCompareSource "or" "or" "a" "b" "a" "c" 2 disjoint disjoint)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.orOrCompare .slt
  runComparison (twoLikeCompareSource "or" "or" "a" "b" "c" "a" 6 disjoint disjoint)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.orOrCompareRightCommuted .ult
  runComparison (twoLikeCompareSource "or" "or" "b" "a" "a" "c" 5 disjoint disjoint)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.orOrCompareLeftCommuted .sge
  runComparison (twoLikeCompareSource "or" "or" "b" "a" "c" "a" 9 disjoint disjoint)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.orOrCompareBothCommuted .uge
  runComparisonWithFlags
    (twoLikeCompareSource "or" "add" "a" "b" "a" "c" 2 disjoint nsw)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.orAddCompare .slt true false
  runComparisonWithFlags
    (twoLikeCompareSource "or" "add" "a" "b" "c" "a" 6 disjoint nuw)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.orAddCompareRightCommuted .ult false true
  runComparisonWithFlags
    (twoLikeCompareSource "or" "add" "b" "a" "a" "c" 5 disjoint nsw)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.orAddCompareLeftCommuted .sge true false
  runComparisonWithFlags
    (twoLikeCompareSource "or" "add" "b" "a" "c" "a" 9 disjoint nuw)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.orAddCompareBothCommuted .uge false true
  runComparisonWithFlags
    (twoLikeCompareSource "add" "or" "a" "b" "a" "c" 3 nsw disjoint)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addOrCompare .sle true false
  runComparisonWithFlags
    (twoLikeCompareSource "add" "or" "a" "b" "c" "a" 7 nuw disjoint)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addOrCompareRightCommuted .ule false true
  runComparisonWithFlags
    (twoLikeCompareSource "add" "or" "b" "a" "a" "c" 4 nsw disjoint)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addOrCompareLeftCommuted .sgt true false
  runComparisonWithFlags
    (twoLikeCompareSource "add" "or" "b" "a" "c" "a" 8 nuw disjoint)
    Veir.Passes.InstCombineLLVM.AddCompareAdd.addOrCompareBothCommuted .ugt false true

private def regressionSub : Except String Unit := do
  let flags := " <{\"overflowFlags\" = 3 : i32}>"
  let nsw := " <{\"overflowFlags\" = 1 : i32}>"
  let nuw := " <{\"overflowFlags\" = 2 : i32}>"
  runComparison (oneBinCompareSource "sub" "a" "b" "x" "a" 0 flags)
    Veir.Passes.InstCombineLLVM.SubCompareSelf.subCompareSelfEq .eq true
  runComparison (oneBinCompareSource "sub" "a" "b" "x" "a" 1 flags)
    Veir.Passes.InstCombineLLVM.SubCompareSelf.subCompareSelfNe .ne true
  runComparison (twoBinCompareSource "sub" "a" "b" "c" "b" 0 flags)
    Veir.Passes.InstCombineLLVM.SubCompareSub.subCompareSubEq .eq true
  runComparison (twoBinCompareSource "sub" "a" "b" "c" "b" 1 flags)
    Veir.Passes.InstCombineLLVM.SubCompareSub.subCompareSubNe .ne true
  runComparisonWithFlags (oneBinCompareSource "sub" "a" "b" "x" "a" 2 nsw)
    Veir.Passes.InstCombineLLVM.SubCompareSelf.subCompareSelfRelational .slt true false
  runComparisonWithFlags (oneBinCompareSource "sub" "a" "b" "x" "a" 6 nuw)
    Veir.Passes.InstCombineLLVM.SubCompareSelf.subCompareSelfRelational .ult false true
  runComparisonWithFlags (twoBinCompareSource "sub" "a" "b" "c" "b" 5 nsw)
    Veir.Passes.InstCombineLLVM.SubCompareSub.subCompareSubRelational .sge true false
  runComparisonWithFlags (twoBinCompareSource "sub" "a" "b" "c" "b" 9 nuw)
    Veir.Passes.InstCombineLLVM.SubCompareSub.subCompareSubRelational .uge false true
  runComparisonNoMatch (oneBinCompareSource "sub" "a" "b" "x" "a" 2 nuw)
    Veir.Passes.InstCombineLLVM.SubCompareSelf.subCompareSelfRelational
  runComparisonNoMatch (twoBinCompareSource "sub" "a" "b" "c" "b" 6 nsw)
    Veir.Passes.InstCombineLLVM.SubCompareSub.subCompareSubRelational

private def regressionXor : Except String Unit := do
  runComparison (oneBinCompareSource "xor" "a" "b" "x" "a" 0)
    Veir.Passes.InstCombineLLVM.XorCompareSelf.xorCompareSelfEq .eq
  runComparison (oneBinCompareSource "xor" "a" "b" "a" "x" 0)
    Veir.Passes.InstCombineLLVM.XorCompareSelf.xorCompareSelfEqSwapped .eq
  runComparison (oneBinCompareSource "xor" "b" "a" "x" "a" 0)
    Veir.Passes.InstCombineLLVM.XorCompareSelf.xorCompareSelfEqCommuted .eq
  runComparison (oneBinCompareSource "xor" "b" "a" "a" "x" 0)
    Veir.Passes.InstCombineLLVM.XorCompareSelf.xorCompareSelfEqCommutedSwapped .eq
  runComparison (oneBinCompareSource "xor" "a" "b" "x" "a" 1)
    Veir.Passes.InstCombineLLVM.XorCompareSelf.xorCompareSelfNe .ne
  runComparison (oneBinCompareSource "xor" "a" "b" "a" "x" 1)
    Veir.Passes.InstCombineLLVM.XorCompareSelf.xorCompareSelfNeSwapped .ne
  runComparison (oneBinCompareSource "xor" "b" "a" "x" "a" 1)
    Veir.Passes.InstCombineLLVM.XorCompareSelf.xorCompareSelfNeCommuted .ne
  runComparison (oneBinCompareSource "xor" "b" "a" "a" "x" 1)
    Veir.Passes.InstCombineLLVM.XorCompareSelf.xorCompareSelfNeCommutedSwapped .ne
  runComparison (xorMoveConstantSource 0)
    Veir.Passes.InstCombineLLVM.XorMoveConstant.xorMoveConstantEq .eq
  runComparison (xorMoveConstantSource 1)
    Veir.Passes.InstCombineLLVM.XorMoveConstant.xorMoveConstantNe .ne
  runComparison (xorMoveConstantSource 0 true)
    Veir.Passes.InstCombineLLVM.XorMoveConstant.xorMoveConstantEqSwapped .eq
  runComparison (xorMoveConstantSource 1 true)
    Veir.Passes.InstCombineLLVM.XorMoveConstant.xorMoveConstantNeSwapped .ne
  runComparisonNoMatch (xorMoveConstantSource 0 false true)
    Veir.Passes.InstCombineLLVM.XorMoveConstant.xorMoveConstantEq
  runComparisonNoMatch (xorMoveConstantSource 1 true true)
    Veir.Passes.InstCombineLLVM.XorMoveConstant.xorMoveConstantNeSwapped

#guard regressionExisting = .ok ()
#guard regressionAdd = .ok ()
#guard regressionSub = .ok ()
#guard regressionXor = .ok ()
