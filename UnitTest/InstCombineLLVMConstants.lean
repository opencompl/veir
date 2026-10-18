import Veir.Input
import Veir.Verifier
import Veir.PatternRewriter.Puddle.Execution
import Veir.Passes.InstCombineLLVM.NegateIncrement
import Veir.Passes.InstCombineLLVM.NegateNot
import Veir.Passes.InstCombineLLVM.DoubleNegation
import Veir.Passes.InstCombineLLVM.NegateI1
import Veir.Passes.InstCombineLLVM.SubSwap
import Veir.Passes.InstCombineLLVM.NegateConstant
import Veir.Passes.InstCombineLLVM.NegateBooleanExtension
import Veir.Passes.InstCombineLLVM.NegateRightShift
import Veir.Passes.InstCombineLLVM.NegateTrunc
import Veir.Passes.InstCombineLLVM.AddI1
import Veir.Passes.InstCombineLLVM.SubI1
import Veir.Passes.InstCombineLLVM.AllOnesSub
import Veir.Passes.InstCombineLLVM.AddNegNeg
import Veir.Passes.InstCombineLLVM.AddNegLeft
import Veir.Passes.InstCombineLLVM.AddNegRight
import Veir.Passes.InstCombineLLVM.SubNegRight
import Veir.Passes.InstCombineLLVM.SubCancellation
import Veir.Passes.InstCombineLLVM.I1MinMaxAnd
import Veir.Passes.InstCombineLLVM.I1MinMaxOr
import Veir.Passes.InstCombineLLVM.I1CountZeros
import Veir.Passes.InstCombineLLVM.AddXorAnd
import Veir.Passes.InstCombineLLVM.SubOrAnd
import Veir.Passes.InstCombineLLVM.SubAddOr
import Veir.Passes.InstCombineLLVM.SubAddAnd
import Veir.Passes.InstCombineLLVM.SubOrXor
import Veir.Passes.InstCombineLLVM.SubAndNot
import Veir.Passes.InstCombineLLVM.SubOrSelf
import Veir.Passes.InstCombineLLVM.XorAndOr
import Veir.Passes.InstCombineLLVM.XorAndXor
import Veir.Passes.InstCombineLLVM.XorOrSelf
import Veir.Passes.InstCombineLLVM.XorAndSelf
import Veir.Passes.InstCombineLLVM.XorAndNotNot
import Veir.Passes.InstCombineLLVM.XorNotAndSelf
import Veir.Passes.InstCombineLLVM.XorXorOrShared
import Veir.Passes.InstCombineLLVM.AndOrNotAnd
import Veir.Passes.InstCombineLLVM.OrComplementaryMasks
import Veir.Passes.InstCombineLLVM.XorComplementaryMasks
import Veir.Passes.InstCombineLLVM.XorComplementaryOrs
import Veir.Passes.InstCombineLLVM.OrAndNotOr
import Veir.Passes.InstCombineLLVM.OrXorNotOr
import Veir.Passes.InstCombineLLVM.AndComplementaryOrs
import Veir.Passes.InstCombineLLVM.NotAndNot
import Veir.Passes.InstCombineLLVM.NotOrNot
import Veir.Passes.InstCombineLLVM.XorNotMixed
import Veir.Passes.InstCombineLLVM.MulDoubleNeg
import Veir.Passes.InstCombineLLVM.MulSinkNeg
import Veir.Passes.InstCombineLLVM.MulNegConstant
import Veir.Passes.InstCombineLLVM.MulShiftConstant
import Veir.Passes.InstCombineLLVM.AddSubAllOnes
import Veir.Passes.InstCombineLLVM.AddSubConstants
import Veir.Passes.InstCombineLLVM.AddOrNegatedConstant
import Veir.Passes.InstCombineLLVM.AddOneNot
import Veir.Passes.InstCombineLLVM.SubAddAllOnes
import Veir.Passes.InstCombineLLVM.NotSub
import Veir.Passes.InstCombineLLVM.NotAndXorOr
import Veir.Passes.InstCombineLLVM.NotOrXorAnd
import Veir.Passes.InstCombineLLVM.SubSubConstants
import Veir.Passes.InstCombineLLVM.NotNegOr
import Veir.Passes.InstCombineLLVM.MaskedMergeNot
import Veir.Passes.InstCombineLLVM.NotAddConstant
import Veir.Passes.InstCombineLLVM.NegatePoison
import Veir.Passes.InstCombineLLVM.DropWrapFlagsUnusedHigh
import Veir.Passes.InstCombineLLVM.FreeInvertDoubleNot
import Veir.Passes.InstCombineLLVM.FreeInvertConstant
import Veir.Passes.InstCombineLLVM.FreeInvertAdd
import Veir.Passes.InstCombineLLVM.FreeInvertXor
import Veir.Passes.InstCombineLLVM.FreeInvertSub
import Veir.Passes.InstCombineLLVM.FreeInvertAShr
import Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan

open Veir
open Veir.Input
open Veir.Puddle
open Veir.Data

private def source (width : Nat) (notCase : Bool) (notConstantLeft : Bool := false) : String :=
  let ty := s!"i{width}"
  let inputValue := if width = 1 then "1" else "7"
  let (notLhs, notRhs) := if notConstantLeft then ("%minus_one", "%input") else ("%input", "%minus_one")
  let middle := if notCase then
    "%minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++
      "}> : () -> " ++ ty ++ "\n  %middle = \"llvm.xor\"(" ++ notLhs ++ ", " ++ notRhs ++ ") : (" ++
      ty ++ ", " ++ ty ++ ") -> " ++ ty
  else
    "%one = \"llvm.mlir.constant\"() <{value = 1 : " ++ ty ++
      "}> : () -> " ++ ty ++ "\n  %middle = \"llvm.add\"(%input, %one) : (" ++
      ty ++ ", " ++ ty ++ ") -> " ++ ty
  "\"builtin.module\"() ({\n  %input = \"llvm.mlir.constant\"() <{value = " ++ inputValue ++ " : " ++ ty ++
    "}> : () -> " ++ ty ++ "\n  " ++ middle ++
    "\n  %zero = \"llvm.mlir.constant\"() <{value = 0 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %root = \"llvm.sub\"(%zero, %middle) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def hasOp (ctx : IRContext OpCode) (opCode : OpCode) : Bool := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = opCode then return true
  return false

private def hasNSWOp (ctx : IRContext OpCode) (opCode : Llvm) : Bool := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = (.llvm opCode) then
        match opCode with
        | .add =>
          if (op.getProperties! ctx Llvm.add).nsw then return true
        | .sub =>
          if (op.getProperties! ctx Llvm.sub).nsw then return true
        | .mul =>
          if (op.getProperties! ctx Llvm.mul).nsw then return true
        | _ => pure ()
  return false

private def hasNUWOp (ctx : IRContext OpCode) (opCode : Llvm) : Bool := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = (.llvm opCode) then
        match opCode with
        | .add =>
          if (op.getProperties! ctx Llvm.add).nuw then return true
        | .sub =>
          if (op.getProperties! ctx Llvm.sub).nuw then return true
        | .mul =>
          if (op.getProperties! ctx Llvm.mul).nuw then return true
        | _ => pure ()
  return false

private def testInputProducer? (ctx : IRContext OpCode) : Option OperationPtr := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = (.test .test) then
        match op.getOperand! ctx 0 with
        | .opResult result => return some result.op
        | .blockArgument _ => return none
  return none

private def ensureTestRootReplaced (before after : IRContext OpCode) : Except String Unit := do
  let some oldRoot := testInputProducer? before
    | throw "test.test input has no defining operation before rewrite"
  let some newRoot := testInputProducer? after
    | throw "test.test input has no defining operation after rewrite"
  if newRoot = oldRoot then throw "rewrite left the tested root unchanged"

private def countOp (ctx : IRContext OpCode) (opCode : OpCode) : Nat := Id.run do
  let mut count := 0
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = opCode then count := count + 1
  return count

private def hasIntegerConstant (ctx : IRContext OpCode) (width : Nat) (value : Int) : Bool :=
    Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = (OpCode.llvm .mlir__constant) then
        let props : LLVMConstantProperties := op.getProperties! ctx (OpCode.llvm .mlir__constant)
        if props.value = LLVMConstantValue.integer
              (IntegerAttr.ofInt value (IntegerType.signless width)) &&
            op.getResultTypes ctx h = #[(IntegerType.signless width : TypeAttr)] then
          return true
  return false

private def runCase (width : Nat) (notCase : Bool) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString (source width notCase).toUTF8
  let rule := if notCase then
    Veir.Passes.InstCombineLLVM.NegateNot.negateNot
  else
    Veir.Passes.InstCombineLLVM.NegateIncrement.negateIncrement
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw "rewrite did not fire"
  ensureTestRootReplaced ctx.raw rewritten.raw
  if hasOp rewritten.raw (.llvm .sub) then throw "matched llvm.sub root was not erased"
  let replacement := if notCase then (.llvm .add) else (.llvm .xor)
  if !hasOp rewritten.raw replacement then throw "replacement operation was not created"
  let constant := if notCase then 1 else -1
  if !hasIntegerConstant rewritten.raw width constant then
    throw "replacement constant does not have the matched type and normalized value"
  rewritten.verify moduleOp

private def negateConstantSource (width : Nat) (value : Int) : String :=
  let ty := s!"i{width}"
  "\"builtin.module\"() ({\n  %constant = \"llvm.mlir.constant\"() <{value = " ++
    toString value ++ " : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %zero = \"llvm.mlir.constant\"() <{value = 0 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %root = \"llvm.sub\"(%zero, %constant) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def runNegateConstantCase (width : Nat) (value : Int) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString (negateConstantSource width value).toUTF8
  let some rewritten := RewritePattern.applyInContext
      (Pattern.compile Veir.Passes.InstCombineLLVM.NegateConstant.negateConstant).run ctx
    | throw "negate-constant rewrite did not fire"
  ensureTestRootReplaced ctx.raw rewritten.raw
  if hasOp rewritten.raw (.llvm .sub) then
    throw "matched negate-constant llvm.sub root was not erased"
  if !hasIntegerConstant rewritten.raw width (-value) then
    throw "negated constant does not have the matched type and normalized value"
  rewritten.verify moduleOp

private def runRule (text : String) (rule : Pattern OpCode) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString text.toUTF8
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw "rewrite did not fire"
  ensureTestRootReplaced ctx.raw rewritten.raw
  rewritten.verify moduleOp

private def commutedIncrementSource (width : Nat) : String :=
  (source width false).replace
    s!"\"llvm.add\"(%input, %one) : (i{width}, i{width})"
    s!"\"llvm.add\"(%one, %input) : (i{width}, i{width})"

private def doubleNegationSource (width : Nat) : String :=
  let ty := s!"i{width}"
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 7 : " ++ ty ++
  "}> : () -> " ++ ty ++ "\n  %zero = \"llvm.mlir.constant\"() <{value = 0 : " ++ ty ++
  "}> : () -> " ++ ty ++ "\n  %inner = \"llvm.sub\"(%zero, %x) : (" ++ ty ++ ", " ++ ty ++
  ") -> " ++ ty ++ "\n  %root = \"llvm.sub\"(%zero, %inner) : (" ++ ty ++ ", " ++ ty ++
  ") -> " ++ ty ++ "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def subSwapSource (width : Nat) : String :=
  let ty := s!"i{width}"
  "\"builtin.module\"() ({\n  %a = \"llvm.mlir.constant\"() <{value = 7 : " ++ ty ++
  "}> : () -> " ++ ty ++ "\n  %b = \"llvm.mlir.constant\"() <{value = 3 : " ++ ty ++
  "}> : () -> " ++ ty ++ "\n  %zero = \"llvm.mlir.constant\"() <{value = 0 : " ++ ty ++
  "}> : () -> " ++ ty ++ "\n  %inner = \"llvm.sub\"(%a, %b) : (" ++ ty ++ ", " ++ ty ++
  ") -> " ++ ty ++ "\n  %root = \"llvm.sub\"(%zero, %inner) : (" ++ ty ++ ", " ++ ty ++
  ") -> " ++ ty ++ "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def subSwapNSWSource (width : Nat) : String :=
  (subSwapSource width)
    |>.replace "%inner = \"llvm.sub\"(%a, %b) :"
      "%inner = \"llvm.sub\"(%a, %b) <{\"overflowFlags\" = 1 : i32}> :"
    |>.replace "%root = \"llvm.sub\"(%zero, %inner) :"
      "%root = \"llvm.sub\"(%zero, %inner) <{\"overflowFlags\" = 1 : i32}> :"

private def negateI1Source := r#""builtin.module"() ({
  %x = "llvm.mlir.constant"() <{value = 1 : i1}> : () -> i1
  %zero = "llvm.mlir.constant"() <{value = 0 : i1}> : () -> i1
  %root = "llvm.sub"(%zero, %x) : (i1, i1) -> i1
  "test.test"(%root) : (i1) -> ()
}) : () -> ()"#

private def negateBooleanExtensionSource (width : Nat) (zext : Bool)
    (nneg : Bool := false) : String :=
  let dstTy := s!"i{width}"
  let opcode := if zext then "llvm.zext" else "llvm.sext"
  let flags := if zext && nneg then " <{nonNeg}>" else ""
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 1 : i1}> : () -> i1" ++
    "\n  %extended = \"" ++ opcode ++ "\"(%x)" ++ flags ++ " : (i1) -> " ++ dstTy ++
    "\n  %zero = \"llvm.mlir.constant\"() <{value = 0 : " ++ dstTy ++ "}> : () -> " ++ dstTy ++
    "\n  %root = \"llvm.sub\"(%zero, %extended) : (" ++ dstTy ++ ", " ++ dstTy ++ ") -> " ++ dstTy ++
    "\n  \"test.test\"(%root) : (" ++ dstTy ++ ") -> ()\n}) : () -> ()"

private def negateRightShiftSource (width : Nat) (lshr exact : Bool) : String :=
  let ty := s!"i{width}"
  let opcode := if lshr then "llvm.lshr" else "llvm.ashr"
  let flags := if exact then " <{isExact}>" else ""
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 0 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %amount = \"llvm.mlir.constant\"() <{value = " ++ toString (width - 1) ++
    " : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %shifted = \"" ++ opcode ++ "\"(%x, %amount)" ++ flags ++ " : (" ++ ty ++
    ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %zero = \"llvm.mlir.constant\"() <{value = 0 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %root = \"llvm.sub\"(%zero, %shifted) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def negateTruncSource (wideWidth narrowWidth : Nat) : String :=
  let wideTy := s!"i{wideWidth}"
  let narrowTy := s!"i{narrowWidth}"
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 7 : " ++ wideTy ++
    "}> : () -> " ++ wideTy ++
    "\n  %wide_zero = \"llvm.mlir.constant\"() <{value = 0 : " ++ wideTy ++
    "}> : () -> " ++ wideTy ++
    "\n  %negated = \"llvm.sub\"(%wide_zero, %x) : (" ++ wideTy ++ ", " ++ wideTy ++
    ") -> " ++ wideTy ++
    "\n  %truncated = \"llvm.trunc\"(%negated) : (" ++ wideTy ++ ") -> " ++ narrowTy ++
    "\n  %narrow_zero = \"llvm.mlir.constant\"() <{value = 0 : " ++ narrowTy ++
    "}> : () -> " ++ narrowTy ++
    "\n  %root = \"llvm.sub\"(%narrow_zero, %truncated) : (" ++ narrowTy ++ ", " ++
      narrowTy ++ ") -> " ++ narrowTy ++
    "\n  \"test.test\"(%root) : (" ++ narrowTy ++ ") -> ()\n}) : () -> ()"

private def negateTruncCommuteSource (wideWidth narrowWidth : Nat) : String :=
  let wideTy := s!"i{wideWidth}"
  let narrowTy := s!"i{narrowWidth}"
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 7 : " ++ wideTy ++
    "}> : () -> " ++ wideTy ++
    "\n  %truncated = \"llvm.trunc\"(%x) : (" ++ wideTy ++ ") -> " ++ narrowTy ++
    "\n  %zero = \"llvm.mlir.constant\"() <{value = 0 : " ++ narrowTy ++
    "}> : () -> " ++ narrowTy ++
    "\n  %root = \"llvm.sub\"(%zero, %truncated) : (" ++ narrowTy ++ ", " ++ narrowTy ++
    ") -> " ++ narrowTy ++
    "\n  \"test.test\"(%root) : (" ++ narrowTy ++ ") -> ()\n}) : () -> ()"

private def i1BinopSource (opcode : String) : String :=
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 1 : i1}> : () -> i1" ++
    "\n  %y = \"llvm.mlir.constant\"() <{value = 0 : i1}> : () -> i1" ++
    "\n  %root = \"llvm." ++ opcode ++ "\"(%x, %y) : (i1, i1) -> i1" ++
    "\n  \"test.test\"(%root) : (i1) -> ()\n}) : () -> ()"

private def allOnesSubSource (width : Nat) : String :=
  let ty := s!"i{width}"
  let xValue := if width = 1 then "1" else "7"
  "\"builtin.module\"() ({\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %x = \"llvm.mlir.constant\"() <{value = " ++ xValue ++ " : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %root = \"llvm.sub\"(%minus_one, %x) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def negatedOperandSource (width variant : Nat) (nsw : Bool := false) : String :=
  let ty := s!"i{width}"
  let flags := if nsw then " <{\"overflowFlags\" = 1 : i32}>" else ""
  let (opcode, lhs, rhs) := match variant with
    | 0 => ("add", "%neg_a", "%neg_b")
    | 1 => ("add", "%neg_a", "%b")
    | 2 => ("add", "%a", "%neg_b")
    | _ => ("sub", "%a", "%neg_b")
  "\"builtin.module\"() ({\n  %a = \"llvm.mlir.constant\"() <{value = 7 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %b = \"llvm.mlir.constant\"() <{value = 3 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %zero_a = \"llvm.mlir.constant\"() <{value = 0 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %neg_a = \"llvm.sub\"(%zero_a, %a)" ++ flags ++ " : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %zero_b = \"llvm.mlir.constant\"() <{value = 0 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %neg_b = \"llvm.sub\"(%zero_b, %b)" ++ flags ++ " : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm." ++ opcode ++ "\"(" ++ lhs ++ ", " ++ rhs ++ ")" ++ flags ++ " : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def subNegConstantSource (width : Nat) (constant : Int)
    (nsw : Bool := false) : String :=
  let ty := s!"i{width}"
  let flags := if nsw then " <{\"overflowFlags\" = 1 : i32}>" else ""
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 42 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %constant = \"llvm.mlir.constant\"() <{value = " ++ toString constant ++ " : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %root = \"llvm.sub\"(%x, %constant)" ++ flags ++ " : (" ++ ty ++ ", " ++ ty ++
    ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def subCancellationSource (width variant : Nat) : String :=
  let ty := s!"i{width}"
  let (innerOpcode, innerLhs, innerRhs, rootLhs, rootRhs) := match variant with
    | 0 => ("add", "%x", "%y", "%x", "%inner")
    | 1 => ("add", "%y", "%x", "%x", "%inner")
    | _ => ("sub", "%x", "%y", "%inner", "%x")
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 7 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %y = \"llvm.mlir.constant\"() <{value = 3 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %inner = \"llvm." ++ innerOpcode ++ "\"(" ++ innerLhs ++ ", " ++ innerRhs ++
      ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.sub\"(" ++ rootLhs ++ ", " ++ rootRhs ++ ") : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def i1IntrinsicBinarySource (opcode : String) : String :=
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 1 : i1}> : () -> i1" ++
    "\n  %y = \"llvm.mlir.constant\"() <{value = 0 : i1}> : () -> i1" ++
    "\n  %root = \"llvm.intr." ++ opcode ++ "\"(%x, %y) : (i1, i1) -> i1" ++
    "\n  \"test.test\"(%root) : (i1) -> ()\n}) : () -> ()"

private def i1CountZerosSource (opcode : String) (zeroPoison : Bool) : String :=
  let flag := if zeroPoison then "1" else "0"
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 1 : i1}> : () -> i1" ++
    "\n  %root = \"llvm.intr." ++ opcode ++ "\"(%x) <{is_zero_poison = " ++ flag ++
      " : i1}> : (i1) -> i1" ++
    "\n  \"test.test\"(%root) : (i1) -> ()\n}) : () -> ()"

private def runIntrinsicRule (text : String) (rule : Pattern OpCode)
    (source replacement : OpCode) (constant : Option Int := none) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString text.toUTF8
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw "intrinsic rewrite did not fire"
  ensureTestRootReplaced ctx.raw rewritten.raw
  if hasOp rewritten.raw source then throw "matched intrinsic root was not erased"
  if !hasOp rewritten.raw replacement then throw "replacement operation was not created"
  if let some value := constant then
    if !hasIntegerConstant rewritten.raw 1 value then
      throw "replacement constant was not normalized at i1"
  rewritten.verify moduleOp

private def bitwiseIdentitySource (width : Nat) (rootOpcode firstOpcode secondOpcode : String)
    (firstSwap secondSwap rootSwap : Bool := false) : String :=
  let ty := s!"i{width}"
  let (firstLhs, firstRhs) := if firstSwap then ("%b", "%a") else ("%a", "%b")
  let (secondLhs, secondRhs) := if secondSwap then ("%b", "%a") else ("%a", "%b")
  let (rootLhs, rootRhs) := if rootSwap then ("%second", "%first") else ("%first", "%second")
  "\"builtin.module\"() ({\n  %a = \"llvm.mlir.constant\"() <{value = 85 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %b = \"llvm.mlir.constant\"() <{value = 51 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %first = \"llvm." ++ firstOpcode ++ "\"(" ++ firstLhs ++ ", " ++ firstRhs ++
      ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %second = \"llvm." ++ secondOpcode ++ "\"(" ++ secondLhs ++ ", " ++ secondRhs ++
      ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm." ++ rootOpcode ++ "\"(" ++ rootLhs ++ ", " ++ rootRhs ++
      ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def subAndNotSource (width : Nat) (commuted : Bool := false) : String :=
  let ty := s!"i{width}"
  let (lhs, rhs) := if commuted then ("%y", "%x") else ("%x", "%y")
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 85 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %y = \"llvm.mlir.constant\"() <{value = 51 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %masked = \"llvm.and\"(" ++ lhs ++ ", " ++ rhs ++ ") : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  %root = \"llvm.sub\"(%x, %masked) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def subOrSelfSource (width : Nat) (commuted : Bool := false) : String :=
  let ty := s!"i{width}"
  let (lhs, rhs) := if commuted then ("%y", "%x") else ("%x", "%y")
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 85 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %y = \"llvm.mlir.constant\"() <{value = 51 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %either = \"llvm.or\"(" ++ lhs ++ ", " ++ rhs ++ ") : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  %root = \"llvm.sub\"(%either, %x) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def addOrNegatedConstantSource (width : Nat) (commuted : Bool := false) : String :=
  let ty := s!"i{width}"
  let (lhs, rhs) := if commuted then ("%inner_constant", "%x")
    else ("%x", "%inner_constant")
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 85 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %inner_constant = \"llvm.mlir.constant\"() <{value = -13 : " ++ ty ++
      "}> : () -> " ++ ty ++
    "\n  %either = \"llvm.or\"(" ++ lhs ++ ", " ++ rhs ++ ") : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  %outer_constant = \"llvm.mlir.constant\"() <{value = 13 : " ++ ty ++
      "}> : () -> " ++ ty ++
    "\n  %root = \"llvm.add\"(%either, %outer_constant) : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def mulShiftConstantSource (width : Nat) (innerNSW : Bool := false) : String :=
  let ty := s!"i{width}"
  let shiftFlags := if innerNSW then " <{\"overflowFlags\" = 1 : i32}>" else ""
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 7 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %amount = \"llvm.mlir.constant\"() <{value = 2 : " ++ ty ++
      "}> : () -> " ++ ty ++
    "\n  %shifted = \"llvm.shl\"(%x, %amount)" ++ shiftFlags ++ " : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  %multiplier = \"llvm.mlir.constant\"() <{value = 3 : " ++ ty ++
      "}> : () -> " ++ ty ++
    "\n  %root = \"llvm.mul\"(%shifted, %multiplier) : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def mulShiftConstantNUWSource (width : Nat) : String :=
  let ty := s!"i{width}"
  let nuw := " <{\"overflowFlags\" = 2 : i32}>"
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 7 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %amount = \"llvm.mlir.constant\"() <{value = 2 : " ++ ty ++
      "}> : () -> " ++ ty ++
    "\n  %shifted = \"llvm.shl\"(%x, %amount)" ++ nuw ++ " : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  %multiplier = \"llvm.mlir.constant\"() <{value = 3 : " ++ ty ++
      "}> : () -> " ++ ty ++
    "\n  %root = \"llvm.mul\"(%shifted, %multiplier)" ++ nuw ++ " : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def mulShiftConstantNSWSource (width : Nat) : String :=
  let ty := s!"i{width}"
  let nsw := " <{\"overflowFlags\" = 1 : i32}>"
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 7 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %amount = \"llvm.mlir.constant\"() <{value = 2 : " ++ ty ++
      "}> : () -> " ++ ty ++
    "\n  %shifted = \"llvm.shl\"(%x, %amount)" ++ nsw ++ " : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  %multiplier = \"llvm.mlir.constant\"() <{value = 3 : " ++ ty ++
      "}> : () -> " ++ ty ++
    "\n  %root = \"llvm.mul\"(%shifted, %multiplier)" ++ nsw ++ " : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def xorSelfInnerSource (width : Nat) (innerOpcode : String)
    (rootCommuted innerCommuted : Bool := false) : String :=
  let ty := s!"i{width}"
  let (innerLhs, innerRhs) := if innerCommuted then ("%y", "%x") else ("%x", "%y")
  let (rootLhs, rootRhs) := if rootCommuted then ("%inner", "%y") else ("%y", "%inner")
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 85 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %y = \"llvm.mlir.constant\"() <{value = 51 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %inner = \"llvm." ++ innerOpcode ++ "\"(" ++ innerLhs ++ ", " ++ innerRhs ++
      ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.xor\"(" ++ rootLhs ++ ", " ++ rootRhs ++
      ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def xorAndNotNotSource (width : Nat) (andCommuted : Bool := false)
    (notBLeft notALeft : Bool := false) : String :=
  let ty := s!"i{width}"
  let (notBLhs, notBRhs) := if notBLeft then ("%minus_one", "%b") else ("%b", "%minus_one")
  let (notALhs, notARhs) := if notALeft then ("%minus_one", "%a") else ("%a", "%minus_one")
  let (andLhs, andRhs) := if andCommuted then ("%not_b", "%a") else ("%a", "%not_b")
  "\"builtin.module\"() ({\n  %a = \"llvm.mlir.constant\"() <{value = 85 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %b = \"llvm.mlir.constant\"() <{value = 51 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %not_b = \"llvm.xor\"(" ++ notBLhs ++ ", " ++ notBRhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %masked = \"llvm.and\"(" ++ andLhs ++ ", " ++ andRhs ++ ") : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %not_a = \"llvm.xor\"(" ++ notALhs ++ ", " ++ notARhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.xor\"(%masked, %not_a) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def xorNotAndSelfSource (width : Nat) (rootCommuted andCommuted : Bool := false)
    (notLeft : Bool := false) : String :=
  let ty := s!"i{width}"
  let (notALhs, notARhs) := if notLeft then ("%minus_one", "%a") else ("%a", "%minus_one")
  let (andLhs, andRhs) := if andCommuted then ("%b", "%not_a") else ("%not_a", "%b")
  let (rootLhs, rootRhs) := if rootCommuted then ("%a", "%masked") else ("%masked", "%a")
  "\"builtin.module\"() ({\n  %a = \"llvm.mlir.constant\"() <{value = 85 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %b = \"llvm.mlir.constant\"() <{value = 51 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %not_a = \"llvm.xor\"(" ++ notALhs ++ ", " ++ notARhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %masked = \"llvm.and\"(" ++ andLhs ++ ", " ++ andRhs ++ ") : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.xor\"(" ++ rootLhs ++ ", " ++ rootRhs ++ ") : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def xorXorOrSharedSource (width : Nat)
    (rootCommuted orCommuted sharedRight : Bool := false) : String :=
  let ty := s!"i{width}"
  let shared := if sharedRight then "%b" else "%a"
  let (orLhs, orRhs) := if orCommuted then ("%c", shared) else (shared, "%c")
  let (rootLhs, rootRhs) := if rootCommuted then ("%inner_or", "%inner_xor")
    else ("%inner_xor", "%inner_or")
  "\"builtin.module\"() ({\n  %a = \"llvm.mlir.constant\"() <{value = 85 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %b = \"llvm.mlir.constant\"() <{value = 51 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %c = \"llvm.mlir.constant\"() <{value = 15 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %inner_xor = \"llvm.xor\"(%a, %b) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %inner_or = \"llvm.or\"(" ++ orLhs ++ ", " ++ orRhs ++ ") : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.xor\"(" ++ rootLhs ++ ", " ++ rootRhs ++ ") : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def andOrNotAndSource (width : Nat) (andCommuted : Bool := false) (notLeft : Bool := false) : String :=
  let ty := s!"i{width}"
  let (notInnerAndLhs, notInnerAndRhs) := if notLeft then ("%minus_one", "%inner_and") else ("%inner_and", "%minus_one")
  let (andLhs, andRhs) := if andCommuted then ("%b", "%a") else ("%a", "%b")
  "\"builtin.module\"() ({\n  %a = \"llvm.mlir.constant\"() <{value = 85 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %b = \"llvm.mlir.constant\"() <{value = 51 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %inner_or = \"llvm.or\"(%a, %b) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %inner_and = \"llvm.and\"(" ++ andLhs ++ ", " ++ andRhs ++ ") : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %not_and = \"llvm.xor\"(" ++ notInnerAndLhs ++ ", " ++ notInnerAndRhs ++ ") : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  %root = \"llvm.and\"(%inner_or, %not_and) : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def orComplementaryMasksSource (width : Nat)
    (leftCommuted rightCommuted : Bool := false)
    (notBLeft notALeft : Bool := false) : String :=
  let ty := s!"i{width}"
  let (notBLhs, notBRhs) := if notBLeft then ("%minus_one", "%b") else ("%b", "%minus_one")
  let (notALhs, notARhs) := if notALeft then ("%minus_one", "%a") else ("%a", "%minus_one")
  let (leftLhs, leftRhs) := if leftCommuted then ("%not_b", "%a") else ("%a", "%not_b")
  let (rightLhs, rightRhs) := if rightCommuted then ("%b", "%not_a") else ("%not_a", "%b")
  "\"builtin.module\"() ({\n  %a = \"llvm.mlir.constant\"() <{value = 85 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %b = \"llvm.mlir.constant\"() <{value = 51 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %not_b = \"llvm.xor\"(" ++ notBLhs ++ ", " ++ notBRhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %left = \"llvm.and\"(" ++ leftLhs ++ ", " ++ leftRhs ++ ") : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %not_a = \"llvm.xor\"(" ++ notALhs ++ ", " ++ notARhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %right = \"llvm.and\"(" ++ rightLhs ++ ", " ++ rightRhs ++ ") : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.or\"(%left, %right) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def xorComplementarySource (width : Nat) (innerOpcode : String)
    (rootCommuted innerCommuted : Bool := false)
    (notBLeft notALeft : Bool := false) : String :=
  let ty := s!"i{width}"
  let (notBLhs, notBRhs) := if notBLeft then ("%minus_one", "%b") else ("%b", "%minus_one")
  let (notALhs, notARhs) := if notALeft then ("%minus_one", "%a") else ("%a", "%minus_one")
  let commuteLeft := innerCommuted && !rootCommuted
  let commuteRight := innerCommuted && rootCommuted
  let (leftLhs, leftRhs) := if commuteLeft then ("%not_b", "%a") else ("%a", "%not_b")
  let (rightLhs, rightRhs) := if commuteRight then ("%b", "%not_a") else ("%not_a", "%b")
  let (rootLhs, rootRhs) := if rootCommuted then ("%right", "%left") else ("%left", "%right")
  "\"builtin.module\"() ({\n  %a = \"llvm.mlir.constant\"() <{value = 85 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %b = \"llvm.mlir.constant\"() <{value = 51 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %not_b = \"llvm.xor\"(" ++ notBLhs ++ ", " ++ notBRhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %left = \"llvm." ++ innerOpcode ++ "\"(" ++ leftLhs ++ ", " ++ leftRhs ++
      ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %not_a = \"llvm.xor\"(" ++ notALhs ++ ", " ++ notARhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %right = \"llvm." ++ innerOpcode ++ "\"(" ++ rightLhs ++ ", " ++ rightRhs ++
      ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.xor\"(" ++ rootLhs ++ ", " ++ rootRhs ++ ") : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def orNotOrSource (width : Nat) (firstOpcode : String)
    (orCommuted : Bool := false) (notLeft : Bool := false) : String :=
  let ty := s!"i{width}"
  let (notInnerOrLhs, notInnerOrRhs) := if notLeft then ("%minus_one", "%inner_or") else ("%inner_or", "%minus_one")
  let (orLhs, orRhs) := if orCommuted then ("%b", "%a") else ("%a", "%b")
  "\"builtin.module\"() ({\n  %a = \"llvm.mlir.constant\"() <{value = 85 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %b = \"llvm.mlir.constant\"() <{value = 51 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %first = \"llvm." ++ firstOpcode ++ "\"(%a, %b) : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  %inner_or = \"llvm.or\"(" ++ orLhs ++ ", " ++ orRhs ++ ") : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %not_or = \"llvm.xor\"(" ++ notInnerOrLhs ++ ", " ++ notInnerOrRhs ++ ") : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  %root = \"llvm.or\"(%first, %not_or) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def andComplementaryOrsSource (width : Nat)
    (leftCommuted rightCommuted : Bool := false)
    (notBLeft notALeft : Bool := false) : String :=
  let ty := s!"i{width}"
  let (notBLhs, notBRhs) := if notBLeft then ("%minus_one", "%b") else ("%b", "%minus_one")
  let (notALhs, notARhs) := if notALeft then ("%minus_one", "%a") else ("%a", "%minus_one")
  let (leftLhs, leftRhs) := if leftCommuted then ("%not_b", "%a") else ("%a", "%not_b")
  let (rightLhs, rightRhs) := if rightCommuted then ("%b", "%not_a") else ("%not_a", "%b")
  "\"builtin.module\"() ({\n  %a = \"llvm.mlir.constant\"() <{value = 85 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %b = \"llvm.mlir.constant\"() <{value = 51 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %not_b = \"llvm.xor\"(" ++ notBLhs ++ ", " ++ notBRhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %left = \"llvm.or\"(" ++ leftLhs ++ ", " ++ leftRhs ++ ") : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %not_a = \"llvm.xor\"(" ++ notALhs ++ ", " ++ notARhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %right = \"llvm.or\"(" ++ rightLhs ++ ", " ++ rightRhs ++ ") : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.and\"(%left, %right) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def notInnerNotSource (width : Nat) (innerOpcode : String)
    (commuted : Bool := false) (innerNotLeft rootNotLeft : Bool := false) : String :=
  let ty := s!"i{width}"
  let xValue := if width = 1 then "1" else "85"
  let yValue := if width = 1 then "0" else "51"
  let (notXLhs, notXRhs) := if innerNotLeft then ("%minus_one", "%x") else ("%x", "%minus_one")
  let (notInnerLhs, notInnerRhs) := if rootNotLeft then ("%minus_one", "%inner") else ("%inner", "%minus_one")
  let (innerLhs, innerRhs) := if commuted then ("%y", "%not_x") else ("%not_x", "%y")
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = " ++ xValue ++ " : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %y = \"llvm.mlir.constant\"() <{value = " ++ yValue ++ " : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %not_x = \"llvm.xor\"(" ++ notXLhs ++ ", " ++ notXRhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %inner = \"llvm." ++ innerOpcode ++ "\"(" ++ innerLhs ++ ", " ++ innerRhs ++
      ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.xor\"(" ++ notInnerLhs ++ ", " ++ notInnerRhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def xorNotMixedSource (width : Nat) (firstOpcode secondOpcode : String)
    (secondCommuted : Bool := false) (notLeft : Bool := false) : String :=
  let ty := s!"i{width}"
  let (notSecondLhs, notSecondRhs) := if notLeft then ("%minus_one", "%second") else ("%second", "%minus_one")
  let (secondLhs, secondRhs) := if secondCommuted then ("%b", "%a") else ("%a", "%b")
  "\"builtin.module\"() ({\n  %a = \"llvm.mlir.constant\"() <{value = 85 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %b = \"llvm.mlir.constant\"() <{value = 51 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %first = \"llvm." ++ firstOpcode ++ "\"(%a, %b) : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  %second = \"llvm." ++ secondOpcode ++ "\"(" ++ secondLhs ++ ", " ++ secondRhs ++
      ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %not_second = \"llvm.xor\"(" ++ notSecondLhs ++ ", " ++ notSecondRhs ++ ") : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  %root = \"llvm.xor\"(%first, %not_second) : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def mulDoubleNegSource (width : Nat) (nsw : Bool := false) : String :=
  let ty := s!"i{width}"
  let flags := if nsw then " <{\"overflowFlags\" = 1 : i32}>" else ""
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 7 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %y = \"llvm.mlir.constant\"() <{value = -11 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %zero_x = \"llvm.mlir.constant\"() <{value = 0 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %neg_x = \"llvm.sub\"(%zero_x, %x)" ++ flags ++ " : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %zero_y = \"llvm.mlir.constant\"() <{value = 0 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %neg_y = \"llvm.sub\"(%zero_y, %y)" ++ flags ++ " : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.mul\"(%neg_x, %neg_y)" ++ flags ++ " : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def mulSinkNegSource (width : Nat) (commuted : Bool := false) : String :=
  let ty := s!"i{width}"
  let (lhs, rhs) := if commuted then ("%y", "%neg_x") else ("%neg_x", "%y")
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 7 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %y = \"llvm.mlir.constant\"() <{value = -11 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %zero = \"llvm.mlir.constant\"() <{value = 0 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %neg_x = \"llvm.sub\"(%zero, %x) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.mul\"(" ++ lhs ++ ", " ++ rhs ++ ") : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def mulNegConstantSource (width : Nat) (constant : Int) : String :=
  let ty := s!"i{width}"
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 7 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %zero = \"llvm.mlir.constant\"() <{value = 0 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %neg_x = \"llvm.sub\"(%zero, %x) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %constant = \"llvm.mlir.constant\"() <{value = " ++ toString constant ++ " : " ++
      ty ++ "}> : () -> " ++ ty ++
    "\n  %root = \"llvm.mul\"(%neg_x, %constant) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++
      ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def runMulNegConstantCase (width : Nat) (constant : Int) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString (mulNegConstantSource width constant).toUTF8
  let some rewritten := RewritePattern.applyInContext
      (Pattern.compile Veir.Passes.InstCombineLLVM.MulNegConstant.mulNegConstant).run ctx
    | throw "mul-neg-constant rewrite did not fire"
  ensureTestRootReplaced ctx.raw rewritten.raw
  if !hasOp rewritten.raw (.llvm .mul) then
    throw "mul-neg-constant replacement multiply was not created"
  if !hasIntegerConstant rewritten.raw width (-constant) then
    throw "mul-neg-constant replacement constant has the wrong type or normalized value"
  rewritten.verify moduleOp

private def addSubAllOnesSource (width : Nat) : String :=
  let ty := s!"i{width}"
  let xValue := if width = 1 then "1" else "42"
  let yValue := if width = 1 then "0" else "-11"
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = " ++ xValue ++ " : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %y = \"llvm.mlir.constant\"() <{value = " ++ yValue ++ " : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %difference = \"llvm.sub\"(%x, %y) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++
      "}> : () -> " ++ ty ++
    "\n  %root = \"llvm.add\"(%difference, %minus_one) : (" ++ ty ++ ", " ++ ty ++
      ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def addSubConstantsSource (width : Nat) : String :=
  let ty := s!"i{width}"
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 19 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %c1 = \"llvm.mlir.constant\"() <{value = -23 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %inner = \"llvm.sub\"(%c1, %x) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %c2 = \"llvm.mlir.constant\"() <{value = 7 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %root = \"llvm.add\"(%inner, %c2) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def addOneNotSource (width : Nat) (variant : Nat) (notLeft : Bool := false) : String :=
  let ty := s!"i{width}"
  let aValue := if width = 1 then "0" else "42"
  let bValue := if width = 1 then "1" else "-11"
  let (notBLhs, notBRhs) := if notLeft then ("%minus_one", "%b") else ("%b", "%minus_one")
  let operations := if variant = 0 then
    "\n  %first = \"llvm.add\"(%a, %one) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.add\"(%first, %not_b) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty
  else if variant = 1 then
    "\n  %first = \"llvm.add\"(%a, %one) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.add\"(%not_b, %first) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty
  else if variant = 2 then
    "\n  %first = \"llvm.add\"(%not_b, %a) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.add\"(%first, %one) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty
  else
    "\n  %first = \"llvm.add\"(%a, %not_b) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.add\"(%first, %one) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty
  "\"builtin.module\"() ({\n  %a = \"llvm.mlir.constant\"() <{value = " ++ aValue ++ " : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %b = \"llvm.mlir.constant\"() <{value = " ++ bValue ++ " : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %one = \"llvm.mlir.constant\"() <{value = 1 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %not_b = \"llvm.xor\"(" ++ notBLhs ++ ", " ++ notBRhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    operations ++ "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def subAddAllOnesSource (width : Nat) : String :=
  let ty := s!"i{width}"
  let xValue := if width = 1 then "1" else "42"
  let yValue := if width = 1 then "0" else "-11"
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = " ++ xValue ++ " : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %y = \"llvm.mlir.constant\"() <{value = " ++ yValue ++ " : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %inner = \"llvm.add\"(%x, %minus_one) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.sub\"(%inner, %y) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def notSubSource (width : Nat) (notLeft : Bool := false) : String :=
  let ty := s!"i{width}"
  let xValue := if width = 1 then "1" else "42"
  let yValue := if width = 1 then "0" else "-11"
  let (notInnerLhs, notInnerRhs) := if notLeft then ("%minus_one", "%inner") else ("%inner", "%minus_one")
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = " ++ xValue ++ " : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %y = \"llvm.mlir.constant\"() <{value = " ++ yValue ++ " : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %inner = \"llvm.sub\"(%x, %y) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.xor\"(" ++ notInnerLhs ++ ", " ++ notInnerRhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def sharedNotXorSource (width : Nat) (orFirst : Bool)
    (andCommuted : Bool := false) (orCommuted : Bool := false)
    (notLeft : Bool := false) : String :=
  let ty := s!"i{width}"
  let aValue := if width = 1 then "1" else "85"
  let bValue := if width = 1 then "0" else "51"
  let dValue := if width = 1 then "1" else "15"
  let (notInnerLhs, notInnerRhs) := if notLeft then ("%minus_one", "%inner") else ("%inner", "%minus_one")
  let (lhs, rhs) := if orFirst then ("%either", "%both") else ("%both", "%either")
  let (andLhs, andRhs) := if andCommuted then ("%b", "%a") else ("%a", "%b")
  let (orLhs, orRhs) := if orCommuted then ("%d", "%a") else ("%a", "%d")
  "\"builtin.module\"() ({\n  %a = \"llvm.mlir.constant\"() <{value = " ++ aValue ++ " : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %b = \"llvm.mlir.constant\"() <{value = " ++ bValue ++ " : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %d = \"llvm.mlir.constant\"() <{value = " ++ dValue ++ " : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %both = \"llvm.and\"(" ++ andLhs ++ ", " ++ andRhs ++ ") : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %either = \"llvm.or\"(" ++ orLhs ++ ", " ++ orRhs ++ ") : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %inner = \"llvm.xor\"(" ++ lhs ++ ", " ++ rhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.xor\"(" ++ notInnerLhs ++ ", " ++ notInnerRhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def subSubConstantsSource (width : Nat) : String :=
  let ty := s!"i{width}"
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 19 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %c = \"llvm.mlir.constant\"() <{value = -23 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %c2 = \"llvm.mlir.constant\"() <{value = 7 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %inner = \"llvm.sub\"(%c2, %x) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.sub\"(%c, %inner) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def notNegOrSource (width : Nat) (commuted : Bool) (notLeft : Bool := false) : String :=
  let ty := s!"i{width}"
  let xValue := if width = 1 then "1" else "42"
  let yValue := if width = 1 then "0" else "-11"
  let (notEitherLhs, notEitherRhs) := if notLeft then ("%minus_one", "%either") else ("%either", "%minus_one")
  let (lhs, rhs) := if commuted then ("%y", "%neg") else ("%neg", "%y")
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = " ++ xValue ++ " : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %y = \"llvm.mlir.constant\"() <{value = " ++ yValue ++ " : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %zero = \"llvm.mlir.constant\"() <{value = 0 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %neg = \"llvm.sub\"(%zero, %x) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %either = \"llvm.or\"(" ++ lhs ++ ", " ++ rhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.xor\"(" ++ notEitherLhs ++ ", " ++ notEitherRhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def maskedMergeNotSource (width : Nat)
    (rootCommuted andCommuted deltaCommuted : Bool := false)
    (notLeft : Bool := false) : String :=
  let ty := s!"i{width}"
  let bValue := if width = 1 then "1" else "85"
  let xValue := if width = 1 then "0" else "51"
  let mValue := if width = 1 then "1" else "15"
  let (notMLhs, notMRhs) := if notLeft then ("%minus_one", "%m") else ("%m", "%minus_one")
  let (deltaLhs, deltaRhs) := if deltaCommuted then ("%x", "%b") else ("%b", "%x")
  let (maskedLhs, maskedRhs) :=
    if andCommuted then ("%not_m", "%delta") else ("%delta", "%not_m")
  let (rootLhs, rootRhs) := if rootCommuted then ("%masked", "%b") else ("%b", "%masked")
  "\"builtin.module\"() ({\n  %b = \"llvm.mlir.constant\"() <{value = " ++ bValue ++ " : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %x = \"llvm.mlir.constant\"() <{value = " ++ xValue ++ " : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %m = \"llvm.mlir.constant\"() <{value = " ++ mValue ++ " : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %delta = \"llvm.xor\"(" ++ deltaLhs ++ ", " ++ deltaRhs ++ ") : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %not_m = \"llvm.xor\"(" ++ notMLhs ++ ", " ++ notMRhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %masked = \"llvm.and\"(" ++ maskedLhs ++ ", " ++ maskedRhs ++ ") : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.xor\"(" ++ rootLhs ++ ", " ++ rootRhs ++ ") : (" ++ ty ++
      ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def notAddConstantSource (width : Nat) (constant : Int) (notLeft : Bool := false) : String :=
  let ty := s!"i{width}"
  let xValue := if width = 1 then "1" else "42"
  let (notSumLhs, notSumRhs) := if notLeft then ("%minus_one", "%sum") else ("%sum", "%minus_one")
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = " ++ xValue ++ " : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %c = \"llvm.mlir.constant\"() <{value = " ++ toString constant ++ " : " ++ ty ++
      "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++ "}> : () -> " ++ ty ++
    "\n  %sum = \"llvm.add\"(%x, %c) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.xor\"(" ++ notSumLhs ++ ", " ++ notSumRhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def negatePoisonSource (width : Nat) : String :=
  let ty := s!"i{width}"
  "\"builtin.module\"() ({\n  %zero = \"llvm.mlir.constant\"() <{value = 0 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %poison = \"llvm.mlir.poison\"() : () -> " ++ ty ++
    "\n  %root = \"llvm.sub\"(%zero, %poison) <{\"overflowFlags\" = 3 : i32}> : (" ++
      ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def dropWrapFlagsSource (width : Nat) (opcode : String)
    (withFlags : Bool := true) : String :=
  let ty := s!"i{width}"
  let flags := if withFlags then " <{\"overflowFlags\" = 3 : i32}>" else ""
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 7 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %y = \"llvm.mlir.constant\"() <{value = 1 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %root = \"llvm." ++ opcode ++ "\"(%x, %y)" ++ flags ++ " : (" ++
      ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def freeInvertDoubleNotSource (width : Nat) (innerLeft outerLeft : Bool) : String :=
  let ty := s!"i{width}"
  let (innerLhs, innerRhs) := if innerLeft then ("%minus_one", "%x") else ("%x", "%minus_one")
  let (outerLhs, outerRhs) := if outerLeft then ("%minus_one", "%inner") else ("%inner", "%minus_one")
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 1 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %inner = \"llvm.xor\"(" ++ innerLhs ++ ", " ++ innerRhs ++ ") : (" ++ ty ++
    ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.xor\"(" ++ outerLhs ++ ", " ++ outerRhs ++ ") : (" ++ ty ++
    ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def freeInvertBinarySource (width : Nat) (opcode : String)
    (invertLeft innerLeft outerLeft : Bool) (exact : Bool := false) : String :=
  let ty := s!"i{width}"
  let (notLhs, notRhs) := if innerLeft then ("%minus_one", "%x") else ("%x", "%minus_one")
  let (lhs, rhs) := if invertLeft then ("%not_x", "%y") else ("%y", "%not_x")
  let (outerLhs, outerRhs) := if outerLeft then ("%minus_one", "%inner") else ("%inner", "%minus_one")
  let props := if exact then " <{exact = true}>" else ""
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 5 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %y = \"llvm.mlir.constant\"() <{value = 1 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %not_x = \"llvm.xor\"(" ++ notLhs ++ ", " ++ notRhs ++ ") : (" ++ ty ++
    ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %inner = \"llvm." ++ opcode ++ "\"(" ++ lhs ++ ", " ++ rhs ++ ")" ++ props ++
    " : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.xor\"(" ++ outerLhs ++ ", " ++ outerRhs ++ ") : (" ++ ty ++
    ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def freeInvertConstantSource (width : Nat) (outerLeft poison : Bool) : String :=
  let ty := s!"i{width}"
  let valueOp := if poison then
    "  %value = \"llvm.mlir.poison\"() : () -> " ++ ty
  else
    "  %value = \"llvm.mlir.constant\"() <{value = " ++
      (if width = 1 then "1" else "5") ++ " : " ++ ty ++ "}> : () -> " ++ ty
  let (lhs, rhs) := if outerLeft then ("%minus_one", "%value") else ("%value", "%minus_one")
  "\"builtin.module\"() ({\n" ++ valueOp ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %root = \"llvm.xor\"(" ++ lhs ++ ", " ++ rhs ++ ") : (" ++ ty ++
    ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def freeInvertDeMorganSource (width : Nat) (opcode : String)
    (xLeft yLeft outerLeft : Bool) : String :=
  let ty := s!"i{width}"
  let (xLhs, xRhs) := if xLeft then ("%minus_one", "%x") else ("%x", "%minus_one")
  let (yLhs, yRhs) := if yLeft then ("%minus_one", "%y") else ("%y", "%minus_one")
  let (outerLhs, outerRhs) := if outerLeft then ("%minus_one", "%inner") else ("%inner", "%minus_one")
  "\"builtin.module\"() ({\n  %x = \"llvm.mlir.constant\"() <{value = 5 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %y = \"llvm.mlir.constant\"() <{value = 3 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %minus_one = \"llvm.mlir.constant\"() <{value = -1 : " ++ ty ++
    "}> : () -> " ++ ty ++
    "\n  %not_x = \"llvm.xor\"(" ++ xLhs ++ ", " ++ xRhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %not_y = \"llvm.xor\"(" ++ yLhs ++ ", " ++ yRhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %inner = \"llvm." ++ opcode ++ "\"(%not_x, %not_y) : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  %root = \"llvm.xor\"(" ++ outerLhs ++ ", " ++ outerRhs ++ ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++
    "\n  \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n}) : () -> ()"

private def ensureTestRootHasNoWrapFlags (ctx : IRContext OpCode)
    (opcode : Llvm) : Except String Unit := do
  let some root := testInputProducer? ctx
    | throw "test.test input has no defining operation"
  if h : root.InBounds ctx then
    if root.getOpType ctx h != (.llvm opcode) then
      throw "flag-clearing replacement has the wrong opcode"
    let flagsSet := match opcode with
      | .add =>
        let props := root.getProperties! ctx Llvm.add
        props.nsw || props.nuw
      | .sub =>
        let props := root.getProperties! ctx Llvm.sub
        props.nsw || props.nuw
      | .mul =>
        let props := root.getProperties! ctx Llvm.mul
        props.nsw || props.nuw
      | _ => true
    if flagsSet then throw "replacement retained an nsw or nuw flag"
  else
    throw "test.test input operation is out of bounds"

private def runDropWrapFlagsRule (text : String) (rule : Pattern OpCode)
    (opcode : Llvm) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString text.toUTF8
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw "flag-clearing rewrite did not fire"
  ensureTestRootReplaced ctx.raw rewritten.raw
  ensureTestRootHasNoWrapFlags rewritten.raw opcode
  rewritten.verify moduleOp

private def runDropWrapFlagsNoMatch (text : String) (rule : Pattern OpCode)
    (opcode : Llvm) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString text.toUTF8
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw "flag-clearing no-match execution did not return its context"
  if testInputProducer? rewritten.raw != testInputProducer? ctx.raw then
    throw "unflagged operation unexpectedly matched the flag-clearing rule"
  ensureTestRootHasNoWrapFlags rewritten.raw opcode
  rewritten.verify moduleOp

private def runBitwiseRule (text : String) (rule : Pattern OpCode)
    (root replacement : OpCode) (allOnesWidth : Option Nat := none)
    (skipRootCount : Bool := false) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString text.toUTF8
  let oldRootCount := countOp ctx root
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw "bitwise rewrite did not fire"
  ensureTestRootReplaced ctx.raw rewritten.raw
  if !skipRootCount && root != replacement && countOp rewritten.raw root >= oldRootCount then
    throw "matched bitwise root was not erased"
  if !hasOp rewritten.raw replacement then
    throw s!"bitwise replacement operation was not created: {repr replacement}"
  if let some width := allOnesWidth then
    if !hasIntegerConstant rewritten.raw width (-1) then
      throw "bitwise not constant does not have the matched type and normalized value"
  rewritten.verify moduleOp

private def runNSWRule (text : String) (rule : Pattern OpCode)
    (replacement : Llvm) (expectedConstant : Option (Nat × Int) := none) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString text.toUTF8
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw "NSW rewrite did not fire"
  ensureTestRootReplaced ctx.raw rewritten.raw
  if !hasNSWOp rewritten.raw replacement then
    throw "replacement operation did not preserve NSW"
  if let some (width, value) := expectedConstant then
    if !hasIntegerConstant rewritten.raw width value then
      throw "NSW replacement constant has the wrong matched type or normalized value"
  rewritten.verify moduleOp

private def runFoldedConstantRule (text : String) (rule : Pattern OpCode)
    (replacement : OpCode) (width : Nat) (expected : Int)
    (expectedNSW : Option Bool := none) (expectedNUW : Option Bool := none) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString text.toUTF8
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw "constant-folding rewrite did not fire"
  ensureTestRootReplaced ctx.raw rewritten.raw
  if !hasOp rewritten.raw replacement then throw "replacement operation was not created"
  if !hasIntegerConstant rewritten.raw width expected then
    throw "folded constant has the wrong matched type or normalized value"
  if let some expected := expectedNSW then
    if hasNSWOp rewritten.raw .mul != expected then
      throw "folded multiply has the wrong NSW flag"
  if let some expected := expectedNUW then
    if hasNUWOp rewritten.raw .mul != expected then
      throw "folded multiply has the wrong NUW flag"
  rewritten.verify moduleOp

private def regression : Except String Unit := do
  runNegateConstantCase 8 127
  runNegateConstantCase 8 (-7)
  runNegateConstantCase 8 (-128)
  runNegateConstantCase 32 1234567
  runCase 8 false
  runCase 32 false
  runCase 8 true
  runCase 32 true
  runRule (commutedIncrementSource 8)
    Veir.Passes.InstCombineLLVM.NegateIncrement.negateIncrementCommuted
  runRule (commutedIncrementSource 32)
    Veir.Passes.InstCombineLLVM.NegateIncrement.negateIncrementCommuted
  for width in [8, 32] do
    runRule (doubleNegationSource width)
      Veir.Passes.InstCombineLLVM.DoubleNegation.doubleNegation
    runRule (subSwapSource width) Veir.Passes.InstCombineLLVM.SubSwap.subSwap
    runRule (subSwapNSWSource width) Veir.Passes.InstCombineLLVM.SubSwap.subSwapNSW
  runRule negateI1Source Veir.Passes.InstCombineLLVM.NegateI1.negateI1
  for width in [8, 32] do
    runRule (negateBooleanExtensionSource width false)
      Veir.Passes.InstCombineLLVM.NegateBooleanExtension.negateSExtI1
    runRule (negateBooleanExtensionSource width true false)
      Veir.Passes.InstCombineLLVM.NegateBooleanExtension.negateZExtI1
    runRule (negateBooleanExtensionSource width true true)
      Veir.Passes.InstCombineLLVM.NegateBooleanExtension.negateZExtI1
  runRule (negateRightShiftSource 8 false true)
    Veir.Passes.InstCombineLLVM.NegateRightShift.negateAShrSignBit
  runRule (negateRightShiftSource 8 true true)
    Veir.Passes.InstCombineLLVM.NegateRightShift.negateLShrSignBit
  runRule (negateRightShiftSource 32 false false)
    Veir.Passes.InstCombineLLVM.NegateRightShift.negateAShrSignBit
  runRule (negateRightShiftSource 32 true false)
    Veir.Passes.InstCombineLLVM.NegateRightShift.negateLShrSignBit
  runRule (negateTruncSource 16 8)
    Veir.Passes.InstCombineLLVM.NegateTrunc.negateTruncDoubleNegation
  runRule (negateTruncSource 64 32)
    Veir.Passes.InstCombineLLVM.NegateTrunc.negateTruncDoubleNegation
  runRule (negateTruncCommuteSource 16 8)
    Veir.Passes.InstCombineLLVM.NegateTrunc.negateTruncCommute
  runRule (negateTruncCommuteSource 64 32)
    Veir.Passes.InstCombineLLVM.NegateTrunc.negateTruncCommute
  runRule (i1BinopSource "add")
    Veir.Passes.InstCombineLLVM.AddI1.addI1ToXor
  runRule (i1BinopSource "sub")
    Veir.Passes.InstCombineLLVM.SubI1.subI1ToXor
  for width in [8, 32] do
    runRule (allOnesSubSource width)
      Veir.Passes.InstCombineLLVM.AllOnesSub.allOnesSubToNot
  runRule (negatedOperandSource 8 0)
    Veir.Passes.InstCombineLLVM.AddNegNeg.addNegNeg
  runRule (negatedOperandSource 8 1)
    Veir.Passes.InstCombineLLVM.AddNegLeft.addNegLeft
  runNSWRule (negatedOperandSource 8 1 true)
    Veir.Passes.InstCombineLLVM.AddNegLeft.addNegLeftNSW .sub
  runRule (negatedOperandSource 8 2)
    Veir.Passes.InstCombineLLVM.AddNegRight.addNegRight
  runNSWRule (negatedOperandSource 8 2 true)
    Veir.Passes.InstCombineLLVM.AddNegRight.addNegRightNSW .sub
  runRule (negatedOperandSource 8 3)
    Veir.Passes.InstCombineLLVM.SubNegRight.subNegRight
  runNSWRule (negatedOperandSource 8 3 true)
    Veir.Passes.InstCombineLLVM.SubNegRight.subNegRightNSW .add
  runFoldedConstantRule (subNegConstantSource 8 (-128))
    Veir.Passes.InstCombineLLVM.SubNegRight.subNegConstant (.llvm .add) 8 128
  runFoldedConstantRule (subNegConstantSource 32 1234567)
    Veir.Passes.InstCombineLLVM.SubNegRight.subNegConstant (.llvm .add) 32 (-1234567)
  runNSWRule (subNegConstantSource 8 (-7) true)
    Veir.Passes.InstCombineLLVM.SubNegRight.subNegConstantNSW .add (some (8, 7))
  runRule (subCancellationSource 8 0)
    Veir.Passes.InstCombineLLVM.SubCancellation.subAddSelf
  runRule (subCancellationSource 8 1)
    Veir.Passes.InstCombineLLVM.SubCancellation.subAddSelfCommuted
  runRule (subCancellationSource 8 2)
    Veir.Passes.InstCombineLLVM.SubCancellation.subSelfFromSub
  runIntrinsicRule (i1IntrinsicBinarySource "umin")
    Veir.Passes.InstCombineLLVM.I1MinMaxAnd.uminI1ToAnd
    (.llvm .intr__umin) (.llvm .and)
  runIntrinsicRule (i1IntrinsicBinarySource "smax")
    Veir.Passes.InstCombineLLVM.I1MinMaxAnd.smaxI1ToAnd
    (.llvm .intr__smax) (.llvm .and)
  runIntrinsicRule (i1IntrinsicBinarySource "umax")
    Veir.Passes.InstCombineLLVM.I1MinMaxOr.umaxI1ToOr
    (.llvm .intr__umax) (.llvm .or)
  runIntrinsicRule (i1IntrinsicBinarySource "smin")
    Veir.Passes.InstCombineLLVM.I1MinMaxOr.sminI1ToOr
    (.llvm .intr__smin) (.llvm .or)
  runIntrinsicRule (i1CountZerosSource "ctlz" false)
    Veir.Passes.InstCombineLLVM.I1CountZeros.ctlzI1ToNot
    (.llvm .intr__ctlz) (.llvm .xor) (some (-1))
  runIntrinsicRule (i1CountZerosSource "cttz" false)
    Veir.Passes.InstCombineLLVM.I1CountZeros.cttzI1ToNot
    (.llvm .intr__cttz) (.llvm .xor) (some (-1))
  runIntrinsicRule (i1CountZerosSource "ctlz" true)
    Veir.Passes.InstCombineLLVM.I1CountZeros.ctlzI1ToZero
    (.llvm .intr__ctlz) (.llvm .mlir__constant) (some 0)
  runIntrinsicRule (i1CountZerosSource "cttz" true)
    Veir.Passes.InstCombineLLVM.I1CountZeros.cttzI1ToZero
    (.llvm .intr__cttz) (.llvm .mlir__constant) (some 0)
  for width in [8, 32] do
    runBitwiseRule (bitwiseIdentitySource width "add" "xor" "and")
      Veir.Passes.InstCombineLLVM.AddXorAnd.addXorAnd (.llvm .add) (.llvm .or)
    runBitwiseRule (bitwiseIdentitySource width "sub" "or" "and")
      Veir.Passes.InstCombineLLVM.SubOrAnd.subOrAnd (.llvm .sub) (.llvm .xor)
    runBitwiseRule (bitwiseIdentitySource width "sub" "add" "or")
      Veir.Passes.InstCombineLLVM.SubAddOr.subAddOr (.llvm .sub) (.llvm .and)
    runBitwiseRule (bitwiseIdentitySource width "sub" "add" "and")
      Veir.Passes.InstCombineLLVM.SubAddAnd.subAddAnd (.llvm .sub) (.llvm .or)
    runBitwiseRule (bitwiseIdentitySource width "sub" "or" "xor")
      Veir.Passes.InstCombineLLVM.SubOrXor.subOrXor (.llvm .sub) (.llvm .and)
    runBitwiseRule (subAndNotSource width)
      Veir.Passes.InstCombineLLVM.SubAndNot.subAndNot (.llvm .sub) (.llvm .xor) (some width)
    runBitwiseRule (subOrSelfSource width)
      Veir.Passes.InstCombineLLVM.SubOrSelf.subOrSelf (.llvm .sub) (.llvm .and) (some width)
    runBitwiseRule (addOrNegatedConstantSource width)
      Veir.Passes.InstCombineLLVM.AddOrNegatedConstant.addOrNegatedConstant
        (.llvm .add) (.llvm .xor)
    runFoldedConstantRule (mulShiftConstantSource width)
      Veir.Passes.InstCombineLLVM.MulShiftConstant.mulShiftConstant
      (.llvm .mul) width 12
  runBitwiseRule (bitwiseIdentitySource 8 "add" "xor" "and" false true false)
    Veir.Passes.InstCombineLLVM.AddXorAnd.addXorAndCommutedAnd (.llvm .add) (.llvm .or)
  runBitwiseRule (bitwiseIdentitySource 8 "add" "xor" "and" false false true)
    Veir.Passes.InstCombineLLVM.AddXorAnd.addAndXor (.llvm .add) (.llvm .or)
  runBitwiseRule (bitwiseIdentitySource 8 "add" "xor" "and" false true true)
    Veir.Passes.InstCombineLLVM.AddXorAnd.addCommutedAndXor (.llvm .add) (.llvm .or)
  runBitwiseRule (bitwiseIdentitySource 8 "sub" "or" "and" true)
    Veir.Passes.InstCombineLLVM.SubOrAnd.subCommutedOrAnd (.llvm .sub) (.llvm .xor)
  runBitwiseRule (bitwiseIdentitySource 8 "sub" "add" "or" false true)
    Veir.Passes.InstCombineLLVM.SubAddOr.subAddCommutedOr (.llvm .sub) (.llvm .and)
  runBitwiseRule (bitwiseIdentitySource 8 "sub" "add" "and" false true)
    Veir.Passes.InstCombineLLVM.SubAddAnd.subAddCommutedAnd (.llvm .sub) (.llvm .or)
  runBitwiseRule (bitwiseIdentitySource 8 "sub" "or" "xor" true)
    Veir.Passes.InstCombineLLVM.SubOrXor.subCommutedOrXor (.llvm .sub) (.llvm .and)
  runBitwiseRule (subAndNotSource 8 true)
    Veir.Passes.InstCombineLLVM.SubAndNot.subCommutedAndNot
      (.llvm .sub) (.llvm .xor) (some 8)
  runBitwiseRule (subOrSelfSource 8 true)
    Veir.Passes.InstCombineLLVM.SubOrSelf.subCommutedOrSelf
      (.llvm .sub) (.llvm .and) (some 8)
  runBitwiseRule (addOrNegatedConstantSource 8 true)
    Veir.Passes.InstCombineLLVM.AddOrNegatedConstant.addCommutedOrNegatedConstant
      (.llvm .add) (.llvm .xor)
  runFoldedConstantRule (mulShiftConstantSource 8 true)
    Veir.Passes.InstCombineLLVM.MulShiftConstant.mulShiftConstantOuterUnflagged
    (.llvm .mul) 8 12 (some false)
  runFoldedConstantRule (mulShiftConstantNUWSource 8)
    Veir.Passes.InstCombineLLVM.MulShiftConstant.mulShiftConstantNUW
    (.llvm .mul) 8 12 (some false) (some true)
  runFoldedConstantRule (mulShiftConstantNSWSource 8)
    Veir.Passes.InstCombineLLVM.MulShiftConstant.mulShiftConstantNSW
    (.llvm .mul) 8 12 (some true) (some false)
  for width in [8, 32] do
    runBitwiseRule (bitwiseIdentitySource width "xor" "and" "or")
      Veir.Passes.InstCombineLLVM.XorAndOr.xorAndOr (.llvm .xor) (.llvm .xor)
    runBitwiseRule (bitwiseIdentitySource width "xor" "and" "xor")
      Veir.Passes.InstCombineLLVM.XorAndXor.xorAndXor (.llvm .xor) (.llvm .or)
  runBitwiseRule (bitwiseIdentitySource 8 "xor" "and" "or" false true)
    Veir.Passes.InstCombineLLVM.XorAndOr.xorAndCommutedOr (.llvm .xor) (.llvm .xor)
  runBitwiseRule (bitwiseIdentitySource 8 "xor" "and" "or" false false true)
    Veir.Passes.InstCombineLLVM.XorAndOr.xorOrAnd (.llvm .xor) (.llvm .xor)
  runBitwiseRule (bitwiseIdentitySource 8 "xor" "and" "or" true false true)
    Veir.Passes.InstCombineLLVM.XorAndOr.xorOrCommutedAnd (.llvm .xor) (.llvm .xor)
  runBitwiseRule (bitwiseIdentitySource 8 "xor" "and" "xor" false true)
    Veir.Passes.InstCombineLLVM.XorAndXor.xorAndCommutedXor (.llvm .xor) (.llvm .or)
  runBitwiseRule (bitwiseIdentitySource 8 "xor" "and" "xor" false false true)
    Veir.Passes.InstCombineLLVM.XorAndXor.xorXorAnd (.llvm .xor) (.llvm .or)
  runBitwiseRule (bitwiseIdentitySource 8 "xor" "and" "xor" true false true)
    Veir.Passes.InstCombineLLVM.XorAndXor.xorXorCommutedAnd (.llvm .xor) (.llvm .or)
  for width in [8, 32] do
    runBitwiseRule (xorSelfInnerSource width "or")
      Veir.Passes.InstCombineLLVM.XorOrSelf.xorOrSelf
      (.llvm .xor) (.llvm .and) (some width) true
    runBitwiseRule (xorSelfInnerSource width "and")
      Veir.Passes.InstCombineLLVM.XorAndSelf.xorAndSelf
      (.llvm .xor) (.llvm .and) (some width) true
  runBitwiseRule (xorSelfInnerSource 8 "or" false true)
    Veir.Passes.InstCombineLLVM.XorOrSelf.xorCommutedOrSelf
    (.llvm .xor) (.llvm .and) (some 8) true
  runBitwiseRule (xorSelfInnerSource 8 "or" true false)
    Veir.Passes.InstCombineLLVM.XorOrSelf.orSelfXor
    (.llvm .xor) (.llvm .and) (some 8) true
  runBitwiseRule (xorSelfInnerSource 8 "or" true true)
    Veir.Passes.InstCombineLLVM.XorOrSelf.commutedOrSelfXor
    (.llvm .xor) (.llvm .and) (some 8) true
  runBitwiseRule (xorSelfInnerSource 8 "and" false true)
    Veir.Passes.InstCombineLLVM.XorAndSelf.xorCommutedAndSelf
    (.llvm .xor) (.llvm .and) (some 8) true
  runBitwiseRule (xorSelfInnerSource 8 "and" true false)
    Veir.Passes.InstCombineLLVM.XorAndSelf.andSelfXor
    (.llvm .xor) (.llvm .and) (some 8) true
  runBitwiseRule (xorSelfInnerSource 8 "and" true true)
    Veir.Passes.InstCombineLLVM.XorAndSelf.commutedAndSelfXor
    (.llvm .xor) (.llvm .and) (some 8) true
  for width in [8, 32] do
    runBitwiseRule (xorAndNotNotSource width)
      Veir.Passes.InstCombineLLVM.XorAndNotNot.xorAndNotNot
      (.llvm .xor) (.llvm .xor) (some width) true
    runBitwiseRule (xorNotAndSelfSource width)
      Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorNotAndSelf
      (.llvm .xor) (.llvm .or)
  runBitwiseRule (xorAndNotNotSource 8 true)
    Veir.Passes.InstCombineLLVM.XorAndNotNot.xorNotAndNot
    (.llvm .xor) (.llvm .xor) (some 8) true
  runBitwiseRule (xorNotAndSelfSource 8 false true)
    Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorCommutedNotAndSelf
    (.llvm .xor) (.llvm .or)
  runBitwiseRule (xorNotAndSelfSource 8 true false)
    Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorSelfNotAnd
    (.llvm .xor) (.llvm .or)
  runBitwiseRule (xorNotAndSelfSource 8 true true)
    Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorSelfCommutedNotAnd
    (.llvm .xor) (.llvm .or)
  for width in [8, 32] do
    runBitwiseRule (xorXorOrSharedSource width)
      Veir.Passes.InstCombineLLVM.XorXorOrShared.xorXorOrShared
      (.llvm .xor) (.llvm .xor) (some width) true
  runBitwiseRule (xorXorOrSharedSource 8 false true)
    Veir.Passes.InstCombineLLVM.XorXorOrShared.xorXorCommutedOrShared
    (.llvm .xor) (.llvm .xor) (some 8) true
  runBitwiseRule (xorXorOrSharedSource 8 true false)
    Veir.Passes.InstCombineLLVM.XorXorOrShared.xorOrSharedXor
    (.llvm .xor) (.llvm .xor) (some 8) true
  runBitwiseRule (xorXorOrSharedSource 8 true true)
    Veir.Passes.InstCombineLLVM.XorXorOrShared.xorCommutedOrSharedXor
    (.llvm .xor) (.llvm .xor) (some 8) true
  runBitwiseRule (xorXorOrSharedSource 8 false false true)
    Veir.Passes.InstCombineLLVM.XorXorOrShared.xorXorOrSharedRight
    (.llvm .xor) (.llvm .xor) (some 8) true
  runBitwiseRule (xorXorOrSharedSource 8 false true true)
    Veir.Passes.InstCombineLLVM.XorXorOrShared.xorXorCommutedOrSharedRight
    (.llvm .xor) (.llvm .xor) (some 8) true
  runBitwiseRule (xorXorOrSharedSource 8 true false true)
    Veir.Passes.InstCombineLLVM.XorXorOrShared.xorOrSharedRightXor
    (.llvm .xor) (.llvm .xor) (some 8) true
  runBitwiseRule (xorXorOrSharedSource 8 true true true)
    Veir.Passes.InstCombineLLVM.XorXorOrShared.xorCommutedOrSharedRightXor
    (.llvm .xor) (.llvm .xor) (some 8) true
  for width in [8, 32] do
    runBitwiseRule (andOrNotAndSource width)
      Veir.Passes.InstCombineLLVM.AndOrNotAnd.andOrNotAnd
      (.llvm .and) (.llvm .xor)
  runBitwiseRule (andOrNotAndSource 8 true)
    Veir.Passes.InstCombineLLVM.AndOrNotAnd.andOrNotCommutedAnd
    (.llvm .and) (.llvm .xor)
  for width in [8, 32] do
    runBitwiseRule (orComplementaryMasksSource width)
      Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orComplementaryMasks
      (.llvm .or) (.llvm .xor)
  runBitwiseRule (orComplementaryMasksSource 8 true false)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orLeftCommutedComplementaryMasks
    (.llvm .or) (.llvm .xor)
  runBitwiseRule (orComplementaryMasksSource 8 false true)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orRightCommutedComplementaryMasks
    (.llvm .or) (.llvm .xor)
  runBitwiseRule (orComplementaryMasksSource 8 true true)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orCommutedComplementaryMasks
    (.llvm .or) (.llvm .xor)
  for width in [8, 32] do
    runBitwiseRule (xorComplementarySource width "and")
      Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorComplementaryMasks
      (.llvm .xor) (.llvm .xor) none true
    runBitwiseRule (xorComplementarySource width "or")
      Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorComplementaryOrs
      (.llvm .xor) (.llvm .xor) none true
  runBitwiseRule (xorComplementarySource 8 "and" false true)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorLeftCommutedComplementaryMasks
    (.llvm .xor) (.llvm .xor) none true
  runBitwiseRule (xorComplementarySource 8 "and" true false)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedComplementaryMasks
    (.llvm .xor) (.llvm .xor) none true
  runBitwiseRule (xorComplementarySource 8 "and" true true)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedCommutedComplementaryMasks
    (.llvm .xor) (.llvm .xor) none true
  runBitwiseRule (xorComplementarySource 8 "or" false true)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorLeftCommutedComplementaryOrs
    (.llvm .xor) (.llvm .xor) none true
  runBitwiseRule (xorComplementarySource 8 "or" true false)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedComplementaryOrs
    (.llvm .xor) (.llvm .xor) none true
  runBitwiseRule (xorComplementarySource 8 "or" true true)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedCommutedComplementaryOrs
    (.llvm .xor) (.llvm .xor) none true
  for width in [8, 32] do
    runBitwiseRule (orNotOrSource width "and")
      Veir.Passes.InstCombineLLVM.OrAndNotOr.orAndNotOr
      (.llvm .or) (.llvm .xor) (some width)
    runBitwiseRule (orNotOrSource width "xor")
      Veir.Passes.InstCombineLLVM.OrXorNotOr.orXorNotOr
      (.llvm .or) (.llvm .xor) (some width)
  runBitwiseRule (orNotOrSource 8 "and" true)
    Veir.Passes.InstCombineLLVM.OrAndNotOr.orAndNotCommutedOr
    (.llvm .or) (.llvm .xor) (some 8)
  runBitwiseRule (orNotOrSource 8 "xor" true)
    Veir.Passes.InstCombineLLVM.OrXorNotOr.orXorNotCommutedOr
    (.llvm .or) (.llvm .xor) (some 8)
  for width in [8, 32] do
    runBitwiseRule (andComplementaryOrsSource width)
      Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andComplementaryOrs
      (.llvm .and) (.llvm .xor) (some width)
  runBitwiseRule (andComplementaryOrsSource 8 true false)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andLeftCommutedComplementaryOrs
    (.llvm .and) (.llvm .xor) (some 8)
  runBitwiseRule (andComplementaryOrsSource 8 false true)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andRightCommutedComplementaryOrs
    (.llvm .and) (.llvm .xor) (some 8)
  runBitwiseRule (andComplementaryOrsSource 8 true true)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andCommutedComplementaryOrs
    (.llvm .and) (.llvm .xor) (some 8)
  for width in [8, 32] do
    runBitwiseRule (notInnerNotSource width "and")
      Veir.Passes.InstCombineLLVM.NotAndNot.notAndNot
      (.llvm .xor) (.llvm .or) (some width) true
    runBitwiseRule (notInnerNotSource width "or")
      Veir.Passes.InstCombineLLVM.NotOrNot.notOrNot
      (.llvm .xor) (.llvm .and) (some width) true
  runBitwiseRule (notInnerNotSource 8 "and" true)
    Veir.Passes.InstCombineLLVM.NotAndNot.notCommutedAndNot
    (.llvm .xor) (.llvm .or) (some 8) true
  runBitwiseRule (notInnerNotSource 8 "or" true)
    Veir.Passes.InstCombineLLVM.NotOrNot.notCommutedOrNot
    (.llvm .xor) (.llvm .and) (some 8) true
  for width in [8, 32] do
    runBitwiseRule (xorNotMixedSource width "or" "and")
      Veir.Passes.InstCombineLLVM.XorNotMixed.xorOrNotAnd
      (.llvm .xor) (.llvm .xor) (some width) true
    runBitwiseRule (xorNotMixedSource width "and" "or")
      Veir.Passes.InstCombineLLVM.XorNotMixed.xorAndNotOr
      (.llvm .xor) (.llvm .xor) (some width) true
  runBitwiseRule (xorNotMixedSource 8 "or" "and" true)
    Veir.Passes.InstCombineLLVM.XorNotMixed.xorOrNotCommutedAnd
    (.llvm .xor) (.llvm .xor) (some 8) true
  runBitwiseRule (xorNotMixedSource 8 "and" "or" true)
    Veir.Passes.InstCombineLLVM.XorNotMixed.xorAndNotCommutedOr
    (.llvm .xor) (.llvm .xor) (some 8) true
  for width in [8, 32] do
    runBitwiseRule (mulDoubleNegSource width)
      Veir.Passes.InstCombineLLVM.MulDoubleNeg.mulDoubleNeg
      (.llvm .mul) (.llvm .mul) none true
    runBitwiseRule (mulSinkNegSource width)
      Veir.Passes.InstCombineLLVM.MulSinkNeg.mulSinkNeg
      (.llvm .mul) (.llvm .sub) none true
  runNSWRule (mulDoubleNegSource 8 true)
    Veir.Passes.InstCombineLLVM.MulDoubleNeg.mulDoubleNegNSW .mul
  runBitwiseRule (mulSinkNegSource 8 true)
    Veir.Passes.InstCombineLLVM.MulSinkNeg.mulSinkNegCommuted
    (.llvm .mul) (.llvm .sub) none true
  runMulNegConstantCase 8 13
  runMulNegConstantCase 8 (-128)
  runMulNegConstantCase 32 (-123456)
  for width in [8, 32] do
    runBitwiseRule (addSubAllOnesSource width)
      Veir.Passes.InstCombineLLVM.AddSubAllOnes.addSubAllOnes
      (.llvm .add) (.llvm .xor) (some width) true
    runFoldedConstantRule (addSubConstantsSource width)
      Veir.Passes.InstCombineLLVM.AddSubConstants.addSubConstants
      (.llvm .sub) width (-16)
    runBitwiseRule (addOneNotSource width 0)
      Veir.Passes.InstCombineLLVM.AddOneNot.addOneNot
      (.llvm .add) (.llvm .sub) none true
    runBitwiseRule (subAddAllOnesSource width)
      Veir.Passes.InstCombineLLVM.SubAddAllOnes.subAddAllOnes
      (.llvm .sub) (.llvm .add) none true
    runBitwiseRule (notSubSource width)
      Veir.Passes.InstCombineLLVM.NotSub.notSub
      (.llvm .xor) (.llvm .add) (some width) true
    runBitwiseRule (sharedNotXorSource width false)
      Veir.Passes.InstCombineLLVM.NotAndXorOr.notAndXorOr
      (.llvm .xor) (.llvm .or) (some width) true
    runBitwiseRule (sharedNotXorSource width true)
      Veir.Passes.InstCombineLLVM.NotOrXorAnd.notOrXorAnd
      (.llvm .xor) (.llvm .or) (some width) true
    runFoldedConstantRule (subSubConstantsSource width)
      Veir.Passes.InstCombineLLVM.SubSubConstants.subSubConstants
      (.llvm .add) width (-30)
    runBitwiseRule (notNegOrSource width false)
      Veir.Passes.InstCombineLLVM.NotNegOr.notNegOr
      (.llvm .xor) (.llvm .and) (some width) true
    runBitwiseRule (maskedMergeNotSource width)
      Veir.Passes.InstCombineLLVM.MaskedMergeNot.maskedMergeNot
      (.llvm .xor) (.llvm .and) none true
    runFoldedConstantRule (notAddConstantSource width 13)
      Veir.Passes.InstCombineLLVM.NotAddConstant.notAddConstant
      (.llvm .sub) width (-14)
  runBitwiseRule (addOneNotSource 8 1)
    Veir.Passes.InstCombineLLVM.AddOneNot.notAddOne
    (.llvm .add) (.llvm .sub) none true
  runBitwiseRule (addOneNotSource 8 2)
    Veir.Passes.InstCombineLLVM.AddOneNot.addNotOne
    (.llvm .add) (.llvm .sub) none true
  runBitwiseRule (addOneNotSource 8 3)
    Veir.Passes.InstCombineLLVM.AddOneNot.addCommutedNotOne
    (.llvm .add) (.llvm .sub) none true
  runBitwiseRule (sharedNotXorSource 8 false false true)
    Veir.Passes.InstCombineLLVM.NotAndXorOr.notAndXorCommutedOr
    (.llvm .xor) (.llvm .or) (some 8) true
  runBitwiseRule (sharedNotXorSource 8 false true false)
    Veir.Passes.InstCombineLLVM.NotAndXorOr.notCommutedAndXorOr
    (.llvm .xor) (.llvm .or) (some 8) true
  runBitwiseRule (sharedNotXorSource 8 false true true)
    Veir.Passes.InstCombineLLVM.NotAndXorOr.notCommutedAndXorCommutedOr
    (.llvm .xor) (.llvm .or) (some 8) true
  runBitwiseRule (sharedNotXorSource 8 true false true)
    Veir.Passes.InstCombineLLVM.NotOrXorAnd.notCommutedOrXorAnd
    (.llvm .xor) (.llvm .or) (some 8) true
  runBitwiseRule (sharedNotXorSource 8 true true false)
    Veir.Passes.InstCombineLLVM.NotOrXorAnd.notOrXorCommutedAnd
    (.llvm .xor) (.llvm .or) (some 8) true
  runBitwiseRule (sharedNotXorSource 8 true true true)
    Veir.Passes.InstCombineLLVM.NotOrXorAnd.notCommutedOrXorCommutedAnd
    (.llvm .xor) (.llvm .or) (some 8) true
  runBitwiseRule (maskedMergeNotSource 8 false false true)
    Veir.Passes.InstCombineLLVM.MaskedMergeNot.maskedMergeNotDeltaCommuted
    (.llvm .xor) (.llvm .and) none true
  runBitwiseRule (maskedMergeNotSource 8 false true false)
    Veir.Passes.InstCombineLLVM.MaskedMergeNot.maskedMergeNotAndCommuted
    (.llvm .xor) (.llvm .and) none true
  runBitwiseRule (maskedMergeNotSource 8 false true true)
    Veir.Passes.InstCombineLLVM.MaskedMergeNot.maskedMergeNotAndDeltaCommuted
    (.llvm .xor) (.llvm .and) none true
  runBitwiseRule (maskedMergeNotSource 8 true false false)
    Veir.Passes.InstCombineLLVM.MaskedMergeNot.maskedMergeNotRootCommuted
    (.llvm .xor) (.llvm .and) none true
  runBitwiseRule (maskedMergeNotSource 8 true false true)
    Veir.Passes.InstCombineLLVM.MaskedMergeNot.maskedMergeNotRootDeltaCommuted
    (.llvm .xor) (.llvm .and) none true
  runBitwiseRule (maskedMergeNotSource 8 true true false)
    Veir.Passes.InstCombineLLVM.MaskedMergeNot.maskedMergeNotRootAndCommuted
    (.llvm .xor) (.llvm .and) none true
  runBitwiseRule (maskedMergeNotSource 8 true true true)
    Veir.Passes.InstCombineLLVM.MaskedMergeNot.maskedMergeNotAllCommuted
    (.llvm .xor) (.llvm .and) none true
  runBitwiseRule (notNegOrSource 8 true)
    Veir.Passes.InstCombineLLVM.NotNegOr.notOrNeg
    (.llvm .xor) (.llvm .and) (some 8) true


  -- LLVM's m_Not accepts xor V, -1 and xor -1, V. Exercise every newly
  -- exposed constant-left matcher, including independent choices at two NOT nodes.
  runBitwiseRule (source 8 true true)
    Veir.Passes.InstCombineLLVM.NegateNot.negateNotConstantLeft
    (.llvm .sub) (.llvm .add)
  for (andComm, notBLeft, notALeft, rule) in #[
      (false, true, false, Veir.Passes.InstCombineLLVM.XorAndNotNot.xorAndNotNotFirstNotLeft),
      (false, false, true, Veir.Passes.InstCombineLLVM.XorAndNotNot.xorAndNotNotSecondNotLeft),
      (false, true, true, Veir.Passes.InstCombineLLVM.XorAndNotNot.xorAndNotNotBothNotLeft),
      (true, true, false, Veir.Passes.InstCombineLLVM.XorAndNotNot.xorNotAndNotFirstNotLeft),
      (true, false, true, Veir.Passes.InstCombineLLVM.XorAndNotNot.xorNotAndNotSecondNotLeft),
      (true, true, true, Veir.Passes.InstCombineLLVM.XorAndNotNot.xorNotAndNotBothNotLeft)] do
    runBitwiseRule (xorAndNotNotSource 8 andComm notBLeft notALeft) rule
      (.llvm .xor) (.llvm .xor) none true
  for (rootComm, andComm, rule) in #[
      (false, false, Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorNotAndSelfConstantLeft),
      (false, true, Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorCommutedNotAndSelfConstantLeft),
      (true, false, Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorSelfNotAndConstantLeft),
      (true, true, Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorSelfCommutedNotAndConstantLeft)] do
    runBitwiseRule (xorNotAndSelfSource 8 rootComm andComm true) rule
      (.llvm .xor) (.llvm .or)
  for (andComm, rule) in #[
      (false, Veir.Passes.InstCombineLLVM.AndOrNotAnd.andOrNotAndConstantLeft),
      (true, Veir.Passes.InstCombineLLVM.AndOrNotAnd.andOrNotCommutedAndConstantLeft)] do
    runBitwiseRule (andOrNotAndSource 8 andComm true) rule (.llvm .and) (.llvm .xor)
  for (orComm, rule) in #[
      (false, Veir.Passes.InstCombineLLVM.OrAndNotOr.orAndNotOrConstantLeft),
      (true, Veir.Passes.InstCombineLLVM.OrAndNotOr.orAndNotCommutedOrConstantLeft)] do
    runBitwiseRule (orNotOrSource 8 "and" orComm true) rule (.llvm .or) (.llvm .xor) none
  for (orComm, rule) in #[
      (false, Veir.Passes.InstCombineLLVM.OrXorNotOr.orXorNotOrConstantLeft),
      (true, Veir.Passes.InstCombineLLVM.OrXorNotOr.orXorNotCommutedOrConstantLeft)] do
    runBitwiseRule (orNotOrSource 8 "xor" orComm true) rule (.llvm .or) (.llvm .xor) none
  for (c1, c2, nb, na, rule) in #[
      (false, false, true, false, Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orComplementaryMasksNotBLeft),
      (false, false, false, true, Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orComplementaryMasksNotALeft),
      (false, false, true, true, Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orComplementaryMasksBothNotLeft),
      (true, false, true, false, Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orLeftCommutedComplementaryMasksNotBLeft),
      (true, false, false, true, Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orLeftCommutedComplementaryMasksNotALeft),
      (true, false, true, true, Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orLeftCommutedComplementaryMasksBothNotLeft),
      (false, true, true, false, Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orRightCommutedComplementaryMasksNotBLeft),
      (false, true, false, true, Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orRightCommutedComplementaryMasksNotALeft),
      (false, true, true, true, Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orRightCommutedComplementaryMasksBothNotLeft),
      (true, true, true, false, Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orCommutedComplementaryMasksNotBLeft),
      (true, true, false, true, Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orCommutedComplementaryMasksNotALeft),
      (true, true, true, true, Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orCommutedComplementaryMasksBothNotLeft)] do
    runBitwiseRule (orComplementaryMasksSource 8 c1 c2 nb na) rule
      (.llvm .or) (.llvm .xor) none
  for (c1, c2, nb, na, rule) in #[
      (false, false, true, false, Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorComplementaryMasksNotBLeft),
      (false, false, false, true, Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorComplementaryMasksNotALeft),
      (false, false, true, true, Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorComplementaryMasksBothNotLeft),
      (false, true, true, false, Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorLeftCommutedComplementaryMasksNotBLeft),
      (false, true, false, true, Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorLeftCommutedComplementaryMasksNotALeft),
      (false, true, true, true, Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorLeftCommutedComplementaryMasksBothNotLeft),
      (true, false, true, false, Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedComplementaryMasksNotBLeft),
      (true, false, false, true, Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedComplementaryMasksNotALeft),
      (true, false, true, true, Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedComplementaryMasksBothNotLeft),
      (true, true, true, false, Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedCommutedComplementaryMasksNotBLeft),
      (true, true, false, true, Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedCommutedComplementaryMasksNotALeft),
      (true, true, true, true, Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedCommutedComplementaryMasksBothNotLeft)] do
    runBitwiseRule (xorComplementarySource 8 "and" c1 c2 nb na) rule
      (.llvm .xor) (.llvm .xor) none true
  for (c1, c2, nb, na, rule) in #[
      (false, false, true, false, Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorComplementaryOrsNotBLeft),
      (false, false, false, true, Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorComplementaryOrsNotALeft),
      (false, false, true, true, Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorComplementaryOrsBothNotLeft),
      (false, true, true, false, Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorLeftCommutedComplementaryOrsNotBLeft),
      (false, true, false, true, Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorLeftCommutedComplementaryOrsNotALeft),
      (false, true, true, true, Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorLeftCommutedComplementaryOrsBothNotLeft),
      (true, false, true, false, Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedComplementaryOrsNotBLeft),
      (true, false, false, true, Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedComplementaryOrsNotALeft),
      (true, false, true, true, Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedComplementaryOrsBothNotLeft),
      (true, true, true, false, Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedCommutedComplementaryOrsNotBLeft),
      (true, true, false, true, Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedCommutedComplementaryOrsNotALeft),
      (true, true, true, true, Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedCommutedComplementaryOrsBothNotLeft)] do
    runBitwiseRule (xorComplementarySource 8 "or" c1 c2 nb na) rule
      (.llvm .xor) (.llvm .xor) none true
  for (c1, c2, nb, na, rule) in #[
      (false, false, true, false, Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andComplementaryOrsNotBLeft),
      (false, false, false, true, Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andComplementaryOrsNotALeft),
      (false, false, true, true, Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andComplementaryOrsBothNotLeft),
      (true, false, true, false, Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andLeftCommutedComplementaryOrsNotBLeft),
      (true, false, false, true, Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andLeftCommutedComplementaryOrsNotALeft),
      (true, false, true, true, Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andLeftCommutedComplementaryOrsBothNotLeft),
      (false, true, true, false, Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andRightCommutedComplementaryOrsNotBLeft),
      (false, true, false, true, Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andRightCommutedComplementaryOrsNotALeft),
      (false, true, true, true, Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andRightCommutedComplementaryOrsBothNotLeft),
      (true, true, true, false, Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andCommutedComplementaryOrsNotBLeft),
      (true, true, false, true, Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andCommutedComplementaryOrsNotALeft),
      (true, true, true, true, Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andCommutedComplementaryOrsBothNotLeft)] do
    runBitwiseRule (andComplementaryOrsSource 8 c1 c2 nb na) rule
      (.llvm .and) (.llvm .xor) none

  for (comm, innerLeft, rootLeft, rule) in #[
      (false, true, false, Veir.Passes.InstCombineLLVM.NotAndNot.notAndNotFirstNotLeft),
      (false, false, true, Veir.Passes.InstCombineLLVM.NotAndNot.notAndNotSecondNotLeft),
      (false, true, true, Veir.Passes.InstCombineLLVM.NotAndNot.notAndNotBothNotLeft),
      (true, true, false, Veir.Passes.InstCombineLLVM.NotAndNot.notCommutedAndNotFirstNotLeft),
      (true, false, true, Veir.Passes.InstCombineLLVM.NotAndNot.notCommutedAndNotSecondNotLeft),
      (true, true, true, Veir.Passes.InstCombineLLVM.NotAndNot.notCommutedAndNotBothNotLeft)] do
    runBitwiseRule (notInnerNotSource 8 "and" comm innerLeft rootLeft) rule
      (.llvm .xor) (.llvm .or) none true
  for (comm, innerLeft, rootLeft, rule) in #[
      (false, true, false, Veir.Passes.InstCombineLLVM.NotOrNot.notOrNotFirstNotLeft),
      (false, false, true, Veir.Passes.InstCombineLLVM.NotOrNot.notOrNotSecondNotLeft),
      (false, true, true, Veir.Passes.InstCombineLLVM.NotOrNot.notOrNotBothNotLeft),
      (true, true, false, Veir.Passes.InstCombineLLVM.NotOrNot.notCommutedOrNotFirstNotLeft),
      (true, false, true, Veir.Passes.InstCombineLLVM.NotOrNot.notCommutedOrNotSecondNotLeft),
      (true, true, true, Veir.Passes.InstCombineLLVM.NotOrNot.notCommutedOrNotBothNotLeft)] do
    runBitwiseRule (notInnerNotSource 8 "or" comm innerLeft rootLeft) rule
      (.llvm .xor) (.llvm .and) none true
  for (first, second, comm, rule) in #[
      ("or", "and", false, Veir.Passes.InstCombineLLVM.XorNotMixed.xorOrNotAndConstantLeft),
      ("or", "and", true, Veir.Passes.InstCombineLLVM.XorNotMixed.xorOrNotCommutedAndConstantLeft),
      ("and", "or", false, Veir.Passes.InstCombineLLVM.XorNotMixed.xorAndNotOrConstantLeft),
      ("and", "or", true, Veir.Passes.InstCombineLLVM.XorNotMixed.xorAndNotCommutedOrConstantLeft)] do
    runBitwiseRule (xorNotMixedSource 8 first second comm true) rule
      (.llvm .xor) (.llvm .xor) none true
  for (variant, rule) in #[
      (0, Veir.Passes.InstCombineLLVM.AddOneNot.addOneNotConstantLeft),
      (1, Veir.Passes.InstCombineLLVM.AddOneNot.notAddOneConstantLeft),
      (2, Veir.Passes.InstCombineLLVM.AddOneNot.addNotOneConstantLeft),
      (3, Veir.Passes.InstCombineLLVM.AddOneNot.addCommutedNotOneConstantLeft)] do
    runBitwiseRule (addOneNotSource 8 variant true) rule (.llvm .add) (.llvm .sub) none true
  runBitwiseRule (addOneNotSource 1 0)
    Veir.Passes.InstCombineLLVM.AddOneNot.addOneNot
    (.llvm .add) (.llvm .sub) none true
  runBitwiseRule (addSubAllOnesSource 1)
    Veir.Passes.InstCombineLLVM.AddSubAllOnes.addSubAllOnes
    (.llvm .add) (.llvm .add) none true
  runBitwiseRule (allOnesSubSource 1)
    Veir.Passes.InstCombineLLVM.AllOnesSub.allOnesSubToNot
    (.llvm .sub) (.llvm .xor) (some 1)
  runBitwiseRule (subAddAllOnesSource 1)
    Veir.Passes.InstCombineLLVM.SubAddAllOnes.subAddAllOnes
    (.llvm .sub) (.llvm .add)
  runBitwiseRule (notSubSource 1)
    Veir.Passes.InstCombineLLVM.NotSub.notSub
    (.llvm .xor) (.llvm .add) none true
  runBitwiseRule (sharedNotXorSource 1 false)
    Veir.Passes.InstCombineLLVM.NotAndXorOr.notAndXorOr
    (.llvm .xor) (.llvm .or) none true
  runBitwiseRule (sharedNotXorSource 1 true)
    Veir.Passes.InstCombineLLVM.NotOrXorAnd.notOrXorAnd
    (.llvm .xor) (.llvm .or) none true
  runBitwiseRule (notInnerNotSource 1 "and")
    Veir.Passes.InstCombineLLVM.NotAndNot.notAndNot
    (.llvm .xor) (.llvm .or) none true
  runBitwiseRule (notInnerNotSource 1 "or")
    Veir.Passes.InstCombineLLVM.NotOrNot.notOrNot
    (.llvm .xor) (.llvm .and) none true
  runBitwiseRule (maskedMergeNotSource 1)
    Veir.Passes.InstCombineLLVM.MaskedMergeNot.maskedMergeNot
    (.llvm .xor) (.llvm .xor) none true
  runBitwiseRule (source 1 true)
    Veir.Passes.InstCombineLLVM.NegateNot.negateNot
    (.llvm .sub) (.llvm .add)
  runFoldedConstantRule (notAddConstantSource 1 1)
    Veir.Passes.InstCombineLLVM.NotAddConstant.notAddConstant
    (.llvm .sub) 1 0
  runBitwiseRule (notNegOrSource 1 false)
    Veir.Passes.InstCombineLLVM.NotNegOr.notNegOr
    (.llvm .xor) (.llvm .and) none true
  for (orFirst, andComm, orComm, rule) in #[
      (false, false, false, Veir.Passes.InstCombineLLVM.NotAndXorOr.notAndXorOrConstantLeft),
      (false, false, true, Veir.Passes.InstCombineLLVM.NotAndXorOr.notAndXorCommutedOrConstantLeft),
      (false, true, false, Veir.Passes.InstCombineLLVM.NotAndXorOr.notCommutedAndXorOrConstantLeft),
      (false, true, true, Veir.Passes.InstCombineLLVM.NotAndXorOr.notCommutedAndXorCommutedOrConstantLeft),
      (true, false, false, Veir.Passes.InstCombineLLVM.NotOrXorAnd.notOrXorAndConstantLeft),
      (true, false, true, Veir.Passes.InstCombineLLVM.NotOrXorAnd.notCommutedOrXorAndConstantLeft),
      (true, true, false, Veir.Passes.InstCombineLLVM.NotOrXorAnd.notOrXorCommutedAndConstantLeft),
      (true, true, true, Veir.Passes.InstCombineLLVM.NotOrXorAnd.notCommutedOrXorCommutedAndConstantLeft)] do
    runBitwiseRule (sharedNotXorSource 8 orFirst andComm orComm true) rule
      (.llvm .xor) (.llvm .or) none true
  for (rootComm, andComm, deltaComm, rule) in #[
      (false, false, false, Veir.Passes.InstCombineLLVM.MaskedMergeNot.maskedMergeNotNotLeft),
      (false, false, true, Veir.Passes.InstCombineLLVM.MaskedMergeNot.maskedMergeNotDeltaCommutedNotLeft),
      (false, true, false, Veir.Passes.InstCombineLLVM.MaskedMergeNot.maskedMergeNotAndCommutedNotLeft),
      (false, true, true, Veir.Passes.InstCombineLLVM.MaskedMergeNot.maskedMergeNotAndDeltaCommutedNotLeft),
      (true, false, false, Veir.Passes.InstCombineLLVM.MaskedMergeNot.maskedMergeNotRootCommutedNotLeft),
      (true, false, true, Veir.Passes.InstCombineLLVM.MaskedMergeNot.maskedMergeNotRootDeltaCommutedNotLeft),
      (true, true, false, Veir.Passes.InstCombineLLVM.MaskedMergeNot.maskedMergeNotRootAndCommutedNotLeft),
      (true, true, true, Veir.Passes.InstCombineLLVM.MaskedMergeNot.maskedMergeNotAllCommutedNotLeft)] do
    runBitwiseRule (maskedMergeNotSource 8 rootComm andComm deltaComm true) rule
      (.llvm .xor) (.llvm .and) none true
  for (comm, rule) in #[
      (false, Veir.Passes.InstCombineLLVM.NotNegOr.notNegOrConstantLeft),
      (true, Veir.Passes.InstCombineLLVM.NotNegOr.notOrNegConstantLeft)] do
    runBitwiseRule (notNegOrSource 8 comm true) rule (.llvm .xor) (.llvm .and) none true
  runBitwiseRule (notSubSource 8 true)
    Veir.Passes.InstCombineLLVM.NotSub.notSubConstantLeft
    (.llvm .xor) (.llvm .add) none true
  runFoldedConstantRule (notAddConstantSource 8 13 true)
    Veir.Passes.InstCombineLLVM.NotAddConstant.notAddConstantConstantLeft
    (.llvm .sub) 8 (-14)
  runBitwiseRule (negatePoisonSource 8)
    Veir.Passes.InstCombineLLVM.NegatePoison.negatePoison
    (.llvm .sub) (.llvm .mlir__poison)
  for (opcodeName, opcode, rule) in #[
      ("add", Llvm.add,
        Veir.Passes.InstCombineLLVM.DropWrapFlagsUnusedHigh.dropAddWrapFlags),
      ("sub", Llvm.sub,
        Veir.Passes.InstCombineLLVM.DropWrapFlagsUnusedHigh.dropSubWrapFlags),
      ("mul", Llvm.mul,
        Veir.Passes.InstCombineLLVM.DropWrapFlagsUnusedHigh.dropMulWrapFlags)] do
    runDropWrapFlagsRule (dropWrapFlagsSource 8 opcodeName) rule opcode
  runDropWrapFlagsNoMatch (dropWrapFlagsSource 8 "add" false)
    Veir.Passes.InstCombineLLVM.DropWrapFlagsUnusedHigh.dropAddWrapFlags Llvm.add

  -- Parsed signless i1 stores all ones as +1. These cases ensure the normalized
  -- matcher fires on that representation, as well as on ordinary i8 constants.
  for (innerLeft, outerLeft, rule) in #[
      (false, false, Veir.Passes.InstCombineLLVM.FreeInvertDoubleNot.doubleNot),
      (true, false, Veir.Passes.InstCombineLLVM.FreeInvertDoubleNot.doubleNotInnerLeft),
      (false, true, Veir.Passes.InstCombineLLVM.FreeInvertDoubleNot.doubleNotOuterLeft),
      (true, true, Veir.Passes.InstCombineLLVM.FreeInvertDoubleNot.doubleNotBothLeft)] do
    runBitwiseRule (freeInvertDoubleNotSource 1 innerLeft outerLeft) rule
      (.llvm .xor) (.llvm .mlir__constant) none true
  for (outerLeft, rule) in #[
      (false, Veir.Passes.InstCombineLLVM.FreeInvertConstant.invertIntegerConstant),
      (true, Veir.Passes.InstCombineLLVM.FreeInvertConstant.invertIntegerConstantNotLeft)] do
    runFoldedConstantRule (freeInvertConstantSource 1 outerLeft false) rule
      (.llvm .mlir__constant) 1 0
  for (outerLeft, rule) in #[
      (false, Veir.Passes.InstCombineLLVM.FreeInvertConstant.invertPoison),
      (true, Veir.Passes.InstCombineLLVM.FreeInvertConstant.invertPoisonNotLeft)] do
    runBitwiseRule (freeInvertConstantSource 1 outerLeft true) rule
      (.llvm .xor) (.llvm .mlir__poison)
  for (invertLeft, innerLeft, outerLeft, rule) in #[
      (false, false, false, Veir.Passes.InstCombineLLVM.FreeInvertAdd.invertAddRight),
      (false, true, false, Veir.Passes.InstCombineLLVM.FreeInvertAdd.invertAddRightInnerLeft),
      (false, false, true, Veir.Passes.InstCombineLLVM.FreeInvertAdd.invertAddRightOuterLeft),
      (false, true, true, Veir.Passes.InstCombineLLVM.FreeInvertAdd.invertAddRightBothLeft),
      (true, false, false, Veir.Passes.InstCombineLLVM.FreeInvertAdd.invertAddLeft),
      (true, true, false, Veir.Passes.InstCombineLLVM.FreeInvertAdd.invertAddLeftInnerLeft),
      (true, false, true, Veir.Passes.InstCombineLLVM.FreeInvertAdd.invertAddLeftOuterLeft),
      (true, true, true, Veir.Passes.InstCombineLLVM.FreeInvertAdd.invertAddLeftBothLeft)] do
    runBitwiseRule (freeInvertBinarySource 8 "add" invertLeft innerLeft outerLeft) rule
      (.llvm .xor) (.llvm .sub) none true
  for (invertLeft, innerLeft, outerLeft, rule) in #[
      (false, false, false, Veir.Passes.InstCombineLLVM.FreeInvertXor.invertXorRight),
      (false, true, false, Veir.Passes.InstCombineLLVM.FreeInvertXor.invertXorRightInnerLeft),
      (false, false, true, Veir.Passes.InstCombineLLVM.FreeInvertXor.invertXorRightOuterLeft),
      (false, true, true, Veir.Passes.InstCombineLLVM.FreeInvertXor.invertXorRightBothLeft),
      (true, false, false, Veir.Passes.InstCombineLLVM.FreeInvertXor.invertXorLeft),
      (true, true, false, Veir.Passes.InstCombineLLVM.FreeInvertXor.invertXorLeftInnerLeft),
      (true, false, true, Veir.Passes.InstCombineLLVM.FreeInvertXor.invertXorLeftOuterLeft),
      (true, true, true, Veir.Passes.InstCombineLLVM.FreeInvertXor.invertXorLeftBothLeft)] do
    runBitwiseRule (freeInvertBinarySource 8 "xor" invertLeft innerLeft outerLeft) rule
      (.llvm .xor) (.llvm .xor) none true
  for (innerLeft, outerLeft, subRule, ashrRule) in #[
      (false, false, Veir.Passes.InstCombineLLVM.FreeInvertSub.invertSub,
        Veir.Passes.InstCombineLLVM.FreeInvertAShr.invertAShr),
      (true, false, Veir.Passes.InstCombineLLVM.FreeInvertSub.invertSubInnerLeft,
        Veir.Passes.InstCombineLLVM.FreeInvertAShr.invertAShrInnerLeft),
      (false, true, Veir.Passes.InstCombineLLVM.FreeInvertSub.invertSubOuterLeft,
        Veir.Passes.InstCombineLLVM.FreeInvertAShr.invertAShrOuterLeft),
      (true, true, Veir.Passes.InstCombineLLVM.FreeInvertSub.invertSubBothLeft,
        Veir.Passes.InstCombineLLVM.FreeInvertAShr.invertAShrBothLeft)] do
    runBitwiseRule (freeInvertBinarySource 8 "sub" true innerLeft outerLeft) subRule
      (.llvm .xor) (.llvm .add) none true
    runBitwiseRule (freeInvertBinarySource 8 "ashr" true innerLeft outerLeft true) ashrRule
      (.llvm .xor) (.llvm .ashr) none true
  for (opcode, replacement, xLeft, yLeft, outerLeft, rule) in #[
      ("or", OpCode.llvm .and, false, false, false, Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan.invertOr),
      ("or", OpCode.llvm .and, true, false, false, Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan.invertOrXLeft),
      ("or", OpCode.llvm .and, false, true, false, Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan.invertOrYLeft),
      ("or", OpCode.llvm .and, true, true, false, Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan.invertOrBothInnerLeft),
      ("or", OpCode.llvm .and, false, false, true, Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan.invertOrOuterLeft),
      ("or", OpCode.llvm .and, true, false, true, Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan.invertOrXOuterLeft),
      ("or", OpCode.llvm .and, false, true, true, Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan.invertOrYOuterLeft),
      ("or", OpCode.llvm .and, true, true, true, Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan.invertOrAllLeft),
      ("and", OpCode.llvm .or, false, false, false, Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan.invertAnd),
      ("and", OpCode.llvm .or, true, false, false, Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan.invertAndXLeft),
      ("and", OpCode.llvm .or, false, true, false, Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan.invertAndYLeft),
      ("and", OpCode.llvm .or, true, true, false, Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan.invertAndBothInnerLeft),
      ("and", OpCode.llvm .or, false, false, true, Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan.invertAndOuterLeft),
      ("and", OpCode.llvm .or, true, false, true, Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan.invertAndXOuterLeft),
      ("and", OpCode.llvm .or, false, true, true, Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan.invertAndYOuterLeft),
      ("and", OpCode.llvm .or, true, true, true, Veir.Passes.InstCombineLLVM.FreeInvertDeMorgan.invertAndAllLeft)] do
    runBitwiseRule (freeInvertDeMorganSource 8 opcode xLeft yLeft outerLeft) rule
      (.llvm .xor) replacement none true

#guard regression = .ok ()
