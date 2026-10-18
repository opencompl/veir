import Veir.Input
import Veir.Verifier
import Veir.PatternRewriter.Puddle.Execution
import Veir.Passes.InstCombineLLVM.ComposeZExt
import Veir.Passes.InstCombineLLVM.ComposeBitcastScalar
import Veir.Passes.InstCombineLLVM.FreeInvertCasts
import Veir.Passes.InstCombineLLVM.CountBitReverse
import Veir.Passes.InstCombineLLVM.CtpopReorder
import Veir.Passes.InstCombineLLVM.ZExtNNegI1
import Veir.Passes.InstCombineLLVM.ZExtTruncLowMaskSrcLt
import Veir.Passes.InstCombineLLVM.ZExtTruncLowMaskSrcEq
import Veir.Passes.InstCombineLLVM.ZExtTruncLowMaskSrcGt
import Veir.Passes.InstCombineLLVM.ZExtAndTruncMask
import Veir.Passes.InstCombineLLVM.ZExtXorAndTruncMask
import Veir.Passes.InstCombineLLVM.ZExtNegTruncLowMask
import Veir.Passes.InstCombineLLVM.TopShiftTruncToICmp
import Veir.Passes.InstCombineLLVM.LShrTruncToBitTest
import Veir.Passes.InstCombineLLVM.OrLShrTruncToBitTest
import Veir.Passes.InstCombineLLVM.OddShlTruncToICmp
import Veir.Passes.InstCombineLLVM.FlaggedXorTruncToICmp
import Veir.Passes.InstCombineLLVM.UsubSatTruncToICmp

open Veir Veir.Input Veir.Puddle Veir.Data

private def source := r#""builtin.module"() ({
  "func.func"() <{function_type = (i5) -> (), sym_name = "f"}> ({
  ^entry(%x : i5):
  %middle = "llvm.zext"(%x) <{nonNeg}> : (i5) -> i12
  %root = "llvm.zext"(%middle) <{nonNeg}> : (i12) -> i23
  "test.test"(%root) : (i23) -> ()
  "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#

private def hasDirectComposeZExt (ctx : IRContext OpCode) : Bool := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = (OpCode.llvm .zext) &&
          op.getOperandTypes! ctx = #[(IntegerType.signless 5 : TypeAttr)] &&
          op.getResultTypes ctx h = #[(IntegerType.signless 23 : TypeAttr)] then
        return true
  return false

private def regression : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString source.toUTF8
  let some rewritten := RewritePattern.applyInContext
      (Pattern.compile
        Veir.Passes.InstCombineLLVM.ComposeZExt.composeZExt).run ctx
    | throw "zext-pair rewrite did not fire"
  if !hasDirectComposeZExt rewritten.raw then
    throw "rewrite did not create the direct i5-to-i23 zext"
  rewritten.verify moduleOp

private def castPairSource (srcTy innerOp middleTy outerOp dstTy : String) : String :=
  "\"builtin.module\"() ({\n" ++
  "  \"func.func\"() <{function_type = (" ++ srcTy ++ ") -> (), sym_name = \"f\"}> ({\n" ++
  "  ^entry(%x : " ++ srcTy ++ "):\n" ++
  "    %middle = \"llvm." ++ innerOp ++ "\"(%x) : (" ++ srcTy ++ ") -> " ++ middleTy ++ "\n" ++
  "    %root = \"llvm." ++ outerOp ++ "\"(%middle) : (" ++ middleTy ++ ") -> " ++ dstTy ++ "\n" ++
  "    \"test.test\"(%root) : (" ++ dstTy ++ ") -> ()\n" ++
  "    \"func.return\"() : () -> ()\n" ++
  "  }) : () -> ()\n}) : () -> ()"

private def testConsumesDirectCastOfBlockArgument (ctx : IRContext OpCode)
    (opcode : OpCode) : Bool := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = (.test .test) then
        match op.getOperand! ctx 0 with
        | .opResult result =>
            if result.op.getOpType! ctx = opcode then
              match result.op.getOperand! ctx 0 with
              | .blockArgument _ => return true
              | .opResult _ => pure ()
        | .blockArgument _ => pure ()
  return false

private def runCastPair (name source : String) (rule : Pattern OpCode)
    (replacement : OpCode) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString source.toUTF8
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw s!"{name} rewrite did not fire"
  if !testConsumesDirectCastOfBlockArgument rewritten.raw replacement then
    throw s!"{name} did not replace the two-cast chain with a direct cast"
  rewritten.verify moduleOp

private def composeCastRegression : Except String Unit := do
  runCastPair "cast-L243-zext-zext" (castPairSource "i5" "zext" "i12" "zext" "i23")
    Veir.Passes.InstCombineLLVM.ComposeZExt.composeZExt (.llvm .zext)
  runCastPair "cast-L243-trunc-trunc" (castPairSource "i23" "trunc" "i12" "trunc" "i5")
    Veir.Passes.InstCombineLLVM.ComposeZExt.composeTrunc (.llvm .trunc)
  runCastPair "cast-L243-sext-sext" (castPairSource "i5" "sext" "i12" "sext" "i23")
    Veir.Passes.InstCombineLLVM.ComposeZExt.composeSExt (.llvm .sext)
  runCastPair "cast-L243-zext-sext" (castPairSource "i5" "zext" "i12" "sext" "i23")
    Veir.Passes.InstCombineLLVM.ComposeZExt.composeZExtSExt (.llvm .zext)
  runCastPair "cast-L243-zext-trunc-zext"
    (castPairSource "i5" "zext" "i23" "trunc" "i12")
    Veir.Passes.InstCombineLLVM.ComposeZExt.composeZExtTruncToZExt (.llvm .zext)
  runCastPair "cast-L243-zext-trunc-trunc"
    (castPairSource "i12" "zext" "i23" "trunc" "i5")
    Veir.Passes.InstCombineLLVM.ComposeZExt.composeZExtTruncToTrunc (.llvm .trunc)
  runCastPair "cast-L243-zext-trunc-bitcast"
    (castPairSource "i12" "zext" "i23" "trunc" "i12")
    Veir.Passes.InstCombineLLVM.ComposeZExt.composeZExtTruncToBitcast (.llvm .bitcast)
  runCastPair "cast-L243-sext-trunc-sext"
    (castPairSource "i5" "sext" "i23" "trunc" "i12")
    Veir.Passes.InstCombineLLVM.ComposeZExt.composeSExtTruncToSExt (.llvm .sext)
  runCastPair "cast-L243-sext-trunc-trunc"
    (castPairSource "i12" "sext" "i23" "trunc" "i5")
    Veir.Passes.InstCombineLLVM.ComposeZExt.composeSExtTruncToTrunc (.llvm .trunc)
  runCastPair "cast-L243-sext-trunc-bitcast"
    (castPairSource "i12" "sext" "i23" "trunc" "i12")
    Veir.Passes.InstCombineLLVM.ComposeZExt.composeSExtTruncToBitcast (.llvm .bitcast)
  runCastPair "cast-L243-trunc-bitcast"
    (castPairSource "i23" "trunc" "i12" "bitcast" "i12")
    Veir.Passes.InstCombineLLVM.ComposeZExt.composeTruncBitcast (.llvm .trunc)
  runCastPair "cast-L243-zext-bitcast"
    (castPairSource "i5" "zext" "i12" "bitcast" "i12")
    Veir.Passes.InstCombineLLVM.ComposeZExt.composeZExtBitcast (.llvm .zext)
  runCastPair "cast-L243-sext-bitcast"
    (castPairSource "i5" "sext" "i12" "bitcast" "i12")
    Veir.Passes.InstCombineLLVM.ComposeZExt.composeSExtBitcast (.llvm .sext)
  runCastPair "cast-L243-bitcast-trunc"
    (castPairSource "i23" "bitcast" "i23" "trunc" "i5")
    Veir.Passes.InstCombineLLVM.ComposeZExt.composeBitcastTrunc (.llvm .trunc)
  runCastPair "cast-L243-bitcast-zext"
    (castPairSource "i5" "bitcast" "i5" "zext" "i12")
    Veir.Passes.InstCombineLLVM.ComposeZExt.composeBitcastZExt (.llvm .zext)
  runCastPair "cast-L243-bitcast-sext"
    (castPairSource "i5" "bitcast" "i5" "sext" "i12")
    Veir.Passes.InstCombineLLVM.ComposeZExt.composeBitcastSExt (.llvm .sext)
  runCastPair "cast-L243-bitcast-bitcast"
    (castPairSource "i12" "bitcast" "i12" "bitcast" "i12")
    Veir.Passes.InstCombineLLVM.ComposeZExt.composeBitcastBitcast (.llvm .bitcast)
  runCastPair "cast-L243-bitcast-IIB"
    (castPairSource "i64" "bitcast" "i64" "bitcast" "!llvm.byte<64>")
    Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastIIB (.llvm .bitcast)
  runCastPair "cast-L243-bitcast-IBI"
    (castPairSource "i64" "bitcast" "!llvm.byte<64>" "bitcast" "i64")
    Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastIBI (.llvm .bitcast)
  runCastPair "cast-L243-bitcast-IBB"
    (castPairSource "i64" "bitcast" "!llvm.byte<64>" "bitcast" "!llvm.byte<64>")
    Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastIBB (.llvm .bitcast)
  runCastPair "cast-L243-bitcast-BII"
    (castPairSource "!llvm.byte<64>" "bitcast" "i64" "bitcast" "i64")
    Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastBII (.llvm .bitcast)
  runCastPair "cast-L243-bitcast-BIB"
    (castPairSource "!llvm.byte<64>" "bitcast" "i64" "bitcast" "!llvm.byte<64>")
    Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastBIB (.llvm .bitcast)
  runCastPair "cast-L243-bitcast-BBI"
    (castPairSource "!llvm.byte<64>" "bitcast" "!llvm.byte<64>" "bitcast" "i64")
    Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastBBI (.llvm .bitcast)
  runCastPair "cast-L243-bitcast-BBB"
    (castPairSource "!llvm.byte<64>" "bitcast" "!llvm.byte<64>" "bitcast" "!llvm.byte<64>")
    Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastBBB (.llvm .bitcast)
  runCastPair "cast-L243-bitcast-PPP"
    (castPairSource "!llvm.ptr" "bitcast" "!llvm.ptr" "bitcast" "!llvm.ptr")
    Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastPPP (.llvm .bitcast)
  runCastPair "cast-L243-bitcast-PPB"
    (castPairSource "!llvm.ptr" "bitcast" "!llvm.ptr" "bitcast" "!llvm.byte<64>")
    Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastPPB (.llvm .bitcast)
  runCastPair "cast-L243-bitcast-PBB"
    (castPairSource "!llvm.ptr" "bitcast" "!llvm.byte<64>" "bitcast" "!llvm.byte<64>")
    Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastPBB (.llvm .bitcast)
  runCastPair "cast-L243-bitcast-PBI"
    (castPairSource "!llvm.ptr" "bitcast" "!llvm.byte<64>" "bitcast" "i64")
    Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastPBI (.llvm .ptrtoint)

private def intrinsicSource (root : String) (zeroPoison : Bool := false) : String :=
  "\"builtin.module\"() ({\n  \"func.func\"() <{function_type = (i32) -> (), sym_name = \"f\"}> ({" ++
    "\n  ^entry(%x : i32):" ++
    "\n  %reversed = \"llvm.intr.bitreverse\"(%x) : (i32) -> i32" ++
    "\n  %root = \"llvm.intr." ++ root ++ "\"(%reversed)" ++
    (if root = "ctpop" then "" else if zeroPoison then
      " <{is_zero_poison = 1 : i1}>" else " <{is_zero_poison = 0 : i1}>") ++
    " : (i32) -> i32\n  \"test.test\"(%root) : (i32) -> ()" ++
    "\n  \"func.return\"() : () -> ()\n  }) : () -> ()\n}) : () -> ()"

private def hasOp (ctx : IRContext OpCode) (opcode : OpCode) : Bool := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = opcode then return true
  return false

private def countOp (ctx : IRContext OpCode) (opcode : OpCode) : Nat := Id.run do
  let mut count := 0
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = opcode then count := count + 1
  return count

private def runIntrinsic (root : String) (rule : Pattern OpCode)
    (source replacement : OpCode) (zeroPoison : Bool := false) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString (intrinsicSource root zeroPoison).toUTF8
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw s!"{root} rewrite did not fire"
  if source = replacement then
    if countOp rewritten.raw replacement != 1 then
      throw s!"{root} rewrite did not leave exactly one replacement"
  else if hasOp rewritten.raw source then throw s!"matched {root} root was not erased"
  if !hasOp rewritten.raw replacement then throw s!"{root} replacement was not created"
  rewritten.verify moduleOp

private def testConsumesCtpopOfBlockArgument (ctx : IRContext OpCode) : Bool := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = (.test .test) then
        match op.getOperand! ctx 0 with
        | .opResult result =>
            if result.op.getOpType! ctx = (.llvm .intr__ctpop) then
              match result.op.getOperand! ctx 0 with
              | .blockArgument _ => return true
              | .opResult _ => pure ()
        | .blockArgument _ => pure ()
  return false

private def ctpopUnarySource (opcode ty : String) : String :=
  "\"builtin.module\"() ({\n" ++
  "  \"func.func\"() <{function_type = (" ++ ty ++ ") -> (), sym_name = \"f\"}> ({\n" ++
  "  ^entry(%x : " ++ ty ++ "):\n" ++
  "    %reordered = \"llvm.intr." ++ opcode ++ "\"(%x) : (" ++ ty ++ ") -> " ++ ty ++ "\n" ++
  "    %root = \"llvm.intr.ctpop\"(%reordered) : (" ++ ty ++ ") -> " ++ ty ++ "\n" ++
  "    \"test.test\"(%root) : (" ++ ty ++ ") -> ()\n" ++
  "    \"func.return\"() : () -> ()\n" ++
  "  }) : () -> ()\n}) : () -> ()"

private def ctpopFunnelSource (opcode : String) : String :=
  "\"builtin.module\"() ({\n" ++
  "  \"func.func\"() <{function_type = (i23, i23) -> (), sym_name = \"f\"}> ({\n" ++
  "  ^entry(%x : i23, %amount : i23):\n" ++
  "    %reordered = \"llvm.intr." ++ opcode ++
    "\"(%x, %x, %amount) : (i23, i23, i23) -> i23\n" ++
  "    %root = \"llvm.intr.ctpop\"(%reordered) : (i23) -> i23\n" ++
  "    \"test.test\"(%root) : (i23) -> ()\n" ++
  "    \"func.return\"() : () -> ()\n" ++
  "  }) : () -> ()\n}) : () -> ()"

private def runCtpopReorder (name source : String) (rule : Pattern OpCode) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString source.toUTF8
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw s!"{name} rewrite did not fire"
  if !testConsumesCtpopOfBlockArgument rewritten.raw then
    throw s!"{name} did not replace ctpop(reorder(x)) with ctpop(x)"
  rewritten.verify moduleOp

private def intrinsicRegression : Except String Unit := do
  runIntrinsic "ctlz"
    Veir.Passes.InstCombineLLVM.CountBitReverse.ctlzBitReverse
    (.llvm .intr__ctlz) (.llvm .intr__cttz)
  runIntrinsic "cttz"
    Veir.Passes.InstCombineLLVM.CountBitReverse.cttzBitReverse
    (.llvm .intr__cttz) (.llvm .intr__ctlz)
  runIntrinsic "ctpop"
    Veir.Passes.InstCombineLLVM.CtpopReorder.ctpopBitReverse
    (.llvm .intr__ctpop) (.llvm .intr__ctpop)
  runIntrinsic "ctlz"
    Veir.Passes.InstCombineLLVM.CountBitReverse.ctlzBitReverseZeroPoison
    (.llvm .intr__ctlz) (.llvm .intr__cttz) true
  runIntrinsic "cttz"
    Veir.Passes.InstCombineLLVM.CountBitReverse.cttzBitReverseZeroPoison
    (.llvm .intr__cttz) (.llvm .intr__ctlz) true
  runCtpopReorder "ctpop-bitreverse" (ctpopUnarySource "bitreverse" "i23")
    Veir.Passes.InstCombineLLVM.CtpopReorder.ctpopBitReverse
  runCtpopReorder "ctpop-bswap" (ctpopUnarySource "bswap" "i32")
    Veir.Passes.InstCombineLLVM.CtpopReorder.ctpopBSwap
  runCtpopReorder "ctpop-fshl" (ctpopFunnelSource "fshl")
    Veir.Passes.InstCombineLLVM.CtpopReorder.ctpopFShl
  runCtpopReorder "ctpop-fshr" (ctpopFunnelSource "fshr")
    Veir.Passes.InstCombineLLVM.CtpopReorder.ctpopFShr

private def nnegSource := r#""builtin.module"() ({
  "func.func"() <{function_type = (i1) -> (), sym_name = "f"}> ({
  ^entry(%x : i1):
  %root = "llvm.zext"(%x) <{nonNeg}> : (i1) -> i9
  "test.test"(%root) : (i9) -> ()
  "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#

private def nnegRegression : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString nnegSource.toUTF8
  let some rewritten := RewritePattern.applyInContext (Pattern.compile
      Veir.Passes.InstCombineLLVM.ZExtNNegI1.zextNNegI1ToZero).run ctx
    | throw "nneg i1 zext rewrite did not fire"
  if hasOp rewritten.raw (.llvm .zext) then throw "matched nneg zext root was not erased"
  rewritten.verify moduleOp

private def castFunction (argTy body : String) : String :=
  "\"builtin.module\"() ({\n" ++
  "  \"func.func\"() <{function_type = (" ++ argTy ++ ") -> (), sym_name = \"f\"}> ({\n" ++
  "  ^entry(%x : " ++ argTy ++ "):\n" ++ body ++
  "    \"func.return\"() : () -> ()\n" ++
  "  }) : () -> ()\n}) : () -> ()"

private def hasOpWithResultType (ctx : IRContext OpCode) (opcode : OpCode)
    (resultType : TypeAttr) : Bool := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = opcode && op.getResultTypes ctx h == #[resultType] then
        return true
  return false

private def runCastRule (name source : String) (rule : Pattern OpCode)
    (replacement : OpCode) (replacementType : TypeAttr) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString source.toUTF8
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw s!"{name} rewrite did not fire"
  if !hasOpWithResultType rewritten.raw replacement replacementType then
    throw s!"{name} rewrite did not create the expected replacement"
  rewritten.verify moduleOp

private def lowMaskRegression : Except String Unit := do
  runCastRule "cast-L1717" (castFunction "i7"
    "    %trunc = \"llvm.trunc\"(%x) : (i7) -> i3\n    %root = \"llvm.zext\"(%trunc) : (i3) -> i11\n    \"test.test\"(%root) : (i11) -> ()\n")
    Veir.Passes.InstCombineLLVM.ZExtTruncLowMaskSrcLt.zextTruncLowMaskSrcLt
    (.llvm .and) (IntegerType.signless 7)
  runCastRule "cast-L1722" (castFunction "i13"
    "    %trunc = \"llvm.trunc\"(%x) : (i13) -> i5\n    %root = \"llvm.zext\"(%trunc) : (i5) -> i13\n    \"test.test\"(%root) : (i13) -> ()\n")
    Veir.Passes.InstCombineLLVM.ZExtTruncLowMaskSrcEq.zextTruncLowMaskSrcEq
    (.llvm .and) (IntegerType.signless 13)
  runCastRule "cast-L1728" (castFunction "i17"
    "    %trunc = \"llvm.trunc\"(%x) : (i17) -> i4\n    %root = \"llvm.zext\"(%trunc) : (i4) -> i9\n    \"test.test\"(%root) : (i9) -> ()\n")
    Veir.Passes.InstCombineLLVM.ZExtTruncLowMaskSrcGt.zextTruncLowMaskSrcGt
    (.llvm .and) (IntegerType.signless 9)
  runCastRule "cast-L1763" (castFunction "i19"
    "    %trunc = \"llvm.trunc\"(%x) : (i19) -> i6\n    %c = \"llvm.mlir.constant\"() <{value = 42 : i6}> : () -> i6\n    %and = \"llvm.and\"(%trunc, %c) : (i6, i6) -> i6\n    %root = \"llvm.zext\"(%and) : (i6) -> i19\n    \"test.test\"(%root) : (i19) -> ()\n")
    Veir.Passes.InstCombineLLVM.ZExtAndTruncMask.zextAndTruncMask
    (.llvm .and) (IntegerType.signless 19)
  runCastRule "cast-L1745" (castFunction "i19"
    "    %trunc = \"llvm.trunc\"(%x) : (i19) -> i6\n    %c = \"llvm.mlir.constant\"() <{value = 42 : i6}> : () -> i6\n    %and = \"llvm.and\"(%trunc, %c) : (i6, i6) -> i6\n    %xor = \"llvm.xor\"(%and, %c) : (i6, i6) -> i6\n    %root = \"llvm.zext\"(%xor) : (i6) -> i19\n    \"test.test\"(%root) : (i19) -> ()\n")
    Veir.Passes.InstCombineLLVM.ZExtXorAndTruncMask.zextXorAndTruncMask
    (.llvm .xor) (IntegerType.signless 19)
  runCastRule "cast-L1753" (castFunction "i19"
    "    %trunc = \"llvm.trunc\"(%x) : (i19) -> i6\n    %zero = \"llvm.mlir.constant\"() <{value = 0 : i6}> : () -> i6\n    %neg = \"llvm.sub\"(%zero, %trunc) : (i6, i6) -> i6\n    %root = \"llvm.zext\"(%neg) : (i6) -> i19\n    \"test.test\"(%root) : (i19) -> ()\n")
    Veir.Passes.InstCombineLLVM.ZExtNegTruncLowMask.zextNegTruncLowMask
    (.llvm .and) (IntegerType.signless 19)

private def shiftTruncRegression : Except String Unit := do
  runCastRule "cast-L1136-lshr" (castFunction "i8"
    "    %amount = \"llvm.mlir.constant\"() <{value = 7 : i8}> : () -> i8\n    %shifted = \"llvm.lshr\"(%x, %amount) : (i8, i8) -> i8\n    %root = \"llvm.trunc\"(%shifted) : (i8) -> i1\n    \"test.test\"(%root) : (i1) -> ()\n")
    Veir.Passes.InstCombineLLVM.TopShiftTruncToICmp.truncLShrTopToICmpSlt
    (.llvm .icmp) (IntegerType.signless 1)
  runCastRule "cast-L1136-ashr" (castFunction "i8"
    "    %amount = \"llvm.mlir.constant\"() <{value = 7 : i8}> : () -> i8\n    %shifted = \"llvm.ashr\"(%x, %amount) : (i8, i8) -> i8\n    %root = \"llvm.trunc\"(%shifted) : (i8) -> i1\n    \"test.test\"(%root) : (i1) -> ()\n")
    Veir.Passes.InstCombineLLVM.TopShiftTruncToICmp.truncAShrTopToICmpSlt
    (.llvm .icmp) (IntegerType.signless 1)
  runCastRule "cast-L1145" (castFunction "i8"
    "    %amount = \"llvm.mlir.constant\"() <{value = 3 : i8}> : () -> i8\n    %shifted = \"llvm.lshr\"(%x, %amount) : (i8, i8) -> i8\n    %root = \"llvm.trunc\"(%shifted) : (i8) -> i1\n    \"test.test\"(%root) : (i1) -> ()\n")
    Veir.Passes.InstCombineLLVM.LShrTruncToBitTest.lshrTruncToBitTest
    (.llvm .icmp) (IntegerType.signless 1)
  runCastRule "cast-L1153" (castFunction "i8"
    "    %amount = \"llvm.mlir.constant\"() <{value = 3 : i8}> : () -> i8\n    %shifted = \"llvm.lshr\"(%x, %amount) : (i8, i8) -> i8\n    %joined = \"llvm.or\"(%shifted, %x) : (i8, i8) -> i8\n    %root = \"llvm.trunc\"(%joined) : (i8) -> i1\n    \"test.test\"(%root) : (i1) -> ()\n")
    Veir.Passes.InstCombineLLVM.OrLShrTruncToBitTest.orLShrTruncToBitTest
    (.llvm .icmp) (IntegerType.signless 1)
  runCastRule "cast-L1153-commuted" (castFunction "i8"
    "    %amount = \"llvm.mlir.constant\"() <{value = 3 : i8}> : () -> i8\n    %shifted = \"llvm.lshr\"(%x, %amount) : (i8, i8) -> i8\n    %joined = \"llvm.or\"(%x, %shifted) : (i8, i8) -> i8\n    %root = \"llvm.trunc\"(%joined) : (i8) -> i1\n    \"test.test\"(%root) : (i1) -> ()\n")
    Veir.Passes.InstCombineLLVM.OrLShrTruncToBitTest.orLShrTruncToBitTestCommuted
    (.llvm .icmp) (IntegerType.signless 1)

private def scalarI1CastRegression : Except String Unit := do
  runCastRule "cast-L1160" (castFunction "i13"
    "    %odd = \"llvm.mlir.constant\"() <{value = 5 : i13}> : () -> i13\n    %shifted = \"llvm.shl\"(%odd, %x) : (i13, i13) -> i13\n    %root = \"llvm.trunc\"(%shifted) : (i13) -> i1\n    \"test.test\"(%root) : (i1) -> ()\n")
    Veir.Passes.InstCombineLLVM.OddShlTruncToICmp.oddShlTruncToICmpEqZero
    (.llvm .icmp) (IntegerType.signless 1)
  runCastRule "cast-L1167" (r#""builtin.module"() ({
  "func.func"() <{function_type = (i13, i13) -> (), sym_name = "f"}> ({
  ^entry(%x : i13, %y : i13):
    %different = "llvm.xor"(%x, %y) : (i13, i13) -> i13
    %root = "llvm.trunc"(%different) <{"overflowFlags" = 1 : i32}> : (i13) -> i1
    "test.test"(%root) : (i1) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#)
    Veir.Passes.InstCombineLLVM.FlaggedXorTruncToICmp.flaggedXorTruncToICmpNe
    (.llvm .icmp) (IntegerType.signless 1)
  runCastRule "cast-L1172" (castFunction "i13"
    "    %one = \"llvm.mlir.constant\"() <{value = 1 : i13}> : () -> i13\n    %saturated = \"llvm.intr.usub.sat\"(%one, %x) : (i13, i13) -> i13\n    %root = \"llvm.trunc\"(%saturated) : (i13) -> i1\n    \"test.test\"(%root) : (i1) -> ()\n")
    Veir.Passes.InstCombineLLVM.UsubSatTruncToICmp.usubSatOneTruncToICmpEqZero
    (.llvm .icmp) (IntegerType.signless 1)


private def invertCastSource (srcTy srcAllOnes castOp castProps dstTy dstAllOnes : String)
    (innerLeft outerLeft : Bool) : String :=
  let innerOperands := if innerLeft then "%srcAllOnes, %x" else "%x, %srcAllOnes"
  let outerOperands := if outerLeft then "%dstAllOnes, %cast" else "%cast, %dstAllOnes"
  "\"builtin.module\"() ({\n" ++
  "  \"func.func\"() <{function_type = (" ++ srcTy ++ ") -> (), sym_name = \"f\"}> ({\n" ++
  "  ^entry(%x : " ++ srcTy ++ "):\n" ++
  "    %srcAllOnes = \"llvm.mlir.constant\"() <{value = " ++ srcAllOnes ++
    " : " ++ srcTy ++ "}> : () -> " ++ srcTy ++ "\n" ++
  "    %inner = \"llvm.xor\"(" ++ innerOperands ++ ") : (" ++ srcTy ++ ", " ++
    srcTy ++ ") -> " ++ srcTy ++ "\n" ++
  "    %cast = \"llvm." ++ castOp ++ "\"(%inner)" ++ castProps ++ " : (" ++ srcTy ++
    ") -> " ++ dstTy ++ "\n" ++
  "    %dstAllOnes = \"llvm.mlir.constant\"() <{value = " ++ dstAllOnes ++
    " : " ++ dstTy ++ "}> : () -> " ++ dstTy ++ "\n" ++
  "    %root = \"llvm.xor\"(" ++ outerOperands ++ ") : (" ++ dstTy ++ ", " ++
    dstTy ++ ") -> " ++ dstTy ++ "\n" ++
  "    \"test.test\"(%root) : (" ++ dstTy ++ ") -> ()\n" ++
  "    \"func.return\"() : () -> ()\n" ++
  "  }) : () -> ()\n}) : () -> ()"

private def runInvertCast (name source : String) (rule : Pattern OpCode)
    (replacement : OpCode) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString source.toUTF8
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw s!"{name} rewrite did not fire"
  if !testConsumesDirectCastOfBlockArgument rewritten.raw replacement then
    throw s!"{name} did not replace the complemented cast with a direct cast"
  rewritten.verify moduleOp

private def invertCastRegression : Except String Unit := do
  -- The i1 all-ones constants deliberately use the parser-normalized spelling `1`.
  runInvertCast "ic-free-invert-casts-L3150-sext"
    (invertCastSource "i1" "1" "sext" "" "i8" "-1" false false)
    Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertSExt (.llvm .sext)
  runInvertCast "ic-free-invert-casts-L3150-sext-inner-left"
    (invertCastSource "i1" "1" "sext" "" "i8" "-1" true false)
    Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertSExtInnerLeft (.llvm .sext)
  runInvertCast "ic-free-invert-casts-L3150-sext-outer-left"
    (invertCastSource "i1" "1" "sext" "" "i8" "-1" false true)
    Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertSExtOuterLeft (.llvm .sext)
  runInvertCast "ic-free-invert-casts-L3150-sext-both-left"
    (invertCastSource "i1" "1" "sext" "" "i8" "-1" true true)
    Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertSExtBothLeft (.llvm .sext)
  runInvertCast "ic-free-invert-casts-L3150-zext-nneg"
    (invertCastSource "i1" "1" "zext" " <{nonNeg}>" "i8" "-1" false false)
    Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertZExtNNeg (.llvm .sext)
  runInvertCast "ic-free-invert-casts-L3150-zext-nneg-inner-left"
    (invertCastSource "i1" "1" "zext" " <{nonNeg}>" "i8" "-1" true false)
    Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertZExtNNegInnerLeft (.llvm .sext)
  runInvertCast "ic-free-invert-casts-L3150-zext-nneg-outer-left"
    (invertCastSource "i1" "1" "zext" " <{nonNeg}>" "i8" "-1" false true)
    Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertZExtNNegOuterLeft (.llvm .sext)
  runInvertCast "ic-free-invert-casts-L3150-zext-nneg-both-left"
    (invertCastSource "i1" "1" "zext" " <{nonNeg}>" "i8" "-1" true true)
    Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertZExtNNegBothLeft (.llvm .sext)
  runInvertCast "ic-free-invert-casts-L3150-trunc"
    (invertCastSource "i8" "-1" "trunc" " <{\"overflowFlags\" = 3 : i32}>"
      "i1" "1" false false)
    Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertTrunc (.llvm .trunc)
  runInvertCast "ic-free-invert-casts-L3150-trunc-inner-left"
    (invertCastSource "i8" "-1" "trunc" " <{\"overflowFlags\" = 3 : i32}>"
      "i1" "1" true false)
    Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertTruncInnerLeft (.llvm .trunc)
  runInvertCast "ic-free-invert-casts-L3150-trunc-outer-left"
    (invertCastSource "i8" "-1" "trunc" " <{\"overflowFlags\" = 3 : i32}>"
      "i1" "1" false true)
    Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertTruncOuterLeft (.llvm .trunc)
  runInvertCast "ic-free-invert-casts-L3150-trunc-both-left"
    (invertCastSource "i8" "-1" "trunc" " <{\"overflowFlags\" = 3 : i32}>"
      "i1" "1" true true)
    Veir.Passes.InstCombineLLVM.FreeInvertCasts.invertTruncBothLeft (.llvm .trunc)

#guard regression = .ok ()
#guard composeCastRegression = .ok ()
#guard intrinsicRegression = .ok ()
#guard nnegRegression = .ok ()
#guard lowMaskRegression = .ok ()
#guard shiftTruncRegression = .ok ()
#guard scalarI1CastRegression = .ok ()
#guard invertCastRegression = .ok ()
