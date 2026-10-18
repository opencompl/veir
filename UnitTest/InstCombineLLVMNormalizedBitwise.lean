import Veir.Input
import Veir.Verifier
import Veir.PatternRewriter.Puddle.Execution
import Veir.Passes.InstCombineLLVM.AndComplementaryOrs
import Veir.Passes.InstCombineLLVM.AndOrNotAnd
import Veir.Passes.InstCombineLLVM.OrAndNotOr
import Veir.Passes.InstCombineLLVM.OrComplementaryMasks
import Veir.Passes.InstCombineLLVM.OrXorNotOr
import Veir.Passes.InstCombineLLVM.XorAndNotNot
import Veir.Passes.InstCombineLLVM.XorComplementaryMasks
import Veir.Passes.InstCombineLLVM.XorComplementaryOrs
import Veir.Passes.InstCombineLLVM.XorNotAndSelf
import Veir.Passes.InstCombineLLVM.XorNotMixed


open Veir Veir.Input Veir.Puddle Veir.Data

private def binarySource (ty body : String) : String :=
  "\"builtin.module\"() ({\n" ++
  "  \"func.func\"() <{function_type = (" ++ ty ++ ", " ++ ty ++
    ") -> (), sym_name = \"f\"}> ({\n" ++
  "  ^entry(%a : " ++ ty ++ ", %b : " ++ ty ++ "):\n" ++ body ++
  "    \"func.return\"() : () -> ()\n" ++
  "  }) : () -> ()\n}) : () -> ()"

private def bin (name opcode lhs rhs ty : String) : String :=
  "    %" ++ name ++ " = \"llvm." ++ opcode ++ "\"(%" ++ lhs ++ ", %" ++ rhs ++
    ") : (" ++ ty ++ ", " ++ ty ++ ") -> " ++ ty ++ "\n"

private def allOnes (ty value : String) : String :=
  "    %m = \"llvm.mlir.constant\"() <{value = " ++ value ++ " : " ++ ty ++
    "}> : () -> " ++ ty ++ "\n"

private def consume (name ty : String) : String :=
  "    \"test.test\"(%" ++ name ++ ") : (" ++ ty ++ ") -> ()\n"

private def mkNot (name value ty : String) (constantLeft : Bool) : String :=
  if constantLeft then bin name "xor" "m" value ty else bin name "xor" value "m" ty

private def andComplementaryOrsSource (ty value : String)
    (leftCommuted rightCommuted notBLeft notALeft : Bool) : String :=
  binarySource ty <| allOnes ty value ++ mkNot "notB" "b" ty notBLeft ++
    (if leftCommuted then bin "left" "or" "notB" "a" ty else bin "left" "or" "a" "notB" ty) ++
    mkNot "notA" "a" ty notALeft ++
    (if rightCommuted then bin "right" "or" "b" "notA" ty else bin "right" "or" "notA" "b" ty) ++
    bin "root" "and" "left" "right" ty ++ consume "root" ty

private def andOrNotAndSource (ty value : String) (andCommuted notLeft : Bool) : String :=
  binarySource ty <| allOnes ty value ++ bin "either" "or" "a" "b" ty ++
    (if andCommuted then bin "both" "and" "b" "a" ty else bin "both" "and" "a" "b" ty) ++
    mkNot "notBoth" "both" ty notLeft ++ bin "root" "and" "either" "notBoth" ty ++
    consume "root" ty

private def orAndNotOrSource (ty value : String) (orCommuted notLeft : Bool) : String :=
  binarySource ty <| allOnes ty value ++ bin "both" "and" "a" "b" ty ++
    (if orCommuted then bin "either" "or" "b" "a" ty else bin "either" "or" "a" "b" ty) ++
    mkNot "notEither" "either" ty notLeft ++ bin "root" "or" "both" "notEither" ty ++
    consume "root" ty

private def orComplementaryMasksSource (ty value : String)
    (leftCommuted rightCommuted notBLeft notALeft : Bool) : String :=
  binarySource ty <| allOnes ty value ++ mkNot "notB" "b" ty notBLeft ++
    (if leftCommuted then bin "left" "and" "notB" "a" ty else bin "left" "and" "a" "notB" ty) ++
    mkNot "notA" "a" ty notALeft ++
    (if rightCommuted then bin "right" "and" "b" "notA" ty else bin "right" "and" "notA" "b" ty) ++
    bin "root" "or" "left" "right" ty ++ consume "root" ty

private def orXorNotOrSource (ty value : String) (orCommuted notLeft : Bool) : String :=
  binarySource ty <| allOnes ty value ++ bin "different" "xor" "a" "b" ty ++
    (if orCommuted then bin "either" "or" "b" "a" ty else bin "either" "or" "a" "b" ty) ++
    mkNot "notEither" "either" ty notLeft ++ bin "root" "or" "different" "notEither" ty ++
    consume "root" ty

private def xorAndNotNotSource (ty value : String)
    (andCommuted notBLeft notALeft : Bool) : String :=
  binarySource ty <| allOnes ty value ++ mkNot "notB" "b" ty notBLeft ++
    (if andCommuted then bin "both" "and" "notB" "a" ty else bin "both" "and" "a" "notB" ty) ++
    mkNot "notA" "a" ty notALeft ++ bin "root" "xor" "both" "notA" ty ++ consume "root" ty

private def xorComplementarySource (innerOpcode ty value : String)
    (rootCommuted innerCommuted notBLeft notALeft : Bool) : String :=
  let left := if innerCommuted && !rootCommuted then
    bin "left" innerOpcode "notB" "a" ty else bin "left" innerOpcode "a" "notB" ty
  let right := if innerCommuted && rootCommuted then
    bin "right" innerOpcode "b" "notA" ty else bin "right" innerOpcode "notA" "b" ty
  let root := if rootCommuted then bin "root" "xor" "right" "left" ty
    else bin "root" "xor" "left" "right" ty
  binarySource ty <| allOnes ty value ++ mkNot "notB" "b" ty notBLeft ++ left ++
    mkNot "notA" "a" ty notALeft ++ right ++ root ++ consume "root" ty

private def xorNotAndSelfSource (ty value : String)
    (rootCommuted andCommuted notLeft : Bool) : String :=
  let both := if andCommuted then bin "both" "and" "b" "notA" ty
    else bin "both" "and" "notA" "b" ty
  let root := if rootCommuted then bin "root" "xor" "a" "both" ty
    else bin "root" "xor" "both" "a" ty
  binarySource ty <| allOnes ty value ++ mkNot "notA" "a" ty notLeft ++ both ++ root ++
    consume "root" ty

private def xorOrNotAndSource (ty value : String) (andCommuted notLeft : Bool) : String :=
  binarySource ty <| allOnes ty value ++ bin "either" "or" "a" "b" ty ++
    (if andCommuted then bin "both" "and" "b" "a" ty else bin "both" "and" "a" "b" ty) ++
    mkNot "notBoth" "both" ty notLeft ++ bin "root" "xor" "either" "notBoth" ty ++
    consume "root" ty

private def xorAndNotOrSource (ty value : String) (orCommuted notLeft : Bool) : String :=
  binarySource ty <| allOnes ty value ++ bin "both" "and" "a" "b" ty ++
    (if orCommuted then bin "either" "or" "b" "a" ty else bin "either" "or" "a" "b" ty) ++
    mkNot "notEither" "either" ty notLeft ++ bin "root" "xor" "both" "notEither" ty ++
    consume "root" ty

private inductive ExpectedShape
  | rootOpcode (opcode : OpCode)
  | directBlockArgs (opcode : OpCode)
  | nestedNot (inner : OpCode)

private def testRootMatches (ctx : IRContext OpCode) (expected : ExpectedShape) : Bool := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = (.test .test) then
        match op.getOperand! ctx 0 with
        | .blockArgument _ => return false
        | .opResult result =>
          match expected with
          | .rootOpcode opcode => return result.op.getOpType! ctx = opcode
          | .directBlockArgs opcode =>
            if result.op.getOpType! ctx != opcode then return false
            match result.op.getOperand! ctx 0, result.op.getOperand! ctx 1 with
            | .blockArgument _, .blockArgument _ => return true
            | _, _ => return false
          | .nestedNot inner =>
            if result.op.getOpType! ctx != (.llvm .xor) then return false
            match result.op.getOperand! ctx 0, result.op.getOperand! ctx 1 with
            | .opResult lhs, .opResult rhs =>
              return lhs.op.getOpType! ctx = inner &&
                rhs.op.getOpType! ctx = (.llvm .mlir__constant)
            | _, _ => return false
  return false

private def run (name source : String) (rule : Pattern OpCode)
    (expected : ExpectedShape) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString source.toUTF8
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw s!"{name} rewrite did not fire"
  if !testRootMatches rewritten.raw expected then
    throw s!"{name} did not replace the test root with the expected normalized form"
  rewritten.verify moduleOp

private def regression : Except String Unit := do
  run "AndComplementaryOrs.andComplementaryOrs-i1" (andComplementaryOrsSource "i1" "1" false false false false)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andComplementaryOrs (.rootOpcode (.llvm .xor))
  run "AndComplementaryOrs.andLeftCommutedComplementaryOrs-i1" (andComplementaryOrsSource "i1" "1" true false false false)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andLeftCommutedComplementaryOrs (.rootOpcode (.llvm .xor))
  run "AndComplementaryOrs.andRightCommutedComplementaryOrs-i1" (andComplementaryOrsSource "i1" "1" false true false false)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andRightCommutedComplementaryOrs (.rootOpcode (.llvm .xor))
  run "AndComplementaryOrs.andCommutedComplementaryOrs-i1" (andComplementaryOrsSource "i1" "1" true true false false)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andCommutedComplementaryOrs (.rootOpcode (.llvm .xor))
  run "AndComplementaryOrs.andComplementaryOrsNotBLeft-i1" (andComplementaryOrsSource "i1" "1" false false true false)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andComplementaryOrsNotBLeft (.rootOpcode (.llvm .xor))
  run "AndComplementaryOrs.andComplementaryOrsNotALeft-i1" (andComplementaryOrsSource "i1" "1" false false false true)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andComplementaryOrsNotALeft (.rootOpcode (.llvm .xor))
  run "AndComplementaryOrs.andComplementaryOrsBothNotLeft-i1" (andComplementaryOrsSource "i1" "1" false false true true)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andComplementaryOrsBothNotLeft (.rootOpcode (.llvm .xor))
  run "AndComplementaryOrs.andLeftCommutedComplementaryOrsNotBLeft-i1" (andComplementaryOrsSource "i1" "1" true false true false)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andLeftCommutedComplementaryOrsNotBLeft (.rootOpcode (.llvm .xor))
  run "AndComplementaryOrs.andLeftCommutedComplementaryOrsNotALeft-i1" (andComplementaryOrsSource "i1" "1" true false false true)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andLeftCommutedComplementaryOrsNotALeft (.rootOpcode (.llvm .xor))
  run "AndComplementaryOrs.andLeftCommutedComplementaryOrsBothNotLeft-i1" (andComplementaryOrsSource "i1" "1" true false true true)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andLeftCommutedComplementaryOrsBothNotLeft (.rootOpcode (.llvm .xor))
  run "AndComplementaryOrs.andRightCommutedComplementaryOrsNotBLeft-i1" (andComplementaryOrsSource "i1" "1" false true true false)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andRightCommutedComplementaryOrsNotBLeft (.rootOpcode (.llvm .xor))
  run "AndComplementaryOrs.andRightCommutedComplementaryOrsNotALeft-i1" (andComplementaryOrsSource "i1" "1" false true false true)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andRightCommutedComplementaryOrsNotALeft (.rootOpcode (.llvm .xor))
  run "AndComplementaryOrs.andRightCommutedComplementaryOrsBothNotLeft-i1" (andComplementaryOrsSource "i1" "1" false true true true)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andRightCommutedComplementaryOrsBothNotLeft (.rootOpcode (.llvm .xor))
  run "AndComplementaryOrs.andCommutedComplementaryOrsNotBLeft-i1" (andComplementaryOrsSource "i1" "1" true true true false)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andCommutedComplementaryOrsNotBLeft (.rootOpcode (.llvm .xor))
  run "AndComplementaryOrs.andCommutedComplementaryOrsNotALeft-i1" (andComplementaryOrsSource "i1" "1" true true false true)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andCommutedComplementaryOrsNotALeft (.rootOpcode (.llvm .xor))
  run "AndComplementaryOrs.andCommutedComplementaryOrsBothNotLeft-i1" (andComplementaryOrsSource "i1" "1" true true true true)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andCommutedComplementaryOrsBothNotLeft (.rootOpcode (.llvm .xor))
  run "AndOrNotAnd.andOrNotAnd-i1" (andOrNotAndSource "i1" "1" false false)
    Veir.Passes.InstCombineLLVM.AndOrNotAnd.andOrNotAnd (.rootOpcode (.llvm .xor))
  run "AndOrNotAnd.andOrNotCommutedAnd-i1" (andOrNotAndSource "i1" "1" true false)
    Veir.Passes.InstCombineLLVM.AndOrNotAnd.andOrNotCommutedAnd (.rootOpcode (.llvm .xor))
  run "AndOrNotAnd.andOrNotAndConstantLeft-i1" (andOrNotAndSource "i1" "1" false true)
    Veir.Passes.InstCombineLLVM.AndOrNotAnd.andOrNotAndConstantLeft (.rootOpcode (.llvm .xor))
  run "AndOrNotAnd.andOrNotCommutedAndConstantLeft-i1" (andOrNotAndSource "i1" "1" true true)
    Veir.Passes.InstCombineLLVM.AndOrNotAnd.andOrNotCommutedAndConstantLeft (.rootOpcode (.llvm .xor))
  run "OrAndNotOr.orAndNotOr-i1" (orAndNotOrSource "i1" "1" false false)
    Veir.Passes.InstCombineLLVM.OrAndNotOr.orAndNotOr (.rootOpcode (.llvm .xor))
  run "OrAndNotOr.orAndNotCommutedOr-i1" (orAndNotOrSource "i1" "1" true false)
    Veir.Passes.InstCombineLLVM.OrAndNotOr.orAndNotCommutedOr (.rootOpcode (.llvm .xor))
  run "OrAndNotOr.orAndNotOrConstantLeft-i1" (orAndNotOrSource "i1" "1" false true)
    Veir.Passes.InstCombineLLVM.OrAndNotOr.orAndNotOrConstantLeft (.rootOpcode (.llvm .xor))
  run "OrAndNotOr.orAndNotCommutedOrConstantLeft-i1" (orAndNotOrSource "i1" "1" true true)
    Veir.Passes.InstCombineLLVM.OrAndNotOr.orAndNotCommutedOrConstantLeft (.rootOpcode (.llvm .xor))
  run "OrComplementaryMasks.orComplementaryMasks-i1" (orComplementaryMasksSource "i1" "1" false false false false)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orComplementaryMasks (.rootOpcode (.llvm .xor))
  run "OrComplementaryMasks.orLeftCommutedComplementaryMasks-i1" (orComplementaryMasksSource "i1" "1" true false false false)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orLeftCommutedComplementaryMasks (.rootOpcode (.llvm .xor))
  run "OrComplementaryMasks.orRightCommutedComplementaryMasks-i1" (orComplementaryMasksSource "i1" "1" false true false false)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orRightCommutedComplementaryMasks (.rootOpcode (.llvm .xor))
  run "OrComplementaryMasks.orCommutedComplementaryMasks-i1" (orComplementaryMasksSource "i1" "1" true true false false)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orCommutedComplementaryMasks (.rootOpcode (.llvm .xor))
  run "OrComplementaryMasks.orComplementaryMasksNotBLeft-i1" (orComplementaryMasksSource "i1" "1" false false true false)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orComplementaryMasksNotBLeft (.rootOpcode (.llvm .xor))
  run "OrComplementaryMasks.orComplementaryMasksNotALeft-i1" (orComplementaryMasksSource "i1" "1" false false false true)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orComplementaryMasksNotALeft (.rootOpcode (.llvm .xor))
  run "OrComplementaryMasks.orComplementaryMasksBothNotLeft-i1" (orComplementaryMasksSource "i1" "1" false false true true)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orComplementaryMasksBothNotLeft (.rootOpcode (.llvm .xor))
  run "OrComplementaryMasks.orLeftCommutedComplementaryMasksNotBLeft-i1" (orComplementaryMasksSource "i1" "1" true false true false)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orLeftCommutedComplementaryMasksNotBLeft (.rootOpcode (.llvm .xor))
  run "OrComplementaryMasks.orLeftCommutedComplementaryMasksNotALeft-i1" (orComplementaryMasksSource "i1" "1" true false false true)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orLeftCommutedComplementaryMasksNotALeft (.rootOpcode (.llvm .xor))
  run "OrComplementaryMasks.orLeftCommutedComplementaryMasksBothNotLeft-i1" (orComplementaryMasksSource "i1" "1" true false true true)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orLeftCommutedComplementaryMasksBothNotLeft (.rootOpcode (.llvm .xor))
  run "OrComplementaryMasks.orRightCommutedComplementaryMasksNotBLeft-i1" (orComplementaryMasksSource "i1" "1" false true true false)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orRightCommutedComplementaryMasksNotBLeft (.rootOpcode (.llvm .xor))
  run "OrComplementaryMasks.orRightCommutedComplementaryMasksNotALeft-i1" (orComplementaryMasksSource "i1" "1" false true false true)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orRightCommutedComplementaryMasksNotALeft (.rootOpcode (.llvm .xor))
  run "OrComplementaryMasks.orRightCommutedComplementaryMasksBothNotLeft-i1" (orComplementaryMasksSource "i1" "1" false true true true)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orRightCommutedComplementaryMasksBothNotLeft (.rootOpcode (.llvm .xor))
  run "OrComplementaryMasks.orCommutedComplementaryMasksNotBLeft-i1" (orComplementaryMasksSource "i1" "1" true true true false)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orCommutedComplementaryMasksNotBLeft (.rootOpcode (.llvm .xor))
  run "OrComplementaryMasks.orCommutedComplementaryMasksNotALeft-i1" (orComplementaryMasksSource "i1" "1" true true false true)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orCommutedComplementaryMasksNotALeft (.rootOpcode (.llvm .xor))
  run "OrComplementaryMasks.orCommutedComplementaryMasksBothNotLeft-i1" (orComplementaryMasksSource "i1" "1" true true true true)
    Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orCommutedComplementaryMasksBothNotLeft (.rootOpcode (.llvm .xor))
  run "OrXorNotOr.orXorNotOr-i1" (orXorNotOrSource "i1" "1" false false)
    Veir.Passes.InstCombineLLVM.OrXorNotOr.orXorNotOr (.rootOpcode (.llvm .xor))
  run "OrXorNotOr.orXorNotCommutedOr-i1" (orXorNotOrSource "i1" "1" true false)
    Veir.Passes.InstCombineLLVM.OrXorNotOr.orXorNotCommutedOr (.rootOpcode (.llvm .xor))
  run "OrXorNotOr.orXorNotOrConstantLeft-i1" (orXorNotOrSource "i1" "1" false true)
    Veir.Passes.InstCombineLLVM.OrXorNotOr.orXorNotOrConstantLeft (.rootOpcode (.llvm .xor))
  run "OrXorNotOr.orXorNotCommutedOrConstantLeft-i1" (orXorNotOrSource "i1" "1" true true)
    Veir.Passes.InstCombineLLVM.OrXorNotOr.orXorNotCommutedOrConstantLeft (.rootOpcode (.llvm .xor))
  run "XorAndNotNot.xorAndNotNot-i1" (xorAndNotNotSource "i1" "1" false false false)
    Veir.Passes.InstCombineLLVM.XorAndNotNot.xorAndNotNot (.nestedNot (.llvm .and))
  run "XorAndNotNot.xorNotAndNot-i1" (xorAndNotNotSource "i1" "1" true false false)
    Veir.Passes.InstCombineLLVM.XorAndNotNot.xorNotAndNot (.nestedNot (.llvm .and))
  run "XorAndNotNot.xorAndNotNotFirstNotLeft-i1" (xorAndNotNotSource "i1" "1" false true false)
    Veir.Passes.InstCombineLLVM.XorAndNotNot.xorAndNotNotFirstNotLeft (.nestedNot (.llvm .and))
  run "XorAndNotNot.xorAndNotNotSecondNotLeft-i1" (xorAndNotNotSource "i1" "1" false false true)
    Veir.Passes.InstCombineLLVM.XorAndNotNot.xorAndNotNotSecondNotLeft (.nestedNot (.llvm .and))
  run "XorAndNotNot.xorAndNotNotBothNotLeft-i1" (xorAndNotNotSource "i1" "1" false true true)
    Veir.Passes.InstCombineLLVM.XorAndNotNot.xorAndNotNotBothNotLeft (.nestedNot (.llvm .and))
  run "XorAndNotNot.xorNotAndNotFirstNotLeft-i1" (xorAndNotNotSource "i1" "1" true true false)
    Veir.Passes.InstCombineLLVM.XorAndNotNot.xorNotAndNotFirstNotLeft (.nestedNot (.llvm .and))
  run "XorAndNotNot.xorNotAndNotSecondNotLeft-i1" (xorAndNotNotSource "i1" "1" true false true)
    Veir.Passes.InstCombineLLVM.XorAndNotNot.xorNotAndNotSecondNotLeft (.nestedNot (.llvm .and))
  run "XorAndNotNot.xorNotAndNotBothNotLeft-i1" (xorAndNotNotSource "i1" "1" true true true)
    Veir.Passes.InstCombineLLVM.XorAndNotNot.xorNotAndNotBothNotLeft (.nestedNot (.llvm .and))
  run "XorComplementaryMasks.xorComplementaryMasks-i1" (xorComplementarySource "and" "i1" "1" false false false false)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorComplementaryMasks (.directBlockArgs (.llvm .xor))
  run "XorComplementaryMasks.xorLeftCommutedComplementaryMasks-i1" (xorComplementarySource "and" "i1" "1" false true false false)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorLeftCommutedComplementaryMasks (.directBlockArgs (.llvm .xor))
  run "XorComplementaryMasks.xorSwappedComplementaryMasks-i1" (xorComplementarySource "and" "i1" "1" true false false false)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedComplementaryMasks (.directBlockArgs (.llvm .xor))
  run "XorComplementaryMasks.xorSwappedCommutedComplementaryMasks-i1" (xorComplementarySource "and" "i1" "1" true true false false)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedCommutedComplementaryMasks (.directBlockArgs (.llvm .xor))
  run "XorComplementaryMasks.xorComplementaryMasksNotBLeft-i1" (xorComplementarySource "and" "i1" "1" false false true false)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorComplementaryMasksNotBLeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryMasks.xorComplementaryMasksNotALeft-i1" (xorComplementarySource "and" "i1" "1" false false false true)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorComplementaryMasksNotALeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryMasks.xorComplementaryMasksBothNotLeft-i1" (xorComplementarySource "and" "i1" "1" false false true true)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorComplementaryMasksBothNotLeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryMasks.xorLeftCommutedComplementaryMasksNotBLeft-i1" (xorComplementarySource "and" "i1" "1" false true true false)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorLeftCommutedComplementaryMasksNotBLeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryMasks.xorLeftCommutedComplementaryMasksNotALeft-i1" (xorComplementarySource "and" "i1" "1" false true false true)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorLeftCommutedComplementaryMasksNotALeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryMasks.xorLeftCommutedComplementaryMasksBothNotLeft-i1" (xorComplementarySource "and" "i1" "1" false true true true)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorLeftCommutedComplementaryMasksBothNotLeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryMasks.xorSwappedComplementaryMasksNotBLeft-i1" (xorComplementarySource "and" "i1" "1" true false true false)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedComplementaryMasksNotBLeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryMasks.xorSwappedComplementaryMasksNotALeft-i1" (xorComplementarySource "and" "i1" "1" true false false true)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedComplementaryMasksNotALeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryMasks.xorSwappedComplementaryMasksBothNotLeft-i1" (xorComplementarySource "and" "i1" "1" true false true true)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedComplementaryMasksBothNotLeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryMasks.xorSwappedCommutedComplementaryMasksNotBLeft-i1" (xorComplementarySource "and" "i1" "1" true true true false)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedCommutedComplementaryMasksNotBLeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryMasks.xorSwappedCommutedComplementaryMasksNotALeft-i1" (xorComplementarySource "and" "i1" "1" true true false true)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedCommutedComplementaryMasksNotALeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryMasks.xorSwappedCommutedComplementaryMasksBothNotLeft-i1" (xorComplementarySource "and" "i1" "1" true true true true)
    Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedCommutedComplementaryMasksBothNotLeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryOrs.xorComplementaryOrs-i1" (xorComplementarySource "or" "i1" "1" false false false false)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorComplementaryOrs (.directBlockArgs (.llvm .xor))
  run "XorComplementaryOrs.xorLeftCommutedComplementaryOrs-i1" (xorComplementarySource "or" "i1" "1" false true false false)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorLeftCommutedComplementaryOrs (.directBlockArgs (.llvm .xor))
  run "XorComplementaryOrs.xorSwappedComplementaryOrs-i1" (xorComplementarySource "or" "i1" "1" true false false false)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedComplementaryOrs (.directBlockArgs (.llvm .xor))
  run "XorComplementaryOrs.xorSwappedCommutedComplementaryOrs-i1" (xorComplementarySource "or" "i1" "1" true true false false)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedCommutedComplementaryOrs (.directBlockArgs (.llvm .xor))
  run "XorComplementaryOrs.xorComplementaryOrsNotBLeft-i1" (xorComplementarySource "or" "i1" "1" false false true false)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorComplementaryOrsNotBLeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryOrs.xorComplementaryOrsNotALeft-i1" (xorComplementarySource "or" "i1" "1" false false false true)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorComplementaryOrsNotALeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryOrs.xorComplementaryOrsBothNotLeft-i1" (xorComplementarySource "or" "i1" "1" false false true true)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorComplementaryOrsBothNotLeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryOrs.xorLeftCommutedComplementaryOrsNotBLeft-i1" (xorComplementarySource "or" "i1" "1" false true true false)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorLeftCommutedComplementaryOrsNotBLeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryOrs.xorLeftCommutedComplementaryOrsNotALeft-i1" (xorComplementarySource "or" "i1" "1" false true false true)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorLeftCommutedComplementaryOrsNotALeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryOrs.xorLeftCommutedComplementaryOrsBothNotLeft-i1" (xorComplementarySource "or" "i1" "1" false true true true)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorLeftCommutedComplementaryOrsBothNotLeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryOrs.xorSwappedComplementaryOrsNotBLeft-i1" (xorComplementarySource "or" "i1" "1" true false true false)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedComplementaryOrsNotBLeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryOrs.xorSwappedComplementaryOrsNotALeft-i1" (xorComplementarySource "or" "i1" "1" true false false true)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedComplementaryOrsNotALeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryOrs.xorSwappedComplementaryOrsBothNotLeft-i1" (xorComplementarySource "or" "i1" "1" true false true true)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedComplementaryOrsBothNotLeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryOrs.xorSwappedCommutedComplementaryOrsNotBLeft-i1" (xorComplementarySource "or" "i1" "1" true true true false)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedCommutedComplementaryOrsNotBLeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryOrs.xorSwappedCommutedComplementaryOrsNotALeft-i1" (xorComplementarySource "or" "i1" "1" true true false true)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedCommutedComplementaryOrsNotALeft (.directBlockArgs (.llvm .xor))
  run "XorComplementaryOrs.xorSwappedCommutedComplementaryOrsBothNotLeft-i1" (xorComplementarySource "or" "i1" "1" true true true true)
    Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedCommutedComplementaryOrsBothNotLeft (.directBlockArgs (.llvm .xor))
  run "XorNotAndSelf.xorNotAndSelf-i1" (xorNotAndSelfSource "i1" "1" false false false)
    Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorNotAndSelf (.directBlockArgs (.llvm .or))
  run "XorNotAndSelf.xorCommutedNotAndSelf-i1" (xorNotAndSelfSource "i1" "1" false true false)
    Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorCommutedNotAndSelf (.directBlockArgs (.llvm .or))
  run "XorNotAndSelf.xorSelfNotAnd-i1" (xorNotAndSelfSource "i1" "1" true false false)
    Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorSelfNotAnd (.directBlockArgs (.llvm .or))
  run "XorNotAndSelf.xorSelfCommutedNotAnd-i1" (xorNotAndSelfSource "i1" "1" true true false)
    Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorSelfCommutedNotAnd (.directBlockArgs (.llvm .or))
  run "XorNotAndSelf.xorNotAndSelfConstantLeft-i1" (xorNotAndSelfSource "i1" "1" false false true)
    Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorNotAndSelfConstantLeft (.directBlockArgs (.llvm .or))
  run "XorNotAndSelf.xorCommutedNotAndSelfConstantLeft-i1" (xorNotAndSelfSource "i1" "1" false true true)
    Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorCommutedNotAndSelfConstantLeft (.directBlockArgs (.llvm .or))
  run "XorNotAndSelf.xorSelfNotAndConstantLeft-i1" (xorNotAndSelfSource "i1" "1" true false true)
    Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorSelfNotAndConstantLeft (.directBlockArgs (.llvm .or))
  run "XorNotAndSelf.xorSelfCommutedNotAndConstantLeft-i1" (xorNotAndSelfSource "i1" "1" true true true)
    Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorSelfCommutedNotAndConstantLeft (.directBlockArgs (.llvm .or))
  run "XorNotMixed.xorOrNotAnd-i1" (xorOrNotAndSource "i1" "1" false false)
    Veir.Passes.InstCombineLLVM.XorNotMixed.xorOrNotAnd (.nestedNot (.llvm .xor))
  run "XorNotMixed.xorOrNotCommutedAnd-i1" (xorOrNotAndSource "i1" "1" true false)
    Veir.Passes.InstCombineLLVM.XorNotMixed.xorOrNotCommutedAnd (.nestedNot (.llvm .xor))
  run "XorNotMixed.xorAndNotOr-i1" (xorAndNotOrSource "i1" "1" false false)
    Veir.Passes.InstCombineLLVM.XorNotMixed.xorAndNotOr (.nestedNot (.llvm .xor))
  run "XorNotMixed.xorAndNotCommutedOr-i1" (xorAndNotOrSource "i1" "1" true false)
    Veir.Passes.InstCombineLLVM.XorNotMixed.xorAndNotCommutedOr (.nestedNot (.llvm .xor))
  run "XorNotMixed.xorOrNotAndConstantLeft-i1" (xorOrNotAndSource "i1" "1" false true)
    Veir.Passes.InstCombineLLVM.XorNotMixed.xorOrNotAndConstantLeft (.nestedNot (.llvm .xor))
  run "XorNotMixed.xorOrNotCommutedAndConstantLeft-i1" (xorOrNotAndSource "i1" "1" true true)
    Veir.Passes.InstCombineLLVM.XorNotMixed.xorOrNotCommutedAndConstantLeft (.nestedNot (.llvm .xor))
  run "XorNotMixed.xorAndNotOrConstantLeft-i1" (xorAndNotOrSource "i1" "1" false true)
    Veir.Passes.InstCombineLLVM.XorNotMixed.xorAndNotOrConstantLeft (.nestedNot (.llvm .xor))
  run "XorNotMixed.xorAndNotCommutedOrConstantLeft-i1" (xorAndNotOrSource "i1" "1" true true)
    Veir.Passes.InstCombineLLVM.XorNotMixed.xorAndNotCommutedOrConstantLeft (.nestedNot (.llvm .xor))
  run "AndComplementaryOrs.andComplementaryOrs-i8"
    (andComplementaryOrsSource "i8" "-1" false false false false)
    Veir.Passes.InstCombineLLVM.AndComplementaryOrs.andComplementaryOrs
    (.rootOpcode (.llvm .xor))

#guard regression = .ok ()
