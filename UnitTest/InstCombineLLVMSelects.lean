import Veir.Input
import Veir.Verifier
import Veir.PatternRewriter.Puddle.Execution
import Veir.Passes.InstCombineLLVM.SelectInvertFalse
import Veir.Passes.InstCombineLLVM.SelectInvertTrue
import Veir.Passes.InstCombineLLVM.SelectNestedTrue
import Veir.Passes.InstCombineLLVM.SelectNestedFalse
import Veir.Passes.InstCombineLLVM.SelectAbsorbNot
import Veir.Passes.InstCombineLLVM.SelectSymmetricNested
import Veir.Passes.InstCombineLLVM.SelectNestedLogicalAnd
import Veir.Passes.InstCombineLLVM.SelectNestedLogicalOr
import Veir.Passes.InstCombineLLVM.SelectNestedLogicalAndNot
import Veir.Passes.InstCombineLLVM.SelectNestedLogicalOrNot
import Veir.Passes.InstCombineLLVM.SelectDeMorganAnd
import Veir.Passes.InstCombineLLVM.SelectDeMorganOr
import Veir.Passes.InstCombineLLVM.SelectOrNotCondition
import Veir.Passes.InstCombineLLVM.SelectAndFalseArm
import Veir.Passes.InstCombineLLVM.SelectOrTrueArm
import Veir.Passes.InstCombineLLVM.SelectAndNotFalse
import Veir.Passes.InstCombineLLVM.SelectLogicalXor

open Veir Veir.Input Veir.Puddle Veir.Data

private def selectSource (constant : Int) (constantIsFalseArm : Bool) : String :=
  "\"builtin.module\"() ({\n" ++
  "  \"func.func\"() <{function_type = (i1, i1) -> (), sym_name = \"f\"}> ({\n" ++
  "  ^entry(%a : i1, %b : i1):\n" ++
  "    %c = \"llvm.mlir.constant\"() <{value = " ++ toString constant ++
    " : i1}> : () -> i1\n" ++
  (if constantIsFalseArm then
    "    %root = \"llvm.select\"(%a, %b, %c) : (i1, i1, i1) -> i1\n"
   else
    "    %root = \"llvm.select\"(%a, %c, %b) : (i1, i1, i1) -> i1\n") ++
  "    \"test.test\"(%root) : (i1) -> ()\n" ++
  "    \"func.return\"() : () -> ()\n" ++
  "  }) : () -> ()\n}) : () -> ()"

private def nestedSelectSource (oneArm : Bool) : String :=
  "\"builtin.module\"() ({\n" ++
  "  \"func.func\"() <{function_type = (i1, i1) -> (), sym_name = \"f\"}> ({\n" ++
  "  ^entry(%a : i1, %b : i1):\n" ++
  "    %c = \"llvm.mlir.constant\"() <{value = " ++ (if oneArm then "1" else "0") ++
    " : i1}> : () -> i1\n" ++
  (if oneArm then
    "    %inner = \"llvm.select\"(%a, %c, %b) : (i1, i1, i1) -> i1\n" ++
    "    %root = \"llvm.select\"(%inner, %c, %b) : (i1, i1, i1) -> i1\n"
   else
    "    %inner = \"llvm.select\"(%a, %b, %c) : (i1, i1, i1) -> i1\n" ++
    "    %root = \"llvm.select\"(%inner, %b, %c) : (i1, i1, i1) -> i1\n") ++
  "    \"test.test\"(%root) : (i1) -> ()\n" ++
  "    \"func.return\"() : () -> ()\n" ++
  "  }) : () -> ()\n}) : () -> ()"

private def absorbNotSource (constantLeft : Bool) : String :=
  "\"builtin.module\"() ({\n" ++
  "  \"func.func\"() <{function_type = (i1, i8, i8) -> (), sym_name = \"f\"}> ({\n" ++
  "  ^entry(%c : i1, %x : i8, %y : i8):\n" ++
  "    %one = \"llvm.mlir.constant\"() <{value = 1 : i1}> : () -> i1\n" ++
  "    %not = \"llvm.xor\"(" ++ (if constantLeft then "%one, %c" else "%c, %one") ++
    ") : (i1, i1) -> i1\n" ++
  "    %root = \"llvm.select\"(%not, %x, %y) : (i1, i8, i8) -> i8\n" ++
  "    \"test.test\"(%root) : (i8) -> ()\n" ++
  "    \"func.return\"() : () -> ()\n" ++
  "  }) : () -> ()\n}) : () -> ()"

private def symmetricNestedSource : String := r#""builtin.module"() ({
  "func.func"() <{function_type = (i1, i1, i8, i8) -> (), sym_name = "f"}> ({
  ^entry(%c0 : i1, %c1 : i1, %a : i8, %b : i8):
    %inner = "llvm.select"(%c1, %a, %b) : (i1, i8, i8) -> i8
    %swapped = "llvm.select"(%c1, %b, %a) : (i1, i8, i8) -> i8
    %root = "llvm.select"(%c0, %inner, %swapped) : (i1, i8, i8) -> i8
    "test.test"(%root) : (i8) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#

private def nestedLogicalSource (isAnd : Bool) : String :=
  "\"builtin.module\"() ({\n" ++
  "  \"func.func\"() <{function_type = (i1, i1, i8, i8) -> (), sym_name = \"f\"}> ({\n" ++
  "  ^entry(%c0 : i1, %c1 : i1, %a : i8, %b : i8):\n" ++
  "    %inner = \"llvm.select\"(%c1, %a, %b) : (i1, i8, i8) -> i8\n" ++
  (if isAnd then
    "    %root = \"llvm.select\"(%c0, %inner, %b) : (i1, i8, i8) -> i8\n"
   else
    "    %root = \"llvm.select\"(%c0, %a, %inner) : (i1, i8, i8) -> i8\n") ++
  "    \"test.test\"(%root) : (i8) -> ()\n" ++
  "    \"func.return\"() : () -> ()\n" ++
  "  }) : () -> ()\n}) : () -> ()"

private def nestedLogicalNotSource (isAnd : Bool) : String :=
  "\"builtin.module\"() ({\n" ++
  "  \"func.func\"() <{function_type = (i1, i1, i8, i8) -> (), sym_name = \"f\"}> ({\n" ++
  "  ^entry(%c0 : i1, %c1 : i1, %a : i8, %b : i8):\n" ++
  "    %inner = \"llvm.select\"(%c1, %b, %a) : (i1, i8, i8) -> i8\n" ++
  (if isAnd then
    "    %root = \"llvm.select\"(%c0, %inner, %b) : (i1, i8, i8) -> i8\n"
   else
    "    %root = \"llvm.select\"(%c0, %a, %inner) : (i1, i8, i8) -> i8\n") ++
  "    \"test.test\"(%root) : (i8) -> ()\n" ++
  "    \"func.return\"() : () -> ()\n" ++
  "  }) : () -> ()\n}) : () -> ()"

private def deMorganAndSource (leftA leftB : Bool) : String :=
  "\"builtin.module\"() ({\n" ++
  "  \"func.func\"() <{function_type = (i1, i1) -> (), sym_name = \"f\"}> ({\n" ++
  "  ^entry(%a : i1, %b : i1):\n" ++
  "    %one.a = \"llvm.mlir.constant\"() <{value = 1 : i1}> : () -> i1\n" ++
  "    %one.b = \"llvm.mlir.constant\"() <{value = 1 : i1}> : () -> i1\n" ++
  "    %zero = \"llvm.mlir.constant\"() <{value = 0 : i1}> : () -> i1\n" ++
  "    %not.a = \"llvm.xor\"(" ++ (if leftA then "%one.a, %a" else "%a, %one.a") ++
    ") : (i1, i1) -> i1\n" ++
  "    %not.b = \"llvm.xor\"(" ++ (if leftB then "%one.b, %b" else "%b, %one.b") ++
    ") : (i1, i1) -> i1\n" ++
  "    %root = \"llvm.select\"(%not.a, %not.b, %zero) : (i1, i1, i1) -> i1\n" ++
  "    \"test.test\"(%root) : (i1) -> ()\n" ++
  "    \"func.return\"() : () -> ()\n" ++
  "  }) : () -> ()\n}) : () -> ()"

private def deMorganOrSource (leftA leftB : Bool) : String :=
  "\"builtin.module\"() ({\n" ++
  "  \"func.func\"() <{function_type = (i1, i1) -> (), sym_name = \"f\"}> ({\n" ++
  "  ^entry(%a : i1, %b : i1):\n" ++
  "    %one.a = \"llvm.mlir.constant\"() <{value = 1 : i1}> : () -> i1\n" ++
  "    %one.b = \"llvm.mlir.constant\"() <{value = 1 : i1}> : () -> i1\n" ++
  "    %one.root = \"llvm.mlir.constant\"() <{value = 1 : i1}> : () -> i1\n" ++
  "    %not.a = \"llvm.xor\"(" ++ (if leftA then "%one.a, %a" else "%a, %one.a") ++
    ") : (i1, i1) -> i1\n" ++
  "    %not.b = \"llvm.xor\"(" ++ (if leftB then "%one.b, %b" else "%b, %one.b") ++
    ") : (i1, i1) -> i1\n" ++
  "    %root = \"llvm.select\"(%not.a, %one.root, %not.b) : (i1, i1, i1) -> i1\n" ++
  "    \"test.test\"(%root) : (i1) -> ()\n" ++
  "    \"func.return\"() : () -> ()\n" ++
  "  }) : () -> ()\n}) : () -> ()"

private def orNotConditionSource (notLeft orSwapped disjoint : Bool) : String :=
  "\"builtin.module\"() ({\n" ++
  "  \"func.func\"() <{function_type = (i1, i1, i1) -> (), sym_name = \"f\"}> ({\n" ++
  "  ^entry(%a : i1, %b : i1, %c : i1):\n" ++
  "    %one = \"llvm.mlir.constant\"() <{value = 1 : i1}> : () -> i1\n" ++
  "    %not = \"llvm.xor\"(" ++ (if notLeft then "%one, %a" else "%a, %one") ++
    ") : (i1, i1) -> i1\n" ++
  "    %condition = \"llvm.or\"(" ++
    (if orSwapped then "%c, %not" else "%not, %c") ++ ")" ++
    (if disjoint then " <{isDisjoint}>" else "") ++ " : (i1, i1) -> i1\n" ++
  "    %root = \"llvm.select\"(%condition, %a, %b) : (i1, i1, i1) -> i1\n" ++
  "    \"test.test\"(%root) : (i1) -> ()\n" ++
  "    \"func.return\"() : () -> ()\n" ++
  "  }) : () -> ()\n}) : () -> ()"

private def invertedOperandConditionSource (opcode notValue other : String)
    (notFirst notLeft opSwapped disjoint : Bool) : String :=
  let notOperand := "%" ++ notValue
  let otherOperand := "%" ++ other
  let ordered := if notFirst then ("%not", otherOperand) else (otherOperand, "%not")
  let operands := if opSwapped then (ordered.2, ordered.1) else ordered
  "\"builtin.module\"() ({\n" ++
  "  \"func.func\"() <{function_type = (i1, i1, i1) -> (), sym_name = \"f\"}> ({\n" ++
  "  ^entry(%a : i1, %b : i1, %c : i1):\n" ++
  "    %one = \"llvm.mlir.constant\"() <{value = 1 : i1}> : () -> i1\n" ++
  "    %not = \"llvm.xor\"(" ++
    (if notLeft then "%one, " ++ notOperand else notOperand ++ ", %one") ++
    ") : (i1, i1) -> i1\n" ++
  "    %condition = \"llvm." ++ opcode ++ "\"(" ++ operands.1 ++ ", " ++ operands.2 ++
    ")" ++ (if disjoint then " <{isDisjoint}>" else "") ++ " : (i1, i1) -> i1\n" ++
  "    %root = \"llvm.select\"(%condition, %a, %b) : (i1, i1, i1) -> i1\n" ++
  "    \"test.test\"(%root) : (i1) -> ()\n" ++
  "    \"func.return\"() : () -> ()\n" ++
  "  }) : () -> ()\n}) : () -> ()"

private def logicalXorSource (andSelect orSelect notLeft outerSwapped orSwapped
    disjoint : Bool) : String :=
  let innerAnd := if andSelect then
    "    %inner.and = \"llvm.select\"(%a, %b, %zero) : (i1, i1, i1) -> i1\n"
  else
    "    %inner.and = \"llvm.and\"(%a, %b) : (i1, i1) -> i1\n"
  let innerOr := if orSelect then
    "    %inner.or = \"llvm.select\"(" ++
      (if orSwapped then "%b, %one, %a" else "%a, %one, %b") ++
      ") : (i1, i1, i1) -> i1\n"
  else
    "    %inner.or = \"llvm.or\"(" ++
      (if orSwapped then "%b, %a" else "%a, %b") ++ ")" ++
      (if disjoint then " <{isDisjoint}>" else "") ++ " : (i1, i1) -> i1\n"
  "\"builtin.module\"() ({\n" ++
  "  \"func.func\"() <{function_type = (i1, i1) -> (), sym_name = \"f\"}> ({\n" ++
  "  ^entry(%a : i1, %b : i1):\n" ++
  "    %zero = \"llvm.mlir.constant\"() <{value = 0 : i1}> : () -> i1\n" ++
  "    %one = \"llvm.mlir.constant\"() <{value = 1 : i1}> : () -> i1\n" ++
  innerAnd ++
  "    %not = \"llvm.xor\"(" ++
    (if notLeft then "%one, %inner.and" else "%inner.and, %one") ++
    ") : (i1, i1) -> i1\n" ++ innerOr ++
  "    %root = \"llvm.select\"(" ++
    (if outerSwapped then "%inner.or, %not, %zero" else "%not, %inner.or, %zero") ++
    ") : (i1, i1, i1) -> i1\n" ++
  "    \"test.test\"(%root) : (i1) -> ()\n" ++
  "    \"func.return\"() : () -> ()\n" ++
  "  }) : () -> ()\n}) : () -> ()"

private def testInputProducer? (ctx : IRContext OpCode) : Option OperationPtr := Id.run do
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = (.test .test) then
        match op.getOperand! ctx 0 with
        | .opResult result => return some result.op
        | .blockArgument _ => return none
  return none

private def countOp (ctx : IRContext OpCode) (opcode : OpCode) : Nat := Id.run do
  let mut count := 0
  for op in ctx.operations.keys do
    if h : op.InBounds ctx then
      if op.getOpType ctx h = opcode then count := count + 1
  return count

private def conditionHasShape (ctx : IRContext OpCode) (select : OperationPtr)
    (expectedOpcode : Option OpCode) : Bool :=
  match select.getOperand! ctx 0 with
  | .blockArgument _ => expectedOpcode.isNone
  | .opResult result => expectedOpcode == some (result.op.getOpType! ctx)

private def runSelect (name source : String) (rule : Pattern OpCode)
    (expectedConditionOpcode : Option OpCode) (expectedSelects : Nat)
    (expectedXors : Option Nat := none) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString source.toUTF8
  let some originalRoot := testInputProducer? ctx.raw
    | throw s!"{name}: test root has no defining operation"
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw s!"{name}: rewrite driver failed"
  let some replacementRoot := testInputProducer? rewritten.raw
    | throw s!"{name}: replacement has no defining operation"
  if replacementRoot = originalRoot || originalRoot.InBounds rewritten.raw then
    throw s!"{name}: matched select root was not replaced"
  if replacementRoot.getOpType! rewritten.raw != (.llvm .select) then
    throw s!"{name}: replacement root is not llvm.select"
  if countOp rewritten.raw (.llvm .select) != expectedSelects then
    throw s!"{name}: unexpected select count after rewrite"
  if let some expected := expectedXors then
    if countOp rewritten.raw (.llvm .xor) != expected then
      throw s!"{name}: unexpected xor count after rewrite"
  if !conditionHasShape rewritten.raw replacementRoot expectedConditionOpcode then
    throw s!"{name}: replacement condition has the wrong defining shape"
  rewritten.verify moduleOp

private def runDeMorgan (name source : String) (rule : Pattern OpCode) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString source.toUTF8
  let some originalRoot := testInputProducer? ctx.raw
    | throw s!"{name}: test root has no defining operation"
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw s!"{name}: rewrite driver failed"
  let some replacementRoot := testInputProducer? rewritten.raw
    | throw s!"{name}: replacement has no defining operation"
  if replacementRoot = originalRoot || originalRoot.InBounds rewritten.raw then
    throw s!"{name}: matched select root was not replaced"
  if replacementRoot.getOpType! rewritten.raw != (.llvm .xor) then
    throw s!"{name}: replacement root is not llvm.xor"
  match replacementRoot.getOperand! rewritten.raw 0 with
  | .blockArgument _ => throw s!"{name}: replacement xor does not consume a select"
  | .opResult result =>
      if result.op.getOpType! rewritten.raw != (.llvm .select) then
        throw s!"{name}: replacement xor does not consume llvm.select"
  if countOp rewritten.raw (.llvm .select) != 1 ||
      countOp rewritten.raw (.llvm .xor) != 1 then
    throw s!"{name}: unexpected De Morgan replacement operation counts"
  rewritten.verify moduleOp

private def runXorResult (name source : String) (rule : Pattern OpCode) : Except String Unit := do
  let (ctx, moduleOp, _) ← parseSourceString source.toUTF8
  let some originalRoot := testInputProducer? ctx.raw
    | throw s!"{name}: test root has no defining operation"
  let some rewritten := RewritePattern.applyInContext (Pattern.compile rule).run ctx
    | throw s!"{name}: rewrite driver failed"
  let some replacementRoot := testInputProducer? rewritten.raw
    | throw s!"{name}: replacement has no defining operation"
  if replacementRoot = originalRoot || originalRoot.InBounds rewritten.raw then
    throw s!"{name}: matched select root was not replaced"
  if replacementRoot.getOpType! rewritten.raw != (.llvm .xor) then
    throw s!"{name}: replacement root is not llvm.xor"
  if countOp rewritten.raw (.llvm .xor) != 1 || countOp rewritten.raw (.llvm .select) != 0 then
    throw s!"{name}: unexpected logical-xor replacement operation counts"
  rewritten.verify moduleOp

private def regression : Except String Unit := do
  runSelect "select-L3966" (selectSource 0 false)
    Veir.Passes.InstCombineLLVM.SelectInvertFalse.selectInvertFalse (some (.llvm .xor)) 1
  runSelect "select-L3974" (selectSource 1 true)
    Veir.Passes.InstCombineLLVM.SelectInvertTrue.selectInvertTrue (some (.llvm .xor)) 1
  runSelect "select-L4002" (nestedSelectSource true)
    Veir.Passes.InstCombineLLVM.SelectNestedTrue.selectNestedTrue none 1
  runSelect "select-L4006" (nestedSelectSource false)
    Veir.Passes.InstCombineLLVM.SelectNestedFalse.selectNestedFalse none 1
  runSelect "select-L5252-right" (absorbNotSource false)
    Veir.Passes.InstCombineLLVM.SelectAbsorbNot.selectAbsorbNot none 1
  runSelect "select-L5252-left" (absorbNotSource true)
    Veir.Passes.InstCombineLLVM.SelectAbsorbNot.selectAbsorbNotConstantLeft none 1
  runSelect "select-L3709" symmetricNestedSource
    Veir.Passes.InstCombineLLVM.SelectSymmetricNested.selectSymmetricNested
      (some (.llvm .xor)) 1
  runSelect "select-L5166-and" (nestedLogicalSource true)
    Veir.Passes.InstCombineLLVM.SelectNestedLogicalAnd.selectNestedLogicalAnd
      (some (.llvm .select)) 2
  runSelect "select-L5197-or" (nestedLogicalSource false)
    Veir.Passes.InstCombineLLVM.SelectNestedLogicalOr.selectNestedLogicalOr
      (some (.llvm .select)) 2
  runSelect "select-L5166-and-not" (nestedLogicalNotSource true)
    Veir.Passes.InstCombineLLVM.SelectNestedLogicalAndNot.selectNestedLogicalAndNot
      (some (.llvm .select)) 2 (some 1)
  runSelect "select-L5197-or-not" (nestedLogicalNotSource false)
    Veir.Passes.InstCombineLLVM.SelectNestedLogicalOrNot.selectNestedLogicalOrNot
      (some (.llvm .select)) 2 (some 1)
  runDeMorgan "select-L3985-rr" (deMorganAndSource false false)
    Veir.Passes.InstCombineLLVM.SelectDeMorganAnd.selectDeMorganAnd
  runDeMorgan "select-L3985-rl" (deMorganAndSource false true)
    Veir.Passes.InstCombineLLVM.SelectDeMorganAnd.selectDeMorganAndNotBLeft
  runDeMorgan "select-L3985-lr" (deMorganAndSource true false)
    Veir.Passes.InstCombineLLVM.SelectDeMorganAnd.selectDeMorganAndNotALeft
  runDeMorgan "select-L3985-ll" (deMorganAndSource true true)
    Veir.Passes.InstCombineLLVM.SelectDeMorganAnd.selectDeMorganAndBothLeft
  runDeMorgan "select-L3996-rr" (deMorganOrSource false false)
    Veir.Passes.InstCombineLLVM.SelectDeMorganOr.selectDeMorganOr
  runDeMorgan "select-L3996-rl" (deMorganOrSource false true)
    Veir.Passes.InstCombineLLVM.SelectDeMorganOr.selectDeMorganOrNotBLeft
  runDeMorgan "select-L3996-lr" (deMorganOrSource true false)
    Veir.Passes.InstCombineLLVM.SelectDeMorganOr.selectDeMorganOrNotALeft
  runDeMorgan "select-L3996-ll" (deMorganOrSource true true)
    Veir.Passes.InstCombineLLVM.SelectDeMorganOr.selectDeMorganOrBothLeft
  runSelect "select-L4020-rr" (orNotConditionSource false false false)
    Veir.Passes.InstCombineLLVM.SelectOrNotCondition.selectOrNotCondition none 2 (some 0)
  runSelect "select-L4020-or-swapped" (orNotConditionSource false true false)
    Veir.Passes.InstCombineLLVM.SelectOrNotCondition.selectOrNotConditionOrSwapped
      none 2 (some 0)
  runSelect "select-L4020-not-left" (orNotConditionSource true false false)
    Veir.Passes.InstCombineLLVM.SelectOrNotCondition.selectOrNotConditionNotLeft
      none 2 (some 0)
  runSelect "select-L4020-both-swapped-disjoint" (orNotConditionSource true true true)
    Veir.Passes.InstCombineLLVM.SelectOrNotCondition.selectOrNotConditionBothSwapped
      none 2 (some 0)
  runSelect "select-L4027-rr"
    (invertedOperandConditionSource "and" "c" "b" true false false false)
    Veir.Passes.InstCombineLLVM.SelectAndFalseArm.selectAndFalseArm none 2 (some 0)
  runSelect "select-L4027-op-swapped"
    (invertedOperandConditionSource "and" "c" "b" true false true false)
    Veir.Passes.InstCombineLLVM.SelectAndFalseArm.selectAndFalseArmAndSwapped none 2 (some 0)
  runSelect "select-L4027-not-left"
    (invertedOperandConditionSource "and" "c" "b" true true false false)
    Veir.Passes.InstCombineLLVM.SelectAndFalseArm.selectAndFalseArmNotLeft none 2 (some 0)
  runSelect "select-L4027-both-swapped"
    (invertedOperandConditionSource "and" "c" "b" true true true false)
    Veir.Passes.InstCombineLLVM.SelectAndFalseArm.selectAndFalseArmBothSwapped none 2 (some 0)
  runSelect "select-L4037-rr"
    (invertedOperandConditionSource "or" "c" "a" false false false false)
    Veir.Passes.InstCombineLLVM.SelectOrTrueArm.selectOrTrueArm none 2 (some 0)
  runSelect "select-L4037-op-swapped"
    (invertedOperandConditionSource "or" "c" "a" false false true false)
    Veir.Passes.InstCombineLLVM.SelectOrTrueArm.selectOrTrueArmOrSwapped none 2 (some 0)
  runSelect "select-L4037-not-left"
    (invertedOperandConditionSource "or" "c" "a" false true false false)
    Veir.Passes.InstCombineLLVM.SelectOrTrueArm.selectOrTrueArmNotLeft none 2 (some 0)
  runSelect "select-L4037-both-swapped-disjoint"
    (invertedOperandConditionSource "or" "c" "a" false true true true)
    Veir.Passes.InstCombineLLVM.SelectOrTrueArm.selectOrTrueArmBothSwapped none 2 (some 0)
  runSelect "select-L4045-rr"
    (invertedOperandConditionSource "and" "b" "c" false false false false)
    Veir.Passes.InstCombineLLVM.SelectAndNotFalse.selectAndNotFalse none 2 (some 0)
  runSelect "select-L4045-op-swapped"
    (invertedOperandConditionSource "and" "b" "c" false false true false)
    Veir.Passes.InstCombineLLVM.SelectAndNotFalse.selectAndNotFalseAndSwapped none 2 (some 0)
  runSelect "select-L4045-not-left"
    (invertedOperandConditionSource "and" "b" "c" false true false false)
    Veir.Passes.InstCombineLLVM.SelectAndNotFalse.selectAndNotFalseNotLeft none 2 (some 0)
  runSelect "select-L4045-both-swapped"
    (invertedOperandConditionSource "and" "b" "c" false true true false)
    Veir.Passes.InstCombineLLVM.SelectAndNotFalse.selectAndNotFalseBothSwapped none 2 (some 0)
  for andSelect in [false, true] do
    for orSelect in [false, true] do
      for notLeft in [false, true] do
        for outerSwapped in [false, true] do
          for orSwapped in [false, true] do
            let disjoint := !orSelect && andSelect && notLeft && outerSwapped && orSwapped
            runXorResult
              s!"select-L4011-{andSelect}-{orSelect}-{notLeft}-{outerSwapped}-{orSwapped}"
              (logicalXorSource andSelect orSelect notLeft outerSwapped orSwapped disjoint)
              (Veir.Passes.InstCombineLLVM.SelectLogicalXor.pattern
                andSelect orSelect notLeft outerSwapped orSwapped)

#guard regression = .ok ()
