import Veir.Passes.ArithCanonicalize.TD004
import Veir.Passes.ArithCanonicalize.TD017
import Veir.Passes.ArithCanonicalize.TD025
import Veir.Passes.ArithCanonicalize.G001
import Veir.PatternRewriter.Puddle.Execution
import Veir.Input

open Veir Veir.Input Veir.Puddle

private def parseBinaryProgram (source : String) : Option (WfIRContext OpCode) := do
  let (ctx, _, _) ← (parseSourceString source.toUTF8).toOption
  return ctx

private def findOp (ctx : IRContext OpCode) (opcode : OpCode) : Option OperationPtr :=
  ctx.operations.keys.find? (fun op => op.getOpType! ctx == opcode)

/-- Validity is conditional on matching. Check that the normalized signless i1
    spelling of all-ones actually matches the translations. -/
private def normalizedAllOnesMatches : String := Id.run do
  let some program := parseBinaryProgram r#""builtin.module"() ({
    %x = "arith.constant"() <{value = 0 : i1}> : () -> i1
    %y = "arith.constant"() <{value = 1 : i1}> : () -> i1
    %ones = "arith.constant"() <{value = -1 : i1}> : () -> i1
    %neg = "arith.muli"(%x, %ones) : (i1, i1) -> i1
    %root = "arith.addi"(%y, %neg) : (i1, i1) -> i1
    "test.test"(%root) : (i1) -> ()
  }) : () -> ()"# | return "parse failed"
  let rule := Pattern.compile ArithCanonicalize.TD004.pattern
  let some result := RewritePattern.applyInContext rule.run program
    | return "rewrite failed"
  if (findOp result.raw (.arith .addi)).isSome then
    return "all-ones i1 multiply-add did not match"
  if (findOp result.raw (.arith .subi)).isNone then
    return "missing replacement subtraction"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! normalizedAllOnesMatches

private def normalizedSelectComplementMatches : String := Id.run do
  let some program := parseBinaryProgram r#""builtin.module"() ({
    %c = "arith.constant"() <{value = 0 : i1}> : () -> i1
    %ones = "arith.constant"() <{value = -1 : i1}> : () -> i1
    %x = "arith.constant"() <{value = 42 : i8}> : () -> i8
    %y = "arith.constant"() <{value = 7 : i8}> : () -> i8
    %not = "arith.xori"(%c, %ones) : (i1, i1) -> i1
    %root = "arith.select"(%not, %x, %y) : (i1, i8, i8) -> i8
    "test.test"(%root) : (i8) -> ()
  }) : () -> ()"# | return "parse failed"
  let some original := findOp program.raw (.arith .select) | return "missing select"
  let some complement := findOp program.raw (.arith .xori) | return "missing complement"
  let c := complement.getOperand! program.raw 0
  let x := original.getOperand! program.raw 1
  let y := original.getOperand! program.raw 2
  let rule := Pattern.compile ArithCanonicalize.TD025.pattern
  let some result := RewritePattern.applyInContext rule.run program
    | return "rewrite failed"
  let some replacement := findOp result.raw (.arith .select) | return "missing replacement select"
  if replacement.getOperand! result.raw 0 != c ||
      replacement.getOperand! result.raw 1 != y ||
      replacement.getOperand! result.raw 2 != x then
    return "select complement did not match normalized i1 all-ones"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! normalizedSelectComplementMatches

/-- The commutative ordering rule must not keep swapping two constants. -/
private def twoConstantsKeepTheirOrder (rhsOpcode : String) : String := Id.run do
  let source := r#""builtin.module"() ({
    %x = "arith.constant"() <{value = 42 : i8}> : () -> i8
    %y = "arith.constant"() <{value = 7 : i8}> : () -> i8
    %root = "arith.addi"(%x, %y) : (i8, i8) -> i8
    "test.test"(%root) : (i8) -> ()
  }) : () -> ()"#
  let source := source.replace "%y = \"arith.constant\"" s!"%y = \"{rhsOpcode}\""
  let some program := parseBinaryProgram source | return "parse failed"
  let some original := findOp program.raw (.arith .addi) | return "missing add"
  let x := original.getOperand! program.raw 0
  let y := original.getOperand! program.raw 1
  let rule := Pattern.compile (ArithCanonicalize.G001.pattern .addi)
  let some result := RewritePattern.applyInContext rule.run program
    | return "rewrite failed"
  let some replacement := findOp result.raw (.arith .addi) | return "missing add after rewrite"
  if replacement.getOperand! result.raw 0 != x || replacement.getOperand! result.raw 1 != y then
    return "commutative rule reordered two constants"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! twoConstantsKeepTheirOrder "arith.constant"

/-- info: "ok" -/
#guard_msgs in
#eval! twoConstantsKeepTheirOrder "llvm.mlir.constant"

/-- The replacement needs a newly created i1 type. It cannot be an unbound
    match variable. The positive-one source guard also excludes i1 itself. -/
private def extendedMultiplyOneMatches (width : Nat) : String := Id.run do
  let source := r#""builtin.module"() ({
    %x = "arith.constant"() <{value = -1 : i8}> : () -> i8
    %one = "arith.constant"() <{value = 1 : i8}> : () -> i8
    %lo, %hi = "arith.mulsi_extended"(%x, %one) : (i8, i8) -> (i8, i8)
    "test.test"(%lo, %hi) : (i8, i8) -> ()
  }) : () -> ()"#
  let source := source.replace "i8" s!"i{width}"
  let some program := parseBinaryProgram source | return "parse failed"
  let rule := Pattern.compile ArithCanonicalize.TD017.pattern
  let some result := RewritePattern.applyInContext rule.run program
    | return "rewrite failed"
  if width == 1 then
    if (findOp result.raw (.arith .mulsi_extended)).isNone then
      return "incorrectly rewrote i1 negative one"
    return "ok"
  if (findOp result.raw (.arith .mulsi_extended)).isSome then
    return "positive-one extended multiply did not match"
  if (findOp result.raw (.arith .cmpi)).isNone ||
      (findOp result.raw (.arith .extsi)).isNone then
    return "missing signed high-half replacement"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! extendedMultiplyOneMatches 8

/-- info: "ok" -/
#guard_msgs in
#eval! extendedMultiplyOneMatches 1
