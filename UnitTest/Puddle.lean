import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution
import Veir.Parser.MlirParser
import Veir.Printer

open Veir
open Veir.Puddle
open Veir.Parser

/- ## Example patterns -/

/-- Match an arithmetic constant of a given value. -/
def matchConstant (returnType : Handle OpCode .type) (constant : Int)
    : MatchProg.Builder (Handle OpCode .value) := do
  let op ← MatchProg.operation (.arith .constant) #[] #[returnType]
    (fun properties => properties.value.value = constant)
  return op.res[0]!

/-- Rewrite `x + 0` to `x`. -/
private def addZero : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let cstVal ← matchConstant returnType 0
      let _ ← MatchProg.root (.arith .addi) #[x, cstVal] #[returnType]
      return x)
    pure
    (fun x => x)

/-- Rewrite `x * 2` to `x + x`. -/
private def mulTwo : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let cstVal ← matchConstant returnType 2
      let _ ← MatchProg.root (.arith .muli) #[x, cstVal] #[returnType]
      return (returnType, x))
    (fun (returnType, x) => do
      let properties ← CreateProg.property (.arith .addi)
        (default : propertiesOf (.arith .addi : OpCode))
      let add ← CreateProg.operation (.arith .addi) #[x, x] #[returnType] properties
      return add)
    (fun result => result)

/- ## Test pattern execution -/

private structure BinaryProgram where
  ctx : WfIRContext OpCode
  moduleOp : OperationPtr

/-- Parse a complete test module. -/
private def parseBinaryProgram (source : String) : Option BinaryProgram := do
  let (ctx, _) ← WfIRContext.create OpCode
  let parser ← (ParserState.fromInput source.toByteArray).toOption
  let (moduleOp, state, _) ←
    (Veir.Parser.parseTopLevelOp.run (MlirParserState.fromContext ctx) parser).toOption
  return ⟨state.ctx, moduleOp⟩

private def addZeroProgram := r#""builtin.module"() ({
  %input = "arith.constant"() <{ value = 42 : i32 }> : () -> i32
  %zero = "arith.constant"() <{ value = 0 : i32 }> : () -> i32
  %root = "arith.addi"(%input, %zero) : (i32, i32) -> i32
  "test.test"(%root) : (i32) -> ()
}) : () -> ()"#

private def mulTwoProgram := r#""builtin.module"() ({
  %input = "arith.constant"() <{ value = 42 : i32 }> : () -> i32
  %two = "arith.constant"() <{ value = 2 : i32 }> : () -> i32
  %root = "arith.muli"(%input, %two) : (i32, i32) -> i32
  "test.test"(%root) : (i32) -> ()
}) : () -> ()"#

/-- Parse a program, apply a compiled Puddle pattern, and print the resulting module. -/
private def rewriteAndPrint (source : String) (rule : Pattern OpCode) : IO Unit := do
  let some program := parseBinaryProgram source | IO.println "parse failed"
  let pattern := Pattern.compile rule
  let some ctx := RewritePattern.applyInContext pattern.run program.ctx | IO.println "rewrite failed"
  Printer.printModule ctx.raw program.moduleOp

/--
info: "builtin.module"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    "test.test"(%5) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint addZeroProgram addZero

/--
info: "builtin.module"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    %10 = "arith.addi"(%5, %5) : (i32, i32) -> i32
    "test.test"(%10) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint mulTwoProgram mulTwo
