import Veir.Verifier
import Veir.Printer
import Veir.Rewriter.WfRewriter

/-! Tests for printing into a `String` rather than to stdout.

`Printer.printModule` writes through `IO.print`; `printModuleToString` is the same printer with its
output collected. The property that matters is that they are *the same printer* -- a second
implementation that drifted would be worse than no second destination at all -- so both are pinned
against one expected text here, and the test fails if either moves.
-/

open Veir

private def i32 : TypeAttr := IntegerType.signless 32

/-- A `builtin.module` holding two `arith.constant`s, built rather than parsed. -/
private def twoConstants : WfIRContext OpCode × OperationPtr := Id.run do
  let (ctx, moduleOp) := WfIRContext.create! OpCode
  let region := moduleOp.getRegion! ctx.raw 0
  let block := (region.getFirstBlock! ctx.raw).get!
  let props : Veir.ArithConstantProperties := { value := IntegerAttr.mk 7 (IntegerType.signless 32) }
  let some (ctx, _) :=
      WfRewriter.createOp! ctx (OpCode.arith Arith.constant) #[i32] #[] #[] #[] props
        (some (.atEnd block))
    | (ctx, moduleOp)
  let props2 : Veir.ArithConstantProperties := { value := IntegerAttr.mk 8 (IntegerType.signless 32) }
  let some (ctx, _) :=
      WfRewriter.createOp! ctx (OpCode.arith Arith.constant) #[i32] #[] #[] #[] props2
        (some (.atEnd block))
    | (ctx, moduleOp)
  (ctx, moduleOp)

/--
info: "builtin.module"() ({
  ^2():
    %3 = "arith.constant"() <{"value" = 7 : i32}> : () -> i32
    %4 = "arith.constant"() <{"value" = 8 : i32}> : () -> i32
}) : () -> ()
-/
#guard_msgs in
#eval! do
  let (ctx, op) := twoConstants
  Printer.printModule ctx.raw op { printGenericOpForm := true }

-- The same text, collected into a `String` and printed by the test instead.
/--
info: "builtin.module"() ({
  ^2():
    %3 = "arith.constant"() <{"value" = 7 : i32}> : () -> i32
    %4 = "arith.constant"() <{"value" = 8 : i32}> : () -> i32
}) : () -> ()
-/
#guard_msgs in
#eval! do
  let (ctx, op) := twoConstants
  IO.print (← Printer.printModuleToString ctx.raw op { printGenericOpForm := true })

/-- Pinning both against the same docstring already forces them to agree, but only as long as
someone keeps the two docstrings in step. This compares them directly, under each printing option
-- the generic path and the custom-printer path call `printString` from different places, and a
sink threaded through only one of them would show up here. -/
private def testSinkMatchesStdout (options : PrinterOptions) : IO String := do
  let (ctx, op) := twoConstants
  let collected ← Printer.printModuleToString ctx.raw op options
  -- What `printModule` writes, captured the way a caller would have had to before
  -- `printModuleToString` existed.
  let buf ← IO.mkRef (IO.FS.Stream.Buffer.mk ⟨#[]⟩ 0)
  let written ← IO.withStdout (IO.FS.Stream.ofBuffer buf) do
    Printer.printModule ctx.raw op options
    let b ← buf.get
    return String.fromUTF8! b.data
  if collected.isEmpty then
    return "the sink collected nothing, so this compares two empty strings"
  if written != collected then
    return s!"the sink and stdout disagree:\n{written}\n---\n{collected}"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testSinkMatchesStdout { printGenericOpForm := true }

/-- info: "ok" -/
#guard_msgs in
#eval! testSinkMatchesStdout { printGenericOpForm := false }
