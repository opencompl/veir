module

import Veir.Input
import Veir.Verifier
import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution
meta import Veir.Input
meta import Veir.Verifier
meta import Veir.PatternRewriter.Puddle.Builders
meta import Veir.PatternRewriter.Puddle.Execution
import all Veir.PatternRewriter.Puddle.Execution

open Veir Veir.Input Veir.Puddle

/-- The usual integer add-zero rewrite, with a concrete constant matcher and a forwarded operand. -/
private def addZero : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let value ← MatchProg.value type
      let zero ← MatchProg.operation (.arith .constant) #[] #[type]
        (fun properties => properties.intAttr?.any (·.value = 0))
      let _ ← MatchProg.root (.arith .addi) #[value, zero.res[0]!] #[type]
      return value)
    pure
    (fun value => value)

private def program : String := r#"
"builtin.module"() ({
  "func.func"() <{sym_name = "f", function_type = () -> i32}> ({
  ^entry:
    %entryzero = "arith.constant"() <{value = 0 : i32}> : () -> i32
    "func.return"(%entryzero) : (i32) -> ()
  ^dead:
    %left = "arith.constant"() <{value = 0 : i32}> : () -> i32
    %right = "arith.constant"() <{value = 0 : i32}> : () -> i32
    %sum = "arith.addi"(%left, %right) : (i32, i32) -> i32
    "func.return"(%sum) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
"#

/-- Build either an ordinary dead-block root or a cyclic one. Forward SSA uses are introduced
through the checked rewriter so the parser need not support textual self-reference. -/
private def fixture (cyclic : Bool) : Except String (WfIRContext OpCode × OperationPtr × OperationPtr) := do
  let (ctx, moduleOp, _) ← parseSourceString program.toUTF8
  let moduleBlock := ((moduleOp.getRegion! ctx.raw 0).getFirstBlock! ctx.raw).get!
  let function := (moduleBlock.getFirstOp! ctx.raw).get!
  let entry := ((function.getRegion! ctx.raw 0).getFirstBlock! ctx.raw).get!
  let dead := (entry.getNextBlock! ctx.raw).get!
  let left := (dead.getFirstOp! ctx.raw).get!
  let right := (left.getNextOp! ctx.raw).get!
  let root := (right.getNextOp! ctx.raw).get!
  let ctx := if cyclic then WfRewriter.replaceValue! ctx (left.getResult 0) (root.getResult 0) else ctx
  return (ctx, moduleOp, root)

/-- Verification deliberately permits cyclic SSA uses in unreachable blocks. The matcher can
therefore bind a fresh input handle to the root's own result pointer. The runtime guard must reject
this rewrite before any insertion or replacement happens. -/
private def cyclicRootRejected : Except String Bool := do
  let (ctx, moduleOp, root) ← fixture true
  ctx.verify moduleOp
  if root.getOperand! ctx.raw 0 != root.getResult 0 then return false
  let some matched := addZero.matcher.run ctx.raw root | return false
  let some (_created, newOps, assignment) := addZero.creation.run matched ctx | return false
  let some replacements := assignment.getValues addZero.replacement.values | return false
  if replacements != #[(root.getResult 0 : ValuePtr)] then return false
  if newOps != #[] then return false
  if hroot : root.InBounds ctx.raw then
    let before : PatternRewriter OpCode := { ctx, hasDoneAction := false, worklist := .empty }
    return (addZero.compile.run before root hroot).isNone
  else return false

/-- The same rewrite still succeeds on an ordinary root in the same unreachable block. -/
private def noncyclicRootRewritten : Except String Bool := do
  let (ctx, moduleOp, root) ← fixture false
  ctx.verify moduleOp
  if hroot : root.InBounds ctx.raw then
    let before : PatternRewriter OpCode := { ctx, hasDoneAction := false, worklist := .empty }
    let some after := addZero.compile.run before root hroot | return false
    after.ctx.verify moduleOp
    return after.hasDoneAction && !decide (root.InBounds after.ctx.raw)
  else return false

#guard cyclicRootRejected = .ok true
#guard noncyclicRootRewritten = .ok true
