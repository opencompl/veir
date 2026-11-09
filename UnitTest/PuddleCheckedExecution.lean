module

import Veir.Input
import Veir.Verifier
import Veir.PatternRewriter.Puddle.CheckedExecution
import Veir.PatternRewriter.Puddle.Builders
meta import Veir.Input
meta import Veir.Verifier
meta import Veir.PatternRewriter.Puddle.CheckedExecution
meta import Veir.PatternRewriter.Puddle.Builders
meta import Veir.Dialects.Builtin.OpInfo
import all Veir.PatternRewriter.Basic

open Veir Veir.Input Veir.Puddle

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
  %graph = "arith.constant"() <{value = 7 : i32}> : () -> i32
  "func.func"() <{sym_name = "f", function_type = () -> i32}> ({
  ^entry:
    %value = "arith.constant"() <{value = 42 : i32}> : () -> i32
    %zero = "arith.constant"() <{value = 0 : i32}> : () -> i32
    %sum = "arith.addi"(%value, %zero) : (i32, i32) -> i32
    "func.return"(%sum) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
"#

private def fixture : Except String (WfIRContext OpCode × OperationPtr × OperationPtr × OperationPtr × OperationPtr) := do
  let (ctx, moduleOp, _) ← parseSourceString program.toUTF8
  ctx.verify moduleOp
  let moduleBlock := ((moduleOp.getRegion! ctx.raw 0).getFirstBlock! ctx.raw).get!
  let graph := (moduleBlock.getFirstOp! ctx.raw).get!
  let function := (graph.getNextOp! ctx.raw).get!
  let entry := ((function.getRegion! ctx.raw 0).getFirstBlock! ctx.raw).get!
  let value := (entry.getFirstOp! ctx.raw).get!
  let zero := (value.getNextOp! ctx.raw).get!
  let sum := (zero.getNextOp! ctx.raw).get!
  return (ctx, moduleOp, graph, function, sum)

/-- A deliberately failing pattern detects accidental execution; an allocating or pure dead
operation also detects accidental dispatch to automatic DCE. Unsupported roots must simply pop. -/
private def skipped (ctx : WfIRContext OpCode) (moduleOp op : OperationPtr) : Bool := Id.run do
  let pattern : RewritePattern OpCode := fun _ _ _ => none
  let before : PatternRewriter OpCode :=
    { ctx, hasDoneAction := true, worklist := PatternRewriter.Worklist.empty.push op }
  let some after := pattern.worklistStepIf (rootEligible moduleOp) before | return false
  return decide (op.InBounds after.ctx.raw) && after.hasDoneAction && after.worklist.isEmpty

private def unsupportedPlacementsSkipped : Except String Bool := do
  let (ctx, moduleOp, graph, function, sum) ← fixture
  if !rootEligible moduleOp ctx sum then return false
  if !skipped ctx moduleOp graph || !skipped ctx moduleOp function || !skipped ctx moduleOp moduleOp then
    return false
  let (ctx, detached) := (WfRewriter.createOp! ctx Test.test #[] #[] #[] #[] () none).get!
  if !skipped ctx moduleOp detached then return false
  let (ctx, region) := WfRewriter.createRegion! ctx
  let (ctx, _) := WfRewriter.createBlock! ctx #[] (some (.atEnd region))
  let (ctx, otherModule) := (WfRewriter.createOp! ctx Builtin.module #[] #[] #[] #[region]
    (default : ModuleProperties) none).get!
  if rootEligible otherModule ctx sum then return false
  return skipped ctx otherModule sum

private def validSSARewriteExecutes : Except String Bool := do
  let (ctx, moduleOp, graph, function, sum) ← fixture
  let some after := applyInModule #[addZero] ctx moduleOp 1 | return false
  after.verify moduleOp
  return decide (graph.InBounds after.raw) && decide (function.InBounds after.raw) &&
    !decide (sum.InBounds after.raw)

private def functionWiseRewriteExecutes : Except String Bool := do
  let (ctx, moduleOp, graph, function, sum) ← fixture
  let some after := applyToFunctionsInModule #[addZero] ctx moduleOp 1 | return false
  after.verify moduleOp
  return decide (graph.InBounds after.raw) && decide (function.InBounds after.raw) &&
    !decide (sum.InBounds after.raw)

#guard unsupportedPlacementsSkipped = .ok true
#guard validSSARewriteExecutes = .ok true
#guard functionWiseRewriteExecutes = .ok true
