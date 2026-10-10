import Veir.Analysis.DataFlow.SCCPRefinement
import Veir.Input

open Veir Veir.Collecting

/-!
These tests construct actual reachability witnesses while executing parsed IR.
The loop exercises repeated dynamic bindings of the same SSA values and parallel
block-argument assignment. The UB test checks that collecting observations does
not require the enclosing block (or function) to return successfully.
-/

private def advance {ctx : WfIRContext OpCode} {initial : Entry ctx → Prop}
    (entry : Entry ctx) (reachable : Reachable initial entry) :
    Option { next : Entry ctx // Reachable initial next } := do
  match executed : entry.run with
  | .ok (state, .branch arguments destination) =>
      if destinationIn : destination.InBounds ctx.raw then
        let next : Entry ctx := ⟨destination, arguments, state, destinationIn⟩
        return ⟨next, .step reachable (.branch executed destinationIn)⟩
      else none
  | _ => none

private structure Observation {ctx : WfIRContext OpCode} (initial : Entry ctx → Prop) where
  entry : Entry ctx
  reachable : Reachable initial entry
  op : OperationPtr
  opIn : op.InBounds ctx.raw
  state : InterpreterState ctx
  atOp : AtOperation entry op state

private def observeEntry {ctx : WfIRContext OpCode} {initial : Entry ctx → Prop}
    (entry : Entry ctx) (reachable : Reachable initial entry) : Option (Observation initial) := do
  match bound : entry.state.variables.setArgumentValues? entry.block entry.arguments entry.inBounds with
  | none => none
  | some variables =>
    match first : (entry.block.get! ctx.raw).firstOp with
    | none => none
    | some op =>
      if opIn : op.InBounds ctx.raw then
        return ⟨entry, reachable, op, opIn, ⟨variables, entry.state.memory⟩,
          ⟨variables, op, bound, first, .refl _ _⟩⟩
      else none

private def Observation.next {ctx : WfIRContext OpCode} {initial : Entry ctx → Prop}
    (current : Observation initial) : Option (Observation initial) := do
  match executed : interpretOp current.op current.state current.opIn with
  | .ok (state, none) =>
    match successor : (current.op.get! ctx.raw).next with
    | none => none
    | some op =>
      if opIn : op.InBounds ctx.raw then
        return ⟨current.entry, current.reachable, op, opIn, state, by
          obtain ⟨variables, first, bound, firstOp, hp⟩ := current.atOp
          exact ⟨variables, first, bound, firstOp, .next hp current.opIn executed successor⟩⟩
      else none
  | _ => none

private theorem Observation.observes {ctx : WfIRContext OpCode} {initial : Entry ctx → Prop}
    (observation : Observation initial) {value runtime}
    (bound : observation.state.variables.getVar? value = some runtime) :
    Values initial value runtime :=
  ⟨observation.op, observation.state,
    ⟨observation.entry, observation.reachable, observation.atOp⟩, bound⟩

private def loopIR := r#""func.func"() <{sym_name = "swap", function_type = () -> (i32, i32)}> ({
^entry:
  %a = "arith.constant"() <{value = 1 : i32}> : () -> i32
  %b = "arith.constant"() <{value = 2 : i32}> : () -> i32
  %yes = "arith.constant"() <{value = 1 : i1}> : () -> i1
  "cf.br"(%a, %b, %yes) [^loop] : (i32, i32, i1) -> ()
^loop(%x : i32, %y : i32, %again : i1):
  %no = "arith.constant"() <{value = 0 : i1}> : () -> i1
  "cf.cond_br"(%again, %y, %x, %no, %x, %y) [^loop, ^exit]
    <{operandSegmentSizes = array<i32: 1, 3, 2>}> : (i1, i32, i32, i1, i32, i32) -> ()
^exit(%resultX : i32, %resultY : i32):
  "func.return"(%resultX, %resultY) : (i32, i32) -> ()
}) : () -> ()"#

private def testLoop : String := Id.run do
  let .ok (ctx, root, _) := Input.parseSourceString loopIR.toUTF8 | return "parse failed"
  let some function := FunctionOp.of? root ctx.raw | return "missing function"
  let some block := function.getEntryBlock? | return "missing entry"
  if blockIn : block.InBounds ctx.raw then
    let entry : Entry ctx := ⟨block, #[], .empty ctx, blockIn⟩
    let initial := fun candidate => candidate = entry
    let reached : Reachable initial entry := .initial rfl
    let some first := advance entry reached | return "entry did not branch"
    let some second := advance first.val first.property | return "loop did not take backedge"
    if first.val.block ≠ second.val.block then return "backedge changed block"
    let some before := observeEntry first.val first.property | return "first argument binding failed"
    let some after := observeEntry second.val second.property | return "second argument binding failed"
    let x := first.val.block.getArgument 0
    let y := first.val.block.getArgument 1
    if before.state.variables.getVar? x ≠ some (.int 32 (.val 1)) then return "first x is not 1"
    if after.state.variables.getVar? x ≠ some (.int 32 (.val 2)) then return "second x is not 2"
    if after.state.variables.getVar? y ≠ some (.int 32 (.val 1)) then return "arguments were not swapped simultaneously"
    let some exit := advance second.val second.property | return "loop did not exit"
    match exit.val.run with
    | .ok (_, .return values) =>
      if values ≠ #[.int 32 (.val 2), .int 32 (.val 1)] then return "incorrect return"
      match completed : interpretBlockCFG entry.block entry.arguments entry.state entry.inBounds with
      | .ok (state, results) =>
        -- Adequacy constructs a returning execution witness from the original
        -- entry, including both visits to the loop block.
        let _execution : Executes entry state results :=
          (executes_iff_interpretBlockCFG entry state results).mpr completed
        if results ≠ values then return "CFG execution disagreed with the traversed path"
        return "ok"
      | _ => return "whole CFG did not return"
    | _ => return "exit did not return"
  else return "entry out of bounds"

/-- info: "ok" -/
#guard_msgs in
#eval! testLoop

private def ubIR := r#""func.func"() <{sym_name = "before_ub", function_type = () -> i32}> ({
^entry:
  %five = "arith.constant"() <{value = 5 : i32}> : () -> i32
  %zero = "arith.constant"() <{value = 0 : i32}> : () -> i32
  %bad = "arith.divsi"(%five, %zero) : (i32, i32) -> i32
  "func.return"(%bad) : (i32) -> ()
}) : () -> ()"#

private def testBeforeUB : String := Id.run do
  let .ok (ctx, root, _) := Input.parseSourceString ubIR.toUTF8 | return "parse failed"
  let some function := FunctionOp.of? root ctx.raw | return "missing function"
  let some block := function.getEntryBlock? | return "missing entry"
  if blockIn : block.InBounds ctx.raw then
    let entry : Entry ctx := ⟨block, #[], .empty ctx, blockIn⟩
    let initial := fun candidate => candidate = entry
    let some first := observeEntry entry (Reachable.initial (initial := initial) rfl)
      | return "could not enter"
    let some second := first.next | return "first constant failed"
    let some division := second.next | return "second constant failed"
    let five := first.op.getResult 0
    match observed : division.state.variables.getVar? five with
    | some runtime =>
      -- The observation really belongs to the collecting semantics, even though
      -- the complete block cannot produce an ordinary result.
      let _collected : Values initial five runtime := division.observes observed
      if runtime ≠ .int 32 (.val 5) then return "wrong collected value"
      match entry.run with
      | .ub _ => return "ok"
      | _ => return "division did not trigger UB"
    | none => return "constant disappeared before UB"
  else return "entry out of bounds"

/-- info: "ok" -/
#guard_msgs in
#eval! testBeforeUB

/-- The semantic certificate is satisfiable for every program and initial set:
all values at top and all control flow live is a sound (imprecise) analysis. -/
private def pessimistic : SCCP.Facts := ⟨fun _ => .top, fun _ => True, fun _ _ => True⟩

private theorem pessimisticValid {ctx : WfIRContext OpCode} (initial : Entry ctx → Prop) :
    pessimistic.Valid initial where
  initial := by simp [pessimistic, SCCP.Facts.CoversEntry, SCCP.Facts.CoversState, AbstractConstant.γ]
  operation := by simp [pessimistic, SCCP.Facts.CoversState, AbstractConstant.γ]
  branch := by simp [pessimistic, SCCP.Facts.CoversEntry, SCCP.Facts.CoversState, AbstractConstant.γ]

example {ctx : WfIRContext OpCode} (initial : Entry ctx → Prop) : pessimistic.Sound initial :=
  SCCP.facts_sound (pessimisticValid initial)
