import UnitTest.DataFlowFramework.Helpers
import Veir.Analysis.DataFlow.SCCPRefinement

open Veir Veir.SCCP

/-!
Exercise the checker on actual joint-solver output, then corrupt one part of the
candidate at a time. These tests intentionally do not supply `TransfersSound`:
executable acceptance and the remaining semantic proof obligations are distinct.
-/

private def run (mlir : String)
    (test : WfIRContext OpCode → RecoveredNames → Candidate → Array BlockPtr → Array String) : String :=
  runWithAnalyses mlir #[Veir.DeadCodeAnalysis, Veir.SparseConstantPropagationAnalysis]
    fun root solver ctx => Id.run do
      let .ok names := recoverNames root ctx mlir | return #["name recovery failed"]
      let some entry := names.blocks["entry"]? | return #["entry not found"]
      let candidate := Candidate.ofDataFlow solver ctx
      if !checkFacts ctx candidate #[entry] then
        let diagnostic : Except String PUnit := ctx.raw.forOpsDepM fun op _ => do
          if operationLive ctx candidate op && !decide (OperationClosed ctx candidate op) then
            throw s!"op {repr (op.getOpType! ctx.raw)}: results {(resultUpdates ctx candidate op).size}/{op.getNumResults! ctx.raw}, regions {op.getNumRegions! ctx.raw}"
        return #[s!"solver output rejected; entry {decide (EntryClosed ctx candidate entry)}; {repr diagnostic}"]
      return test ctx names candidate #[entry]

private def setConstant (candidate : Candidate) (value : ValuePtr)
    (constant : AbstractConstant) : Candidate :=
  { candidate with constant := fun v => if v = value then constant else candidate.constant v }

private def integer (n : Nat) : AbstractConstant := .constant (.int 32 (.val (BitVec.ofNat 32 n)))

private def unknownBranch := r#""func.func"() <{sym_name = "f", function_type = (i1) -> i32}> ({
^entry(%condition : i1):
  %a = "arith.constant"() <{value = 5 : i32}> : () -> i32
  %b = "arith.constant"() <{value = 7 : i32}> : () -> i32
  "cf.cond_br"(%condition, %a, %b) [^left, ^right]
    <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
^left(%x : i32):
  "func.return"(%x) : (i32) -> ()
^right(%y : i32):
  "func.return"(%y) : (i32) -> ()
}) : () -> ()"#

private def testCorruptions : String :=
  run unknownBranch fun ctx names candidate entries => Id.run do
    let some entry := names.blocks["entry"]? | return #["missing entry"]
    let some left := names.blocks["left"]? | return #["missing left"]
    let some a := names.values["a"]? | return #["missing a"]
    let some x := names.values["x"]? | return #["missing x"]
    let some condition := names.values["condition"]? | return #["missing condition"]
    let mutations : Array (String × Candidate) := #[
      ("all bottom/dead", ⟨fun _ => .bottom, fun _ => false, fun _ _ => false⟩),
      ("dead entry", { candidate with blockLive := fun b => b != entry && candidate.blockLive b }),
      ("narrow entry argument", setConstant candidate condition (.constant (.int 1 (.val 0)))),
      ("wrong result", setConstant candidate a (integer 9)),
      ("missing result", setConstant candidate a .bottom),
      ("wrong forwarded argument", setConstant candidate x (integer 9)),
      ("missing edge", { candidate with edgeLive := fun s t =>
        !(s == entry && t == left) && candidate.edgeLive s t }),
      ("dead destination", { candidate with blockLive := fun b => b != left && candidate.blockLive b })
    ]
    let mut failures := #[]
    for (name, mutation) in mutations do
      if checkFacts ctx mutation entries then failures := failures.push s!"accepted {name}"
    -- A post-fixed point need not be the least result produced by the solver.
    let conservative : Candidate := ⟨fun _ => .top, fun _ => true, fun _ _ => true⟩
    if !checkFacts ctx conservative entries then failures := failures.push "rejected conservative facts"
    return failures

/-- info: "ok" -/
#guard_msgs in
#eval! testCorruptions

private def literalBranch := r#""func.func"() <{sym_name = "f", function_type = () -> i32}> ({
^entry:
  %condition = "arith.constant"() <{value = 1 : i1}> : () -> i1
  %a = "arith.constant"() <{value = 5 : i32}> : () -> i32
  %b = "arith.constant"() <{value = 7 : i32}> : () -> i32
  "cf.cond_br"(%condition, %a, %b) [^left, ^right]
    <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
^left(%x : i32):
  "func.return"(%x) : (i32) -> ()
^right(%y : i32):
  "func.return"(%y) : (i32) -> ()
}) : () -> ()"#

private def testRetainedEdgesAndWidening : String :=
  run literalBranch fun ctx names candidate entries => Id.run do
    let some entry := names.blocks["entry"]? | return #["missing entry"]
    let some right := names.blocks["right"]? | return #["missing right"]
    let some y := names.values["y"]? | return #["missing y"]
    let some condition := names.values["condition"]? | return #["missing condition"]
    -- Literal syntax must not override a widened candidate: its concretization
    -- includes both conditions, and the checker must require both edges.
    if checkFacts ctx (setConstant candidate condition .top) entries then
      return #["widened condition did not require the other edge"]
    -- An accumulated edge still propagates arguments even though today's branch
    -- transfer only selects left. This detects checking only selected edges.
    let retained := { candidate with
      edgeLive := fun s t => (s == entry && t == right) || candidate.edgeLive s t
      blockLive := fun b => b == right || candidate.blockLive b }
    if checkFacts ctx retained entries then return #["retained edge failed to propagate arguments"]
    let closed := setConstant retained y (integer 7)
    if !checkFacts ctx closed entries then return #["rejected closed retained edge"]
    if !checkFacts ctx (setConstant closed condition .top) entries then
      return #["rejected properly covered widened condition"]
    return #[]

/-- info: "ok" -/
#guard_msgs in
#eval! testRetainedEdgesAndWidening

private def duplicateSuccessors := r#""func.func"() <{sym_name = "f", function_type = (i1) -> i32}> ({
^entry(%condition : i1):
  %a = "arith.constant"() <{value = 5 : i32}> : () -> i32
  %b = "arith.constant"() <{value = 7 : i32}> : () -> i32
  "cf.cond_br"(%condition, %a, %b) [^join, ^join]
    <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
^join(%x : i32):
  "func.return"(%x) : (i32) -> ()
}) : () -> ()"#

private def testDuplicateSuccessors : String :=
  run duplicateSuccessors fun ctx names candidate entries => Id.run do
    let some x := names.values["x"]? | return #["missing x"]
    if checkFacts ctx (setConstant candidate x (integer 5)) entries then
      return #["missed second successor occurrence"]
    if checkFacts ctx (setConstant candidate x (integer 7)) entries then
      return #["missed first successor occurrence"]
    return #[]

/-- info: "ok" -/
#guard_msgs in
#eval! testDuplicateSuccessors

private def loop := r#""func.func"() <{sym_name = "swap", function_type = () -> (i32, i32)}> ({
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

private def testLoop : String :=
  run loop fun ctx names candidate entries => Id.run do
    let some x := names.values["x"]? | return #["missing x"]
    if checkFacts ctx (setConstant candidate x (integer 1)) entries then
      return #["missed loop-carried conflicting value"]
    return #[]

/-- info: "ok" -/
#guard_msgs in
#eval! testLoop

private def poisonJoin := r#""func.func"() <{sym_name = "f", function_type = (i1) -> i32}> ({
^entry(%condition : i1):
  %poison = "llvm.mlir.poison"() : () -> i32
  %defined = "arith.constant"() <{value = 5 : i32}> : () -> i32
  "cf.cond_br"(%condition, %poison, %defined) [^join, ^join]
    <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
^join(%x : i32):
  "func.return"(%x) : (i32) -> ()
}) : () -> ()"#

private def testPoisonJoin : String :=
  run poisonJoin fun ctx names candidate entries => Id.run do
    let some x := names.values["x"]? | return #["missing x"]
    if candidate.constant x != integer 5 then return #["poison did not join to the defined constant"]
    if checkFacts ctx (setConstant candidate x (.constant (.int 32 .poison))) entries then
      return #["accepted poison fact for defined incoming value"]
    return #[]

/-- info: "ok" -/
#guard_msgs in
#eval! testPoisonJoin

private def nestedFunctions := r#""builtin.module"() ({
^entry:
  "func.func"() <{sym_name = "f", function_type = (i32) -> i32}> ({
  ^functionEntry(%input : i32):
    "func.return"(%input) : (i32) -> ()
  }) : () -> ()
}) : () -> ()"#

private def testRegionInitialization : String :=
  run nestedFunctions fun ctx names candidate entries => Id.run do
    let some input := names.values["input"]? | return #["missing input"]
    if checkFacts ctx (setConstant candidate input (integer 5)) entries then
      return #["missed initialization of a nested function"]
    return #[]

/-- info: "ok" -/
#guard_msgs in
#eval! testRegionInitialization
