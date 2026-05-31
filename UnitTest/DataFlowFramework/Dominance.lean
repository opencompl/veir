import UnitTest.DataFlowFramework.Helpers

import Veir.Analysis.DataFlow.DominanceAnalysis

open Std (HashSet)
open Veir

/-- Expected dominance information for one named block in the test harness. -/
private structure ExpectedBlockDominators where
  name : String
  dominators : HashSet String

/--
Compare one expected dominator label against the observed dominance information.

This is the completeness half of the reachable block check: every expected
dominator must be observed.
-/
private def compareExpectedDominator
    (block : BlockPtr)
    (expectedDom : String)
    (recovered : RecoveredNames)
    (expected : ExpectedBlockDominators)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : MismatchReport := Id.run do
  let some expectedBlock := recovered.blocks[expectedDom]?
    | return #[s!"dominators {expected.name}: missing block label {expectedDom}"]
  let shouldProperlyDom := expectedDom ≠ expected.name
  let mut report := #[]
  if !Veir.DominanceAnalysis.dominates expectedBlock block dfCtx irCtx then
    report := report.push s!"dominators {expected.name}: missing expected dominator {expectedDom}"
  if Veir.DominanceAnalysis.properlyDominates expectedBlock block dfCtx irCtx ≠ shouldProperlyDom then
    report := report.push
      s!"dominators {expected.name}: unexpected properlyDominates result for {expectedDom}"
  return report

/--
Compare one observed block label against the expected dominator list.

This is the soundness half of the reachable block check: every observed
dominator must be expected.
-/
private def compareObservedDominator
    (block : BlockPtr)
    (observedName : String)
    (observedBlock : BlockPtr)
    (expected : ExpectedBlockDominators)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : MismatchReport := Id.run do
  let observedByRelation := Veir.DominanceAnalysis.dominates observedBlock block dfCtx irCtx
  let observedProperly := Veir.DominanceAnalysis.properlyDominates observedBlock block dfCtx irCtx
  let mut report := #[]
  if observedProperly ≠ (observedByRelation && observedBlock ≠ block) then
    report := report.push
      s!"dominators {expected.name}: dominates/properlyDominates disagree on {observedName}"
  if observedByRelation && !expected.dominators.contains observedName then
    report := report.push s!"dominators {expected.name}: unexpected dominator {observedName}"
  if observedProperly && (!expected.dominators.contains observedName || observedName = expected.name) then
    report := report.push s!"dominators {expected.name}: unexpected proper dominator {observedName}"
  report

/--
Compare the observed dominator information for one reachable block.

This runs both passes of the reachable block check: every expected dominator must
be observed, and every observed dominator must be expected.
-/
private def compareReachableDominators
    (block : BlockPtr)
    (recovered : RecoveredNames)
    (expected : ExpectedBlockDominators)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : MismatchReport := Id.run do
  let mut report := #[]
  for expectedDom in expected.dominators.toArray do
    report := report ++ compareExpectedDominator
      block expectedDom recovered expected dfCtx irCtx
  for (observedName, observedBlock) in recovered.blocks.toList do
    report := report ++ compareObservedDominator
      block observedName observedBlock expected dfCtx irCtx
  report

/--
Compare the observed dominator information for one named block.

An empty expected dominator set means the block should be unreachable and
therefore should not have an initialized dominator fact.
-/
private def compareNamedBlockDominators
    (recovered : RecoveredNames)
    (expected : ExpectedBlockDominators)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : MismatchReport := Id.run do
  let some block := recovered.blocks[expected.name]?
    | return #[s!"dominators {expected.name}: missing block label"]
  let observedFact? := block.getDominatorFact? dfCtx irCtx
  match expected.dominators.isEmpty, observedFact? with
  | true, none =>
      return #[]
  | true, some _ =>
      return #[s!"dominators {expected.name}: expected unreachable block, observed initialized state"]
  | false, none =>
      return #[s!"dominators {expected.name}: expected initialized state, observed unreachable block"]
  | false, some _ =>
      return compareReachableDominators block recovered expected dfCtx irCtx

/--
Compare the observed dominator relation against an expected map keyed by block
label.
-/
private def compareNamedDominators
    (recovered : RecoveredNames)
    (expectations : Array ExpectedBlockDominators)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : MismatchReport := Id.run do
  let mut report := #[]
  for expected in expectations do
    report := report ++ compareNamedBlockDominators recovered expected dfCtx irCtx
  report

namespace DominanceAnalysis

/--
Run the dominance analysis test harness on one MLIR snippet.

The expected data associates each block label with the full set of blocks that
should dominate it. An empty set means the block should remain unreachable.
-/
def run
    (mlir : String)
    (expected : Array ExpectedBlockDominators) : String :=
  runWithAnalyses mlir #[Veir.DominanceAnalysis] (fun top dfCtx parserState => Id.run do
    match recoverNames top parserState.ctx mlir with
    | Except.error err =>
        return #[err]
    | Except.ok recovered =>
        compareNamedDominators recovered expected dfCtx parserState.ctx)

/-
  Test: loop with a backedge
            ┌───┐
            │ 0 │
            └─┬─┘
              │
              │
            ┌─▼─┐
            │ 1 ◄──┐
            └─┬─┘  │
              │    │
              │    │
            ┌─▼─┐  │
            │ 2 ├──┘
            └───┘
-/
def testDomLoop : String :=
  run
    "\"builtin.module\"() ({\n\
^bb0:\n\
  \"test.test\"() [^bb1] : () -> ()\n\
^bb1:\n\
  \"test.test\"() [^bb2] : () -> ()\n\
^bb2:\n\
  \"test.test\"() [^bb1] : () -> ()\n\
}) : () -> ()"
    #[ { name := "bb0", dominators := { "bb0" } }
     , { name := "bb1", dominators := { "bb0", "bb1" } }
     , { name := "bb2", dominators := { "bb0", "bb1", "bb2" } }
     ]

/-
  Test: diamond
         ┌───┐
      ┌──┤ 0 ├──┐
      │  └───┘  │
    ┌─▼─┐     ┌─▼─┐
    │ 1 │     │ 2 │
    └─┬─┘     └─┬─┘
      │  ┌───┐  │
      └──► 3 ◄──┘
         └───┘
-/
def testDomDiamond : String :=
  run
    "\"builtin.module\"() ({\n\
^bb0:\n\
  \"test.test\"() [^bb1, ^bb2] : () -> ()\n\
^bb1:\n\
  \"test.test\"() [^bb3] : () -> ()\n\
^bb2:\n\
  \"test.test\"() [^bb3] : () -> ()\n\
^bb3:\n\
  \"test.test\"() : () -> ()\n\
}) : () -> ()"
    #[ { name := "bb0", dominators := { "bb0" } }
     , { name := "bb1", dominators := { "bb0", "bb1" } }
     , { name := "bb2", dominators := { "bb0", "bb2" } }
     , { name := "bb3", dominators := { "bb0", "bb3" } }
     ]

/-
  Test: straight line
        ┌───┐
        │ 0 │
        └─┬─┘
          │
        ┌─▼─┐
        │ 1 │
        └─┬─┘
          │
        ┌─▼─┐
        │ 2 │
        └─┬─┘
          │
        ┌─▼─┐
        │ 3 │
        └───┘
-/
def testDomLine : String :=
  run
    "\"builtin.module\"() ({\n\
^bb0:\n\
  \"test.test\"() [^bb1] : () -> ()\n\
^bb1:\n\
  \"test.test\"() [^bb2] : () -> ()\n\
^bb2:\n\
  \"test.test\"() [^bb3] : () -> ()\n\
^bb3:\n\
  \"test.test\"() : () -> ()\n\
}) : () -> ()"
    #[ { name := "bb0", dominators := { "bb0" } }
     , { name := "bb1", dominators := { "bb0", "bb1" } }
     , { name := "bb2", dominators := { "bb0", "bb1", "bb2" } }
     , { name := "bb3", dominators := { "bb0", "bb1", "bb2", "bb3" } }
     ]

/-
  Test: entry branches to a while-loop or to an if-statement, then join.
                      ┌───┐
                  ┌───┤ 0 ├───┐
                  │   └───┘   │
                ┌─▼─┐       ┌─▼─┐
              ┌─► 1 │    ┌──┤ 2 ├──┐
              │ └─┬─┘    │  └───┘  │
              │   │    ┌─▼─┐     ┌─▼─┐
              │ ┌─▼─┐  │ 3 │     │ 4 │
              └─┤ 5 │  └─┬─┘     └─┬─┘
                └─┬─┘    │  ┌───┐  │
                  │      └──► 6 ◄──┘
                  │         └─┬─┘
                  │   ┌───┐   │
                  └───► 7 ◄───┘
                      └───┘
-/
def testDomIfLoopIf : String :=
  run
    "\"builtin.module\"() ({\n\
^bb0:\n\
  \"test.test\"() [^bb1, ^bb2] : () -> ()\n\
^bb1:\n\
  \"test.test\"() [^bb5] : () -> ()\n\
^bb2:\n\
  \"test.test\"() [^bb3, ^bb4] : () -> ()\n\
^bb3:\n\
  \"test.test\"() [^bb6] : () -> ()\n\
^bb4:\n\
  \"test.test\"() [^bb6] : () -> ()\n\
^bb5:\n\
  \"test.test\"() [^bb1, ^bb7] : () -> ()\n\
^bb6:\n\
  \"test.test\"() [^bb7] : () -> ()\n\
^bb7:\n\
  \"test.test\"() : () -> ()\n\
}) : () -> ()"
    #[ { name := "bb0", dominators := { "bb0" } }
     , { name := "bb1", dominators := { "bb0", "bb1" } }
     , { name := "bb2", dominators := { "bb0", "bb2" } }
     , { name := "bb3", dominators := { "bb0", "bb2", "bb3" } }
     , { name := "bb4", dominators := { "bb0", "bb2", "bb4" } }
     , { name := "bb5", dominators := { "bb0", "bb1", "bb5" } }
     , { name := "bb6", dominators := { "bb0", "bb2", "bb6" } }
     , { name := "bb7", dominators := { "bb0", "bb7" } }
     ]

/--
info: "ok"
-/
#guard_msgs in
#eval! testDomLoop

/--
info: "ok"
-/
#guard_msgs in
#eval! testDomDiamond

/--
info: "ok"
-/
#guard_msgs in
#eval! testDomLine

/--
info: "ok"
-/
#guard_msgs in
#eval! testDomIfLoopIf

end DominanceAnalysis
