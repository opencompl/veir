import UnitTest.DataFlowFramework.Helpers

import Veir.Analysis.DataFlow.DominanceAnalysis

open Std (HashMap HashSet)
open Veir

/--
Compare one expected dominator label against the observed dominance information.

This checks `dominates`, `strictlyDominates`, and membership in the dominator
set returned by `BlockPtr.getDoms?`.
-/
private def compareExpectedDominator
    (name : String)
    (block : BlockPtr)
    (observedDoms : HashSet BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode)
    (blockMap : HashMap String BlockPtr)
    (expectedDom : String) : MismatchReport :=
  match blockMap[expectedDom]? with
  | none =>
    #[s!"dominators {name}: missing block label {expectedDom}"]
  | some expectedBlock =>
    Id.run do
      let shouldStrictlyDom := expectedDom ≠ name
      let mut report := #[]
      if !Veir.DominanceAnalysis.dominates expectedBlock block dfCtx irCtx then
        report := report.push s!"dominators {name}: missing expected dominator {expectedDom}"
      if !observedDoms.contains expectedBlock then
        report := report.push
          s!"dominators {name}: BlockPtr.getDoms? missing expected dominator {expectedDom}"
      if Veir.DominanceAnalysis.strictlyDominates expectedBlock block dfCtx irCtx != shouldStrictlyDom then
        report := report.push
          s!"dominators {name}: unexpected strictlyDominates result for {expectedDom}"
      report

/--
Compare one observed block label against the expected dominator list.

This also cross checks the three ways of observing dominance for consistency:
`dominates`, `strictlyDominates`, and membership in `BlockPtr.getDoms?`.
-/
private def compareObservedDominator
    (name : String)
    (block : BlockPtr)
    (observedDoms : HashSet BlockPtr)
    (expectedDoms : Array String)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode)
    (observedName : String)
    (observedBlock : BlockPtr) : MismatchReport :=
  Id.run do
    let observedByRelation := Veir.DominanceAnalysis.dominates observedBlock block dfCtx irCtx
    let observedBySet := observedDoms.contains observedBlock
    let observedStrictly := Veir.DominanceAnalysis.strictlyDominates observedBlock block dfCtx irCtx
    let mut report := #[]
    if observedByRelation != observedBySet then
      report := report.push s!"dominators {name}: dominates/getDoms? disagree on {observedName}"
    if observedStrictly != (observedByRelation && observedBlock ≠ block) then
      report := report.push s!"dominators {name}: dominates/strictlyDominates disagree on {observedName}"
    if observedByRelation && !expectedDoms.contains observedName then
      report := report.push s!"dominators {name}: unexpected dominator {observedName}"
    if observedBySet && !expectedDoms.contains observedName then
      report := report.push s!"dominators {name}: BlockPtr.getDoms? has unexpected dominator {observedName}"
    if observedStrictly && (!expectedDoms.contains observedName || observedName = name) then
      report := report.push s!"dominators {name}: unexpected strict dominator {observedName}"
    report

/--
Compare the observed dominator information for one reachable block.

This runs both passes of the reachable block check: every expected dominator must
be observed, and every observed dominator must be expected.
-/
private def compareReachableDominators
    (name : String)
    (block : BlockPtr)
    (observedDoms : HashSet BlockPtr)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode)
    (blockMap : HashMap String BlockPtr)
    (expectedDoms : Array String) : MismatchReport := Id.run do
  let mut report := #[]
  for expectedDom in expectedDoms do
    report := report ++ compareExpectedDominator
      name block observedDoms dfCtx irCtx blockMap expectedDom
  for (observedName, observedBlock) in blockMap.toList do
    report := report ++ compareObservedDominator
      name block observedDoms expectedDoms dfCtx irCtx observedName observedBlock
  report

/--
Compare the observed dominator information for one named block.

An expected value of `none` means the block should be unreachable and therefore
should not have an initialized dominator set.
-/
private def compareNamedBlockDominators
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode)
    (blockMap : HashMap String BlockPtr)
    (name : String)
    (expectedDoms? : Option (Array String)) : MismatchReport :=
  match blockMap[name]? with
  | none =>
    #[s!"dominators {name}: missing block label"]
  | some block =>
    let observedDoms? := block.getDoms? dfCtx irCtx
    match expectedDoms? with
    | none =>
      if observedDoms?.isSome then
        #[s!"dominators {name}: expected unreachable block, observed initialized state"]
      else
        #[]
    | some expectedDoms =>
      match observedDoms? with
      | none =>
        #[s!"dominators {name}: expected initialized state, observed none"]
      | some observedDoms =>
        compareReachableDominators name block observedDoms dfCtx irCtx blockMap expectedDoms

/--
Compare the observed dominator relation against an expected map keyed by block
label.
-/
private def compareNamedDominators
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode)
    (blockMap : HashMap String BlockPtr)
    (expected : Array (String × Option (Array String))) : MismatchReport := Id.run do
  let mut report := #[]
  for (name, expectedDoms?) in expected do
    report := report ++ compareNamedBlockDominators dfCtx irCtx blockMap name expectedDoms?
  report

namespace DominanceAnalysis

/--
Run the dominance analysis test harness on one MLIR snippet.

The expected data associates each block label with either the full set of blocks
that should dominate it, or `none` if the block should remain unreachable.
-/
def run
    (mlir : String)
    (expected : Array (String × Option (Array String))) : String :=
  runWithAnalyses mlir #[Veir.DominanceAnalysis] (fun top dfCtx parserState => Id.run do
    let some recovered := recoverNames? top parserState.ctx mlir
      | return #["failed to recover block/value names from MLIR"]
    compareNamedDominators dfCtx parserState.ctx recovered.blocks expected)

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
    #[ ("bb0", some #["bb0"])
     , ("bb1", some #["bb0", "bb1"])
     , ("bb2", some #["bb0", "bb1", "bb2"])
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
    #[ ("bb0", some #["bb0"])
     , ("bb1", some #["bb0", "bb1"])
     , ("bb2", some #["bb0", "bb2"])
     , ("bb3", some #["bb0", "bb3"])
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
    #[ ("bb0", some #["bb0"])
     , ("bb1", some #["bb0", "bb1"])
     , ("bb2", some #["bb0", "bb1", "bb2"])
     , ("bb3", some #["bb0", "bb1", "bb2", "bb3"])
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
    #[ ("bb0", some #["bb0"])
     , ("bb1", some #["bb0", "bb1"])
     , ("bb2", some #["bb0", "bb2"])
     , ("bb3", some #["bb0", "bb2", "bb3"])
     , ("bb4", some #["bb0", "bb2", "bb4"])
     , ("bb5", some #["bb0", "bb1", "bb5"])
     , ("bb6", some #["bb0", "bb2", "bb6"])
     , ("bb7", some #["bb0", "bb7"])
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
