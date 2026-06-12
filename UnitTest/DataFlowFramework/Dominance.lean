import UnitTest.DataFlowFramework.Helpers

import Veir.Analysis.DataFlow.DominanceAnalysis
import Veir.IR.Dominance

open Std (HashSet)
open Veir

/-- Expected dominance information for one named block in the test harness. -/
private structure ExpectedBlockDominators where
  name : String
  dominators : HashSet String
  iDom : String

/-- Expected dominance result for one pair of named operations. -/
private structure ExpectedOperationDominance where
  dominator : String
  dominated : String
  dominates : Bool
  properlyDominates : Bool

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
  if !expectedBlock.dominates block dfCtx irCtx then
    report := report.push s!"dominators {expected.name}: missing expected dominator {expectedDom}"
  if expectedBlock.properlyDominates block dfCtx irCtx ≠ shouldProperlyDom then
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
  let observedByRelation := observedBlock.dominates block dfCtx irCtx
  let observedProperly := observedBlock.properlyDominates block dfCtx irCtx
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
Compare `BlockPtr.immediateDominator?` against the expected block label.
-/
private def compareImmediateDominator
    (recovered : RecoveredNames)
    (expected : ExpectedBlockDominators)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : MismatchReport := Id.run do
  let some block := recovered.blocks[expected.name]?
    | return #[s!"idom {expected.name}: missing block label"]
  let some observedIDom := block.immediateDominator? dfCtx irCtx
    | return #[s!"idom {expected.name}: expected immediate dominator {expected.iDom}, observed none"]
  let some expectedIDom := recovered.blocks[expected.iDom]?
    | return #[s!"idom {expected.name}: missing block label {expected.iDom}"]
  if observedIDom = expectedIDom then
    return #[]
  let observedName :=
    (recovered.blocks.toList.findSome? fun (name, block) =>
      if block = observedIDom then some name else none).getD "none"
  return #[s!"idom {expected.name}: expected {expected.iDom}, observed {observedName}"]

/--
Compare the observed dominator information against the
expected dominator information for one reachable block.

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
Compare the observed dominator information against the
expected dominator information for one named block.

An empty expected dominator set means the block should be unreachable and
therefore should not have an initialized dominator fact.
-/
private def compareDominators
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
    report := report ++ compareDominators recovered expected dfCtx irCtx
    report := report ++ compareImmediateDominator recovered expected dfCtx irCtx
  report

/-- Resolve a named SSA value to the operation that defines it. -/
private def getNamedOperation?
    (recovered : RecoveredNames)
    (name : String)
    (irCtx : IRContext OpCode) : Option OperationPtr := do
  let value ← recovered.values[name]?
  value.getDefiningOp! irCtx

/--
Compare one expected operation dominance relation.
-/
private def compareOperationDominance
    (recovered : RecoveredNames)
    (expected : ExpectedOperationDominance)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : MismatchReport := Id.run do
  let some dominator := getNamedOperation? recovered expected.dominator irCtx
    | return #[s!"op dominance {expected.dominator}->{expected.dominated}: missing dominator"]
  let some dominated := getNamedOperation? recovered expected.dominated irCtx
    | return #[s!"op dominance {expected.dominator}->{expected.dominated}: missing dominated op"]

  let observedDominates := dominator.dominates dominated dfCtx irCtx
  let observedProperly := dominator.properlyDominates dominated dfCtx irCtx
  let mut report := #[]
  if observedDominates ≠ expected.dominates then
    report := report.push
      s!"op dominance {expected.dominator}->{expected.dominated}: expected dominates={expected.dominates}, observed {observedDominates}"
  if observedProperly ≠ expected.properlyDominates then
    report := report.push
      s!"op dominance {expected.dominator}->{expected.dominated}: expected properlyDominates={expected.properlyDominates}, observed {observedProperly}"
  if observedProperly && !observedDominates then
    report := report.push
      s!"op dominance {expected.dominator}->{expected.dominated}: properlyDominates without dominates"
  report

/--
Compare the observed operation dominance relation against an expected list keyed
by SSA result names.
-/
private def compareNamedOperationDominance
    (recovered : RecoveredNames)
    (expectations : Array ExpectedOperationDominance)
    (dfCtx : DataFlowContext)
    (irCtx : IRContext OpCode) : MismatchReport := Id.run do
  let mut report := #[]
  for expected in expectations do
    report := report ++ compareOperationDominance recovered expected dfCtx irCtx
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

/--
Run the operation dominance test harness on one MLIR snippet.

Operations are referenced by the SSA names of one of their results.
-/
def runOperationDominance
    (mlir : String)
    (expected : Array ExpectedOperationDominance) : String :=
  runWithAnalyses mlir #[Veir.DominanceAnalysis] (fun top dfCtx parserState => Id.run do
    match recoverNames top parserState.ctx mlir with
    | Except.error err =>
        return #[err]
    | Except.ok recovered =>
        compareNamedOperationDominance recovered expected dfCtx parserState.ctx)

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
    #[ { name := "bb0", dominators := { "bb0" },               iDom := "bb0" }
     , { name := "bb1", dominators := { "bb0", "bb1" },        iDom := "bb0" }
     , { name := "bb2", dominators := { "bb0", "bb1", "bb2" }, iDom := "bb1" }
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
    #[ { name := "bb0", dominators := { "bb0" },        iDom := "bb0" }
     , { name := "bb1", dominators := { "bb0", "bb1" }, iDom := "bb0" }
     , { name := "bb2", dominators := { "bb0", "bb2" }, iDom := "bb0" }
     , { name := "bb3", dominators := { "bb0", "bb3" }, iDom := "bb0" }
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
    #[ { name := "bb0", dominators := { "bb0" },                      iDom := "bb0" }
     , { name := "bb1", dominators := { "bb0", "bb1" },               iDom := "bb0" }
     , { name := "bb2", dominators := { "bb0", "bb1", "bb2" },        iDom := "bb1" }
     , { name := "bb3", dominators := { "bb0", "bb1", "bb2", "bb3" }, iDom := "bb2" }
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
    #[ { name := "bb0", dominators := { "bb0" },               iDom := "bb0" }
     , { name := "bb1", dominators := { "bb0", "bb1" },        iDom := "bb0" }
     , { name := "bb2", dominators := { "bb0", "bb2" },        iDom := "bb0" }
     , { name := "bb3", dominators := { "bb0", "bb2", "bb3" }, iDom := "bb2" }
     , { name := "bb4", dominators := { "bb0", "bb2", "bb4" }, iDom := "bb2" }
     , { name := "bb5", dominators := { "bb0", "bb1", "bb5" }, iDom := "bb1" }
     , { name := "bb6", dominators := { "bb0", "bb2", "bb6" }, iDom := "bb2" }
     , { name := "bb7", dominators := { "bb0", "bb7" },        iDom := "bb0" }
     ]

/-
  Test: nested sibling regions inside the same outer block.

          ┌───────────────┐
          │ ┌───┐   ┌───┐ │
          │ │ 1 │ 0 │ 2 │ │
          │ └───┘   └───┘ │
          └───────────────┘

  The outer block dominates both nested entry blocks, but sibling nested blocks
  do not dominate each other.
-/
def testDomNestedRegions : String :=
  run r#""builtin.module"() ({
^bb0:
  "test.test"() ({
  ^bb1:
    "test.test"() : () -> ()
  }) : () -> ()
  "test.test"() ({
  ^bb2:
    "test.test"() : () -> ()
  }) : () -> ()
}) : () -> ()"#
    #[ { name := "bb0", dominators := { "bb0" },        iDom := "bb0" }
     , { name := "bb1", dominators := { "bb0", "bb1" }, iDom := "bb1" }
     , { name := "bb2", dominators := { "bb0", "bb2" }, iDom := "bb2" }
     ]

/-
  Test: diamond, nested region inside the join block.
            ┌───┐
        ┌───┤ 0 ├───┐
        │   └───┘   │
      ┌─▼─┐       ┌─▼─┐
      │ 1 │       │ 2 │
      └─┬─┘       └─┬─┘
        │ ┌───────┐ │
        │ │   3   │ │
        │ │ ┌───┐ │ │
        └─► │ 4 │ ◄─┘
          │ └───┘ │
          └───────┘
-/
def testDomDiamondNestedJoin : String :=
  run r#""builtin.module"() ({
^bb0:
  "test.test"() [^bb1, ^bb2] : () -> ()
^bb1:
  "test.test"() [^bb3] : () -> ()
^bb2:
  "test.test"() [^bb3] : () -> ()
^bb3:
  "test.test"() ({
^bb4:
    "test.test"() : () -> ()
  }) : () -> ()
}) : () -> ()"#
    #[ { name := "bb0", dominators := { "bb0" },               iDom := "bb0" }
     , { name := "bb1", dominators := { "bb0", "bb1" },        iDom := "bb0" }
     , { name := "bb2", dominators := { "bb0", "bb2" },        iDom := "bb0" }
     , { name := "bb3", dominators := { "bb0", "bb3" },        iDom := "bb0" }
     , { name := "bb4", dominators := { "bb0", "bb3", "bb4" }, iDom := "bb4" }
     ]

/-
  Test: two levels of nesting.
        ┌───────────┐
        │     0     │
        │ ┌───────┐ │
        │ │   1   │ │
        │ │ ┌───┐ │ │
        │ │ │ 2 │ │ │
        │ │ └───┘ │ │
        │ └───────┘ │
        └───────────┘
-/
def testDomTwoLevelNested : String :=
  run r#""builtin.module"() ({
^bb0:
  "test.test"() : () -> ()
  "test.test"() ({
^bb1:
    "test.test"() : () -> ()
    "test.test"() ({
^bb2:
      "test.test"() : () -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()"#
    #[ { name := "bb0", dominators := { "bb0" },               iDom := "bb0" }
     , { name := "bb1", dominators := { "bb0", "bb1" },        iDom := "bb1" }
     , { name := "bb2", dominators := { "bb0", "bb1", "bb2" }, iDom := "bb2" }
     ]
/-
  Test: Diamond with a loop
  ┌────────┐
  │      ┌─▼─┐
  │   ┌──┤ 0 ├──┐
  │   │  └───┘  │
  │ ┌─▼─┐     ┌─▼─┐
  │ │ 1 │     │ 2 ├──┐
  │ └─┬─┘     └─┬─┘  │
  │   │  ┌───┐  │  ┌─▼─┐
  │   └──► 3 ◄──┘  │ 4 │
  │      └─┬─┘     └───┘
  └────────┘
-/
def testDomDiamondLoop: String :=
  run r#""builtin.module"() ({
^bb0:
  "test.test"() [^bb1, ^bb2] : () -> ()
^bb1:
  "test.test"() [^bb3] : () -> ()
^bb2:
  "test.test"() [^bb3, ^bb4] : () -> ()
^bb3:
  "test.test"() [^bb0] : () -> ()
^bb4:
  "test.test"() : () -> ()
}) : () -> ()"#
    #[ { name := "bb0", dominators := { "bb0" },               iDom := "bb0" }
     , { name := "bb1", dominators := { "bb0", "bb1" },        iDom := "bb0" }
     , { name := "bb2", dominators := { "bb0", "bb2" },        iDom := "bb0" }
     , { name := "bb3", dominators := { "bb0", "bb3" },        iDom := "bb0" }
     , { name := "bb4", dominators := { "bb0", "bb2", "bb4" }, iDom := "bb2" }
     ]

/-
  Test: operation dominance across nested regions
-/
def testOpDomNestedRegions : String :=
  runOperationDominance r#""builtin.module"() ({
^bb0:
  %outer = "test.test"() ({
  ^bb1:
    %inner = "test.test"() : () -> i32
  }) : () -> i32
  %otherOuter = "test.test"() ({
  ^bb2:
    %siblingInner = "test.test"() : () -> i32
  }) : () -> i32
}) : () -> ()"#
    #[ { dominator := "outer",      dominated := "outer",        dominates := true,  properlyDominates := false }
     , { dominator := "outer",      dominated := "inner",        dominates := true,  properlyDominates := true  }
     , { dominator := "outer",      dominated := "otherOuter",   dominates := true,  properlyDominates := true  }
     , { dominator := "outer",      dominated := "siblingInner", dominates := true,  properlyDominates := true  }
     , { dominator := "inner",      dominated := "siblingInner", dominates := false, properlyDominates := false }
     , { dominator := "otherOuter", dominated := "inner",        dominates := false, properlyDominates := false }
     , { dominator := "otherOuter", dominated := "siblingInner", dominates := true,  properlyDominates := true  }
     ]

/-
  Test: two levels of nested operation dominance.
-/
def testOpDomTwoLevelNested : String :=
  runOperationDominance r#""builtin.module"() ({
^bb0:
  %top = "test.test"() ({
  ^bb1:
    %middle = "test.test"() ({
    ^bb2:
      %leaf = "test.test"() : () -> i32
    }) : () -> i32
  }) : () -> i32
}) : () -> ()"#
    #[ { dominator := "top",    dominated := "middle", dominates := true, properlyDominates := true  }
     , { dominator := "top",    dominated := "leaf",   dominates := true, properlyDominates := true  }
     , { dominator := "middle", dominated := "leaf",   dominates := true, properlyDominates := true  }
     , { dominator := "leaf",   dominated := "leaf",   dominates := true, properlyDominates := false }
     ]

/-
  Test: operation dominance across two blocks in the same nested region.
-/
def testOpDomSameRegionTwoBlocks : String :=
  runOperationDominance r#""builtin.module"() ({
^bb0:
  %outer = "test.test"() ({
  ^bb1:
    %entry = "test.test"() : () -> i32
    "test.test"() [^bb2] : () -> ()
  ^bb2:
    %exit = "test.test"() : () -> i32
  }) : () -> i32
}) : () -> ()"#
    #[ { dominator := "entry", dominated := "entry", dominates := true,  properlyDominates := false }
     , { dominator := "entry", dominated := "exit",  dominates := true,  properlyDominates := true  }
     , { dominator := "exit",  dominated := "entry", dominates := false, properlyDominates := false }
     , { dominator := "outer", dominated := "entry", dominates := true,  properlyDominates := true  }
     , { dominator := "outer", dominated := "exit",  dominates := true,  properlyDominates := true  }
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

/--
info: "ok"
-/
#guard_msgs in
#eval! testDomNestedRegions

/--
info: "ok"
-/
#guard_msgs in
#eval! testDomDiamondNestedJoin

/--
info: "ok"
-/
#guard_msgs in
#eval! testDomTwoLevelNested

/--
info: "ok"
-/
#guard_msgs in
#eval! testDomDiamondLoop

/--
info: "ok"
-/
#guard_msgs in
#eval! testOpDomNestedRegions

/--
info: "ok"
-/
#guard_msgs in
#eval! testOpDomTwoLevelNested

/--
info: "ok"
-/
#guard_msgs in
#eval! testOpDomSameRegionTwoBlocks

end DominanceAnalysis
