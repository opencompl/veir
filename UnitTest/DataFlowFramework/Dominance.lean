import UnitTest.DataFlowFramework.Helpers

import Veir.Analysis.DataFlow.DominanceAnalysis
import Veir.IR.Dominance

open Std (HashSet)
open Veir

/-- Expected dominance information for one named block in the test harness. -/
private structure ExpectedBlockDominators where
  name : String
  doms : HashSet String
  immediateDom : String

/-- Expected dominance result for one pair of named operations. -/
private structure ExpectedOperationDominance where
  dominator : String
  dominated : String
  dominates : Bool
  properDom : Bool

/--
Whether `block` lies in a region without SSA dominance: a *single-block* graph
region. There, source order is ignored, so dominance is reflexive even for the
proper variant: a block (or op) properly dominates itself, and a dominator
properly dominates every block it dominates, including itself. As in MLIR,
multi-block regions always have SSA dominance, whatever their kind.
-/
private def blockInGraphRegion (block : BlockPtr) (irCtx : IRContext OpCode) : Bool :=
  match (block.get! irCtx).parent with
  | some region =>
    (match (region.get! irCtx).firstBlock with
     | some first => (first.get! irCtx).next.isNone
     | none => true) &&
    match (region.get! irCtx).parent with
    | some parentOp =>
      let parent := parentOp.get! irCtx
      match parent.opType.getRegionKind (parent.regions.idxOf region) with
      | .Graph => true
      | .SSACFG => false
    | none => false
  | none => false

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
  -- In a graph region every dominator (including the block itself) properly
  -- dominates the block; in an SSACFG region a block does not properly dominate
  -- itself.
  let shouldProperlyDom := blockInGraphRegion block irCtx || expectedDom ≠ expected.name
  let mut report := #[]
  if !expectedBlock.dominatesByAnalysis block dfCtx irCtx then
    report := report.push s!"dominators {expected.name}: missing expected dominator {expectedDom}"
  if expectedBlock.properlyDominatesByAnalysis block dfCtx irCtx ≠ shouldProperlyDom then
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
  let inGraph := blockInGraphRegion block irCtx
  let observedByRelation := observedBlock.dominatesByAnalysis block dfCtx irCtx
  let observedProperly := observedBlock.properlyDominatesByAnalysis block dfCtx irCtx
  let mut report := #[]
  -- In a graph region proper dominance coincides with dominance (self included);
  -- in an SSACFG region a block does not properly dominate itself.
  if observedProperly ≠ (observedByRelation && (inGraph || observedBlock ≠ block)) then
    report := report.push
      s!"dominators {expected.name}: dominates/properlyDominates disagree on {observedName}"
  if observedByRelation && !expected.doms.contains observedName then
    report := report.push s!"dominators {expected.name}: unexpected dominator {observedName}"
  if observedProperly && (!expected.doms.contains observedName || (!inGraph && observedName = expected.name)) then
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
    | return #[s!"idom {expected.name}: expected immediate dominator {expected.immediateDom}, observed none"]
  let some expectedIDom := recovered.blocks[expected.immediateDom]?
    | return #[s!"idom {expected.name}: missing block label {expected.immediateDom}"]
  if observedIDom = expectedIDom then
    return #[]
  let observedName :=
    (recovered.blocks.toList.findSome? fun (name, block) =>
      if block = observedIDom then some name else none).getD "none"
  return #[s!"idom {expected.name}: expected {expected.immediateDom}, observed {observedName}"]

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
  for expectedDom in expected.doms.toArray do
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
  match expected.doms.isEmpty, observedFact? with
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

  let observedDominates := dominator.dominatesByAnalysis dominated dfCtx irCtx
  let observedProperly := dominator.properlyDominatesByAnalysis dominated dfCtx irCtx
  let mut report := #[]
  if observedDominates ≠ expected.dominates then
    report := report.push
      s!"op dominance {expected.dominator}->{expected.dominated}: expected dominates={expected.dominates}, observed {observedDominates}"
  if observedProperly ≠ expected.properDom then
    report := report.push
      s!"op dominance {expected.dominator}->{expected.dominated}: expected properlyDominates={expected.properDom}, observed {observedProperly}"
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
    r#""func.func"() <{function_type = () -> (), sym_name = "f"}> ({
^bb0:
  "test.test"() [^bb1] : () -> ()
^bb1:
  "test.test"() [^bb2] : () -> ()
^bb2:
  "test.test"() [^bb1] : () -> ()
}) : () -> ()"#
    #[ { name := "bb0", doms := { "bb0" },               immediateDom := "bb0" }
     , { name := "bb1", doms := { "bb0", "bb1" },        immediateDom := "bb0" }
     , { name := "bb2", doms := { "bb0", "bb1", "bb2" }, immediateDom := "bb1" }
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
    r#""func.func"() <{function_type = () -> (), sym_name = "f"}> ({
^bb0:
  "test.test"() [^bb1, ^bb2] : () -> ()
^bb1:
  "test.test"() [^bb3] : () -> ()
^bb2:
  "test.test"() [^bb3] : () -> ()
^bb3:
  "test.test"() : () -> ()
}) : () -> ()"#
    #[ { name := "bb0", doms := { "bb0" },        immediateDom := "bb0" }
     , { name := "bb1", doms := { "bb0", "bb1" }, immediateDom := "bb0" }
     , { name := "bb2", doms := { "bb0", "bb2" }, immediateDom := "bb0" }
     , { name := "bb3", doms := { "bb0", "bb3" }, immediateDom := "bb0" }
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
    r#""func.func"() <{function_type = () -> (), sym_name = "f"}> ({
^bb0:
  "test.test"() [^bb1] : () -> ()
^bb1:
  "test.test"() [^bb2] : () -> ()
^bb2:
  "test.test"() [^bb3] : () -> ()
^bb3:
  "test.test"() : () -> ()
}) : () -> ()"#
    #[ { name := "bb0", doms := { "bb0" },                      immediateDom := "bb0" }
     , { name := "bb1", doms := { "bb0", "bb1" },               immediateDom := "bb0" }
     , { name := "bb2", doms := { "bb0", "bb1", "bb2" },        immediateDom := "bb1" }
     , { name := "bb3", doms := { "bb0", "bb1", "bb2", "bb3" }, immediateDom := "bb2" }
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
    r#""func.func"() <{function_type = () -> (), sym_name = "f"}> ({
^bb0:
  "test.test"() [^bb1, ^bb2] : () -> ()
^bb1:
  "test.test"() [^bb5] : () -> ()
^bb2:
  "test.test"() [^bb3, ^bb4] : () -> ()
^bb3:
  "test.test"() [^bb6] : () -> ()
^bb4:
  "test.test"() [^bb6] : () -> ()
^bb5:
  "test.test"() [^bb1, ^bb7] : () -> ()
^bb6:
  "test.test"() [^bb7] : () -> ()
^bb7:
  "test.test"() : () -> ()
}) : () -> ()"#
    #[ { name := "bb0", doms := { "bb0" },               immediateDom := "bb0" }
     , { name := "bb1", doms := { "bb0", "bb1" },        immediateDom := "bb0" }
     , { name := "bb2", doms := { "bb0", "bb2" },        immediateDom := "bb0" }
     , { name := "bb3", doms := { "bb0", "bb2", "bb3" }, immediateDom := "bb2" }
     , { name := "bb4", doms := { "bb0", "bb2", "bb4" }, immediateDom := "bb2" }
     , { name := "bb5", doms := { "bb0", "bb1", "bb5" }, immediateDom := "bb1" }
     , { name := "bb6", doms := { "bb0", "bb2", "bb6" }, immediateDom := "bb2" }
     , { name := "bb7", doms := { "bb0", "bb7" },        immediateDom := "bb0" }
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
    #[ { name := "bb0", doms := { "bb0" },        immediateDom := "bb0" }
     , { name := "bb1", doms := { "bb0", "bb1" }, immediateDom := "bb1" }
     , { name := "bb2", doms := { "bb0", "bb2" }, immediateDom := "bb2" }
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
  run r#""func.func"() <{function_type = () -> (), sym_name = "f"}> ({
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
    #[ { name := "bb0", doms := { "bb0" },               immediateDom := "bb0" }
     , { name := "bb1", doms := { "bb0", "bb1" },        immediateDom := "bb0" }
     , { name := "bb2", doms := { "bb0", "bb2" },        immediateDom := "bb0" }
     , { name := "bb3", doms := { "bb0", "bb3" },        immediateDom := "bb0" }
     , { name := "bb4", doms := { "bb0", "bb3", "bb4" }, immediateDom := "bb4" }
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
    #[ { name := "bb0", doms := { "bb0" },               immediateDom := "bb0" }
     , { name := "bb1", doms := { "bb0", "bb1" },        immediateDom := "bb1" }
     , { name := "bb2", doms := { "bb0", "bb1", "bb2" }, immediateDom := "bb2" }
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
  run r#""func.func"() <{function_type = () -> (), sym_name = "f"}> ({
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
    #[ { name := "bb0", doms := { "bb0" },               immediateDom := "bb0" }
     , { name := "bb1", doms := { "bb0", "bb1" },        immediateDom := "bb0" }
     , { name := "bb2", doms := { "bb0", "bb2" },        immediateDom := "bb0" }
     , { name := "bb3", doms := { "bb0", "bb3" },        immediateDom := "bb0" }
     , { name := "bb4", doms := { "bb0", "bb2", "bb4" }, immediateDom := "bb2" }
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
    #[ -- `outer` and `otherOuter` share the module's graph region, so source order
       -- is ignored: each properly dominates itself and `otherOuter` dominates
       -- `inner` (nested in `outer`) despite appearing later.
       { dominator := "outer",      dominated := "outer",        dominates := true,  properDom := true  }
     , { dominator := "outer",      dominated := "inner",        dominates := true,  properDom := true  }
     , { dominator := "outer",      dominated := "otherOuter",   dominates := true,  properDom := true  }
     , { dominator := "outer",      dominated := "siblingInner", dominates := true,  properDom := true  }
     , { dominator := "inner",      dominated := "siblingInner", dominates := false, properDom := false }
     , { dominator := "otherOuter", dominated := "inner",        dominates := true,  properDom := true  }
     , { dominator := "otherOuter", dominated := "siblingInner", dominates := true,  properDom := true  }
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
    #[ { dominator := "top",    dominated := "middle", dominates := true, properDom := true  }
     , { dominator := "top",    dominated := "leaf",   dominates := true, properDom := true  }
     , { dominator := "middle", dominated := "leaf",   dominates := true, properDom := true  }
     , { dominator := "leaf",   dominated := "leaf",   dominates := true, properDom := true  }
     ]

/-
  Test: operation dominance across two blocks in the same nested region.
-/
def testOpDomSameRegionTwoBlocks : String :=
  runOperationDominance r#""func.func"() <{function_type = () -> (), sym_name = "f"}> ({
^bb1:
  %entry = "test.test"() : () -> i32
  "test.test"() [^bb2] : () -> ()
^bb2:
  %exit = "test.test"() : () -> i32
}) : () -> ()"#
    #[ { dominator := "entry", dominated := "entry", dominates := true,  properDom := false }
     , { dominator := "entry", dominated := "exit",  dominates := true,  properDom := true  }
     , { dominator := "exit",  dominated := "entry", dominates := false, properDom := false }
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
