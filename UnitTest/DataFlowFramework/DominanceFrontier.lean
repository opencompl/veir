import UnitTest.DataFlowFramework.Helpers
import Veir.Analysis.DominanceFrontier

open Veir

namespace DominanceFrontierTest

private structure Query where
  /-- A block identifying the region whose frontiers are queried. -/
  regionBlock : String
  definitions : Array String
  expected : Array String

private def run (mlir : String) (queries : Array Query) : String :=
  runWithAnalyses mlir #[Veir.DominanceAnalysis] fun top dfCtx ctx => Id.run do
    let .ok names := recoverNames top ctx mlir
      | return #["failed to recover block names"]
    let mut report := #[]
    for query in queries do
      let some block := names.blocks[query.regionBlock]?
        | return #[s!"missing region block {query.regionBlock}"]
      let some region := (block.get! ctx.raw).parent
        | return #["region block has no parent"]
      let some definitions := query.definitions.mapM (names.blocks[·]?)
        | return #["missing definition block"]
      let some expected := query.expected.mapM (names.blocks[·]?)
        | return #["missing expected block"]
      let frontier := DominanceFrontier.compute region dfCtx ctx
      let observed := frontier.iterated definitions
      if observed != expected then
        let observedNames := observed.map fun block =>
          (names.blocks.toList.findSome? fun (name, ptr) =>
            if ptr = block then some name else none).getD "unknown"
        report := report.push
          s!"IDF({query.definitions}) in {query.regionBlock}: expected {query.expected}, observed {observedNames}"
    return report

-- A diamond, including duplicate CFG edges and duplicate/reordered seeds.
private def diamond : String := r#""func.func"() <{sym_name = "f", function_type = () -> ()}> ({
^entry:
  %cond = "test.test"() : () -> i1
  "cf.cond_br"(%cond) [^left, ^right]
    <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^left:
  "cf.cond_br"(%cond) [^join, ^join]
    <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^right:
  "cf.br"() [^join] : () -> ()
^join:
  "func.return"() : () -> ()
}) : () -> ()"#

/-- info: "ok" -/
#guard_msgs in
#eval! run diamond #[
  ⟨"entry", #[], #[]⟩,
  ⟨"entry", #["entry"], #[]⟩,
  ⟨"entry", #["join"], #[]⟩,
  ⟨"entry", #["left"], #["join"]⟩,
  ⟨"entry", #["right", "left", "right"], #["join"]⟩,
  ⟨"entry", #["left", "right"], #["join"]⟩]

-- DF(left) = {join}, but DF(join) = {header}: placement must iterate.
-- The header's backedge also puts it in its own frontier.
private def loopDiamond : String := r#""func.func"() <{sym_name = "f", function_type = () -> ()}> ({
^entry:
  %cond = "test.test"() : () -> i1
  "cf.br"() [^header] : () -> ()
^header:
  "cf.cond_br"(%cond) [^left, ^right]
    <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^left:
  "cf.br"() [^join] : () -> ()
^right:
  "cf.br"() [^join] : () -> ()
^join:
  "cf.br"() [^header] : () -> ()
}) : () -> ()"#

/-- info: "ok" -/
#guard_msgs in
#eval! run loopDiamond #[
  ⟨"entry", #["left"], #["header", "join"]⟩,
  ⟨"entry", #["header"], #["header"]⟩,
  ⟨"entry", #["join"], #["header"]⟩,
  ⟨"entry", #["join", "left"], #["header", "join"]⟩,
  ⟨"entry", #["left", "join"], #["header", "join"]⟩,
  ⟨"entry", #["entry"], #[]⟩]

private def selfLoop : String := r#""func.func"() <{sym_name = "f", function_type = () -> ()}> ({
^entry:
  %cond = "test.test"() : () -> i1
  "cf.br"() [^header] : () -> ()
^header:
  "cf.cond_br"(%cond) [^header, ^exit]
    <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^exit:
  "func.return"() : () -> ()
}) : () -> ()"#

/-- info: "ok" -/
#guard_msgs in
#eval! run selfLoop #[
  ⟨"entry", #["header"], #["header"]⟩,
  ⟨"entry", #["exit"], #[]⟩]

-- Two entries into a cycle: the utility must not assume reducible control flow.
private def irreducible : String := r#""func.func"() <{sym_name = "f", function_type = () -> ()}> ({
^entry:
  %cond = "test.test"() : () -> i1
  "cf.cond_br"(%cond) [^a, ^b]
    <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^a:
  "cf.br"() [^b] : () -> ()
^b:
  "cf.cond_br"(%cond) [^a, ^exit]
    <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^exit:
  "func.return"() : () -> ()
}) : () -> ()"#

/-- info: "ok" -/
#guard_msgs in
#eval! run irreducible #[
  ⟨"entry", #["a"], #["a", "b"]⟩,
  ⟨"entry", #["b"], #["a", "b"]⟩,
  ⟨"entry", #["a", "b"], #["a", "b"]⟩]

-- The reachable CFG is a straight line. An unreachable cycle with an edge
-- into that line must neither create merge points nor contribute definitions.
private def unreachable : String := r#""func.func"() <{sym_name = "f", function_type = () -> ()}> ({
^entry:
  %cond = "test.test"() : () -> i1
  "cf.br"() [^middle] : () -> ()
^dead:
  "cf.cond_br"(%cond) [^dead, ^exit]
    <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^exit:
  "func.return"() : () -> ()
^middle:
  "cf.br"() [^exit] : () -> ()
}) : () -> ()"#

/-- info: "ok" -/
#guard_msgs in
#eval! run unreachable #[
  ⟨"entry", #["entry", "middle", "exit"], #[]⟩,
  ⟨"entry", #["dead"], #[]⟩,
  ⟨"entry", #["middle", "dead"], #[]⟩]

-- Regions are independent; nested definitions do not implicitly count as
-- definitions in the enclosing CFG. The mem2reg caller must summarize them.
private def nested : String := r#""func.func"() <{sym_name = "f", function_type = () -> ()}> ({
^entry:
  %cond = "test.test"() : () -> i1
  "cf.cond_br"(%cond) [^left, ^right]
    <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
^left:
  "func.func"() <{sym_name = "nested", function_type = () -> ()}> ({
  ^innerEntry:
    "cf.br"() [^innerLoop] : () -> ()
  ^innerLoop:
    "cf.br"() [^innerLoop] : () -> ()
  }) : () -> ()
  "cf.br"() [^join] : () -> ()
^right:
  "cf.br"() [^join] : () -> ()
^join:
  "test.test"() ({
  ^graph:
    "test.test"() : () -> ()
  }) : () -> ()
  "func.return"() : () -> ()
}) : () -> ()"#

/-- info: "ok" -/
#guard_msgs in
#eval! run nested #[
  ⟨"entry", #["innerLoop"], #[]⟩,
  ⟨"entry", #["left", "innerLoop"], #["join"]⟩,
  ⟨"innerEntry", #["innerLoop", "left"], #["innerLoop"]⟩,
  ⟨"graph", #["graph", "left"], #[]⟩]

/-- info: "ok" -/
#guard_msgs in
#eval! runWithAnalyses r#""test.test"() ({}) : () -> ()"# #[Veir.DominanceAnalysis]
  fun top dfCtx ctx =>
    let frontier := DominanceFrontier.compute (top.getRegion! ctx.raw 0) dfCtx ctx
    if frontier.blocks.isEmpty && (frontier.iterated #[]).isEmpty then #[]
    else #["expected an empty frontier for an empty region"]

end DominanceFrontierTest
