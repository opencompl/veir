import Veir.GlobalOpInfo
import Veir.Interfaces.RegionKindInterfaces
import Veir.Parser.MlirParser

open Veir
open Veir.Parser

private def parse (s : String) : OperationPtr × WfIRContext OpCode :=
  match WfIRContext.create OpCode with
  | none => panic! "failed to create IR context"
  | some (ctx, _) =>
    match ParserState.fromInput s.toByteArray with
    | .error _ => panic! "lex error"
    | .ok parser =>
      match parseTopLevelOp.run (MlirParserState.fromContext ctx) parser with
      | .error _ => panic! "parse error"
      | .ok (op, state, _) => (op, state.ctx)

private def firstRegion (parsed : OperationPtr × WfIRContext OpCode) : RegionPtr :=
  parsed.1.getRegion! parsed.2.raw 0

private def emptyRegion := parse r#""test.test"() ({}) : () -> ()"#

private def oneBlockRegion := parse r#""test.test"() ({
  "test.test"() : () -> ()
}) : () -> ()"#

/-
  A `test` operation declares every one of its regions to be a graph region, so
  the declared kind is the same whatever the region holds.
-/

#guard (firstRegion emptyRegion).getRegionKind emptyRegion.2 == .Graph
#guard (firstRegion oneBlockRegion).getRegionKind oneBlockRegion.2 == .Graph

/-
  Dominance does not follow the declaration blindly: only a region holding
  exactly one block can take its owner's graph setting, so the empty region
  uses SSA dominance while the single-block one does not. This matches MLIR,
  where the same query is gated on `Region::hasOneBlock` and an empty region
  leaves `hasSSADominance` at its initial `true`.
-/

#guard (firstRegion emptyRegion).hasSSADominance emptyRegion.2
#guard !(firstRegion oneBlockRegion).hasSSADominance oneBlockRegion.2
