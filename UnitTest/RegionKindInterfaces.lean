import Veir.Interfaces.RegionKindInterfaces
import Veir.Input

open Veir
open Veir.Input

private def firstRegion (parsed : WfIRContext OpCode × OperationPtr) : RegionPtr :=
  parsed.2.getRegion! parsed.1.raw 0

private def emptyRegion := parseSourceString! r#""test.test"() ({}) : () -> ()"#.toUTF8

private def oneBlockRegion := parseSourceString! r#""test.test"() ({
  "test.test"() : () -> ()
}) : () -> ()"#.toUTF8

/-
  A `test` operation declares every one of its regions to be a graph region, so
  the declared kind is the same whatever the region holds.
-/

#guard (firstRegion emptyRegion).getRegionKind emptyRegion.1 == .Graph
#guard (firstRegion oneBlockRegion).getRegionKind oneBlockRegion.1 == .Graph

/-
  Dominance does not follow the declaration blindly: only a region holding
  exactly one block can take its owner's graph setting, so the empty region
  uses SSA dominance while the single-block one does not. This matches MLIR,
  where the same query is gated on `Region::hasOneBlock` and an empty region
  leaves `hasSSADominance` at its initial `true`.
-/

#guard (firstRegion emptyRegion).hasSSADominance emptyRegion.1
#guard !(firstRegion oneBlockRegion).hasSSADominance oneBlockRegion.1
