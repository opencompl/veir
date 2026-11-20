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

/-
  An `hw.module` body is a graph region, as in CIRCT, because a module is a netlist rather than
  a schedule: a register takes the value its own output feeds into, so no ordering of the body
  would satisfy SSA dominance. The body holds one block, so dominance follows the declaration.
-/

private def hwModule := parseSourceString! r#""hw.module"() <{module_type = !hw.modty<input clk : i1, output q : i1>, parameters = [], per_port_attrs = [], sym_name = "m"}> ({
^bb0(%clk: i1):
  "hw.output"(%clk) : (i1) -> ()
}) : () -> ()"#.toUTF8

#guard (firstRegion hwModule).getRegionKind hwModule.1 == .Graph
#guard !(firstRegion hwModule).hasSSADominance hwModule.1

/-
  The setting is specific to `hw.module`: an ordinary body, such as a function's, is still an
  SSACFG region whose definitions must dominate their uses.
-/

private def funcBody := parseSourceString! r#""func.func"() <{function_type = () -> (), sym_name = "f"}> ({
^bb0():
  "func.return"() : () -> ()
}) : () -> ()"#.toUTF8

#guard (firstRegion funcBody).getRegionKind funcBody.1 == .SSACFG
#guard (firstRegion funcBody).hasSSADominance funcBody.1
