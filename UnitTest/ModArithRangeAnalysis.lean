import UnitTest.DataFlowFramework.Helpers

import Veir.Dialects.ModArith.Analysis.RangeAnalysis

open Veir

namespace ModArithDataflow

/-- Expected range for one named SSA value. -/
private structure ExpectedRange where
  name : String
  range : IntegerRangeLattice

private def rangeToString : IntegerRangeLattice → String
  | .bottom => "bottom"
  | .top => "top"
  | .interval r => s!"[{r.lower}, {r.upper}]"

private def compareRanges
    (recovered : RecoveredNames)
    (expected : Array ExpectedRange)
    (irCtx : IRContext OpCode) : MismatchReport := Id.run do
  let mut knownRanges : IntegerRangeLattice.KnownRanges := {}
  let mut report := #[]
  for e in expected do
    let some value := recovered.values[e.name]?
      | report := report.push s!"range {e.name}: missing SSA value"
        continue
    let some observed := IntegerRangeLattice.inferModArithRange? value knownRanges irCtx
      | report := report.push s!"range {e.name}: no inferred mod_arith range"
        continue
    knownRanges := knownRanges.insert value observed
    if observed != e.range then
      report := report.push
        s!"range {e.name}: expected {rangeToString e.range}, observed {rangeToString observed}"
  report

private def interval (lower upper : Int) (h : lower ≤ upper := by omega) : IntegerRangeLattice :=
  .interval { lower, upper, lower_le_upper := h }

/--
Mod_Arith range example with default reduction.

a, b ∈ [0, q)
c = 46
s = 3
add₀ = (a + c) mod q
add₁ = (add₀ + b) mod q
add₂ = (add₁ + a) mod q
out = (add₂ · s) mod q

When the reduction attribute is missing, it is treated as full reduction, so each
operation result is folded back into the canonical range `[0, q)`.
-/
def runModArithDefaultReductionExample : String :=
  let mlir := r#""builtin.module"() ({
^bb0:
  "func.func"() <{function_type = (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>, sym_name = "mod_arith_add_chain"}> ({
  ^bb1(%a : !mod_arith.int<12289 : i32>, %b : !mod_arith.int<12289 : i32>):
    %c = "mod_arith.constant"() <{"value" = 46 : i32}> : () -> !mod_arith.int<12289 : i32>
    %small = "mod_arith.constant"() <{"value" = 3 : i32}> : () -> !mod_arith.int<12289 : i32>
    %add0 = "mod_arith.add"(%a, %c) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %add1 = "mod_arith.add"(%add0, %b) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %add2 = "mod_arith.add"(%add1, %a) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %out = "mod_arith.mul"(%add2, %small) : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    "func.return"(%out) : (!mod_arith.int<12289 : i32>) -> ()
  }) : () -> ()
}) : () -> ()"#
  let expected :=
    #[ { name := "a",     range := interval 0 12288 }
      , { name := "b",     range := interval 0 12288 }
      , { name := "c",     range := interval 46 46 }
      , { name := "small", range := interval 3 3 }
      , { name := "add0",  range := interval 0 12288 }
      , { name := "add1",  range := interval 0 12288 }
      , { name := "add2",  range := interval 0 12288 }
      , { name := "out",   range := interval 0 12288 }
      ]
  match parseTopLevelOp mlir with
  | .error err => s!"parse failed: {err}"
  | .ok (top, parserState) =>
      match recoverNames top parserState.ctx mlir with
      | .error err => err
      | .ok recovered => renderReport (compareRanges recovered expected parserState.ctx)

/--
Mod_Arith range example without reduction.

a, b ∈ [0, q)
c = 46
s = 3
add₀ = a + c
add₁ = add₀ + b
add₂ = add₁ + a
out = add₂ · s

The input block arguments are assumed to already be canonical values in `[0, q)`.
Since every operation in this example has `reduction = "none"`, operation results
keep their raw integer ranges instead of being folded back to `[0, q)`.
Constants are tracked exactly.
-/


def runModArithNoneReductionExample : String :=
  let mlir := r#""builtin.module"() ({
^bb0:
  "func.func"() <{function_type = (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>, sym_name = "mod_arith_add_chain"}> ({
  ^bb1(%a : !mod_arith.int<12289 : i32>, %b : !mod_arith.int<12289 : i32>):
    %c = "mod_arith.constant"() <{"value" = 46 : i32}> : () -> !mod_arith.int<12289 : i32>
    %small = "mod_arith.constant"() <{"value" = 3 : i32}> : () -> !mod_arith.int<12289 : i32>
    %add0 = "mod_arith.add"(%a, %c) {"reduction" = "none"} : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %add1 = "mod_arith.add"(%add0, %b) {"reduction" = "none"} : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %add2 = "mod_arith.add"(%add1, %a) {"reduction" = "none"} : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    %out = "mod_arith.mul"(%add2, %small) {"reduction" = "none"} : (!mod_arith.int<12289 : i32>, !mod_arith.int<12289 : i32>) -> !mod_arith.int<12289 : i32>
    "func.return"(%out) : (!mod_arith.int<12289 : i32>) -> ()
  }) : () -> ()
}) : () -> ()"#
  let expected :=
    #[ { name := "a",     range := interval 0 12288 }
     , { name := "b",     range := interval 0 12288 }
     , { name := "c",     range := interval 46 46 }
     , { name := "small", range := interval 3 3 }
     , { name := "add0",  range := interval 46 12334 }
     , { name := "add1",  range := interval 46 24622 }
     , { name := "add2",  range := interval 46 36910 }
     , { name := "out",   range := interval 138 110730 }
     ]
  match parseTopLevelOp mlir with
  | .error err => s!"parse failed: {err}"
  | .ok (top, parserState) =>
      match recoverNames top parserState.ctx mlir with
      | .error err => err
      | .ok recovered => renderReport (compareRanges recovered expected parserState.ctx)


/--
info: "ok"
-/
#guard_msgs in
#eval! runModArithDefaultReductionExample

/--
info: "ok"
-/
#guard_msgs in
#eval! runModArithNoneReductionExample

end ModArithDataflow
