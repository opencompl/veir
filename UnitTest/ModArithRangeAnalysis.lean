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
  | .interval r => s!"[{r.lower}, {r.upper}] : i{r.bitwidth}"

/-- The canonical `[0, q)` range for a `!mod_arith.int<q : iN>` value. -/
def canonicalModArithRange? (ty : TypeAttr) : Option IntegerRangeLattice := do
  let .modArithType mt := ty.val | none
  let q := mt.modulus.value
  if q <= 0 then
    none
  else
    some <| .interval
      { bitwidth := mt.bitwidth
        lower := 0
        upper := q - 1 }

private def hasNoReductionAttr (op : OperationPtr) (irCtx : IRContext OpCode) : Bool :=
  match (op.get! irCtx).attrs.entries.find? (fun entry => entry.1 == "reduction".toUTF8) with
  | some (_, .stringAttr attr) => attr.value == "none".toUTF8
  | _ => false

private def applyReduction (op : OperationPtr) (raw : IntegerRangeLattice)
    (irCtx : IRContext OpCode) : Option IntegerRangeLattice :=
  if hasNoReductionAttr op irCtx then
    some raw
  else
    -- Match the lowering pass default: missing reduction attrs are treated as `full`.
    canonicalModArithRange? ((op.getResult 0 : ValuePtr).getType! irCtx)

abbrev KnownRanges := Std.HashMap ValuePtr IntegerRangeLattice

/-- Infer one value using ranges already present in `knownRanges`. -/
private def inferModArithRange? (value : ValuePtr) (knownRanges : KnownRanges)
    (irCtx : IRContext OpCode) : Option IntegerRangeLattice := do
  let some op := value.getDefiningOp! irCtx
    | canonicalModArithRange? (value.getType! irCtx)

  match op.getOpType! irCtx with
  | OpCode.mod_arith Mod_Arith.constant =>
    let props := op.getProperties! irCtx (OpCode.mod_arith Mod_Arith.constant)
    let .modArithType mt := ((op.getResult 0 : ValuePtr).getType! irCtx).val | none
    let q := mt.modulus.value
    if q <= 0 then
      none
    else
      some <| IntegerRangeLattice.singleton mt.bitwidth (props.value.value % q)
  | OpCode.mod_arith Mod_Arith.add =>
    let operands := op.getOperands! irCtx
    let lhs ← knownRanges[operands[0]!]?
    let rhs ← knownRanges[operands[1]!]?
    applyReduction op (IntegerRangeLattice.addRange lhs rhs) irCtx
  | OpCode.mod_arith Mod_Arith.mul =>
    let operands := op.getOperands! irCtx
    let lhs ← knownRanges[operands[0]!]?
    let rhs ← knownRanges[operands[1]!]?
    applyReduction op (IntegerRangeLattice.mulRange lhs rhs) irCtx
  | _ =>
    none

private def compareRanges
    (recovered : RecoveredNames)
    (expected : Array ExpectedRange)
    (irCtx : IRContext OpCode) : MismatchReport := Id.run do
  let mut knownRanges : KnownRanges := {}
  let mut report := #[]
  for e in expected do
    let some value := recovered.values[e.name]?
      | report := report.push s!"range {e.name}: missing SSA value"
        continue
    let some observed := inferModArithRange? value knownRanges irCtx
      | report := report.push s!"range {e.name}: no inferred mod_arith range"
        continue
    knownRanges := knownRanges.insert value observed
    if observed != e.range then
      report := report.push
        s!"range {e.name}: expected {rangeToString e.range}, observed {rangeToString observed}"
  report

private def interval (bitwidth : Nat) (lower upper : Int) : IntegerRangeLattice :=
  .interval { bitwidth, lower, upper }

/--
Mod_Arith range example with default reduction. When the reduction attribute is
missing, it is treated as full reduction, so reduction is always executed and
the result is folded into the range `[0, q)`.
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
    #[ { name := "a",     range := interval 32 0 12288 }
      , { name := "b",     range := interval 32 0 12288 }
      , { name := "c",     range := interval 32 46 46 }
      , { name := "small", range := interval 32 3 3 }
      , { name := "add0",  range := interval 32 0 12288 }
      , { name := "add1",  range := interval 32 0 12288 }
      , { name := "add2",  range := interval 32 0 12288 }
      , { name := "out",   range := interval 32 0 12288 }
      ]
  match parseTopLevelOp mlir with
  | .error err => s!"parse failed: {err}"
  | .ok (top, parserState) =>
      match recoverNames top parserState.ctx mlir with
      | .error err => err
      | .ok recovered => renderReport (compareRanges recovered expected parserState.ctx)

/--
Run the mod_arith range example. The input block arguments are assumed to already
be canonical values in `[0, q)`. Operation results track raw integer ranges when
`reduction = "none"`; otherwise they are folded back to the canonical range.
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
    #[ { name := "a",     range := interval 32 0 12288 }
     , { name := "b",     range := interval 32 0 12288 }
     , { name := "c",     range := interval 32 46 46 }
     , { name := "small", range := interval 32 3 3 }
     , { name := "add0",  range := interval 32 46 12334 }
     , { name := "add1",  range := interval 32 46 24622 }
     , { name := "add2",  range := interval 32 46 36910 }
     , { name := "out",   range := interval 32 138 110730 }
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
