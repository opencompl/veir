module

public import Veir.Analysis.DataFlow.Domains.IntegerRangeDomain
public import Veir.Analysis.DataFlow.SparseForwardDataFlowAnalysis

public section

namespace Veir

/-!
# Integer range analysis

This module implements a sparse forward dataflow analysis that approximates each
ModArith SSA value with an interval of its possible unsigned integer representations.

The analysis distinguishes the canonical range `[0, modulus - 1]` from the maximum
storage range `[0, 2^bitwidth - 1]`. Region entry arguments and fully reduced operation
results use the canonical range. Constants receive singleton ranges, while supported
unreduced arithmetic operations preserve their computed interval when it fits in the
storage type. Unknown operations and results that may exceed the storage type use the
maximum storage range conservatively.

Ranges are joined along control flow edges.
-/

namespace IntegerRangeAnalysis

instance : SparseFactSpec .integerRange IntegerRangeLattice where
  payloadEq := rfl

def kind : AnalysisKind :=
  .integerRange

/-- Read the current integer range attached to an SSA value. -/
def getRange (value : ValuePtr) (dfCtx : DataFlowContext) : IntegerRangeLattice :=
  SparseFact.getElement .integerRange value dfCtx

/--
The canonical range contains the normalized representatives of a ModArith value:
`[0, modulus - 1]`. It describes values after full modular reduction and is therefore
determined by the modulus, not by the width of the underlying storage type.
-/
def canonicalRange (value : ValuePtr) (irCtx : IRContext OpCode) : IntegerRangeLattice :=
  match (value.getType! irCtx).val with
  | .modArithType mt =>
    let modulus := mt.modulus.value
    if h : 0 < modulus then
      .interval
        { lower := 0
          upper := modulus - 1
          lower_le_upper := by omega }
    else
      ⊤
  | _ => ⊤

/--
The maximum range contains every unsigned value representable by a ModArith value's
storage type: `[0, 2^bitwidth - 1]`. Unlike `canonicalRange`, it may include values at
least as large as the modulus. It is the conservative bound for unreduced results,
and unknown operations.
-/
def maxRange (value : ValuePtr) (irCtx : IRContext OpCode) : IntegerRangeLattice :=
  match (value.getType! irCtx).val with
  | .modArithType mt =>
    let storageCardinality : Nat := 2 ^ mt.bitwidth
    .interval
      { lower := 0
        upper := (storageCardinality : Int) - 1
        lower_le_upper := by
          have := Nat.two_pow_pos mt.bitwidth
          omega }
  | _ => ⊤

/-- Keep a raw result when it fits; otherwise conservatively use its storage range. -/
private def boundToMaxRange
    (raw maximum : IntegerRangeLattice) : IntegerRangeLattice :=
  match raw, maximum with
  | .bottom, _ => .bottom
  | raw, .top => raw
  | raw, .bottom => raw
  | .top, .interval maximum => .interval maximum
  | .interval raw, .interval maximum =>
    if maximum.lower ≤ raw.lower ∧ raw.upper ≤ maximum.upper then
      .interval raw
    else
      .interval maximum

private def applyReduction
    (op : OperationPtr)
    (raw : IntegerRangeLattice)
    (irCtx : WfIRContext OpCode) : IntegerRangeLattice :=
  let hasNoReduction :=
    match (op.get! irCtx.raw).attrs.entries.find?
        (fun entry => entry.1 == "reduction".toUTF8) with
    | some (_, .stringAttr attr) => attr.value == "none".toUTF8
    | _ => false
  if hasNoReduction then
    let maximum := maxRange (op.getResult 0) irCtx.raw
    boundToMaxRange raw maximum
  else
    -- Match the lowering pass default: a missing reduction attribute means `full`.
    canonicalRange (op.getResult 0) irCtx.raw

private def constantRange
    (op : OperationPtr)
    (irCtx : WfIRContext OpCode) : IntegerRangeLattice :=
  let props := op.getProperties! irCtx.raw (OpCode.mod_arith Mod_Arith.constant)
  match ((op.getResult 0 : ValuePtr).getType! irCtx.raw).val with
  | .modArithType mt =>
    let modulus := mt.modulus.value
    if 0 < modulus then
      IntegerRangeLattice.singleton (props.value.value % modulus)
    else
      ⊤
  | _ => ⊤

/--
Infer result ranges for one operation.

Unknown operations that produce ModArith values conservatively receive their type's
maximum storage range; unrelated results receive no update. Operations with an
uninitialized operand wait for more information.
-/
def transfer
    (op : OperationPtr)
    (operands : Array IntegerRangeLattice)
    (irCtx : WfIRContext OpCode) : Array (Option IntegerRangeLattice) :=
  let numResults := op.getNumResults! irCtx.raw
  let pessimisticUpdates := (op.getResults! irCtx.raw).map fun result =>
    match (result.getType! irCtx.raw).val with
    | .modArithType _ => some (maxRange result irCtx.raw)
    | _ => none

  if op.getNumRegions! irCtx.raw ≠ 0 then
    pessimisticUpdates
  else
    match op.getOpType! irCtx.raw with
    | OpCode.mod_arith Mod_Arith.constant =>
      Array.replicate numResults (some (constantRange op irCtx))
    | OpCode.mod_arith Mod_Arith.add =>
      match operands[0]?, operands[1]? with
      | some IntegerRangeLattice.bottom, _
      | _, some IntegerRangeLattice.bottom => Array.replicate numResults none
      | some lhs, some rhs =>
        Array.replicate numResults <| some <|
          applyReduction op (IntegerRangeLattice.add lhs rhs) irCtx
      | _, _ => pessimisticUpdates
    | OpCode.mod_arith Mod_Arith.sub =>
      match operands[0]?, operands[1]? with
      | some IntegerRangeLattice.bottom, _
      | _, some IntegerRangeLattice.bottom => Array.replicate numResults none
      | some lhs, some rhs =>
        match ((op.getResult 0 : ValuePtr).getType! irCtx.raw).val with
        | .modArithType mt =>
          -- Match lowering: subtraction is formed as `(lhs + q) - rhs` to avoid
          -- unsigned underflow for canonical operands.
          let shifted := IntegerRangeLattice.add lhs <|
            IntegerRangeLattice.singleton mt.modulus.value
          Array.replicate numResults <| some <|
            applyReduction op (IntegerRangeLattice.sub shifted rhs) irCtx
        | _ => pessimisticUpdates
      | _, _ => pessimisticUpdates
    | OpCode.mod_arith Mod_Arith.mul =>
      match operands[0]?, operands[1]? with
      | some IntegerRangeLattice.bottom, _
      | _, some IntegerRangeLattice.bottom => Array.replicate numResults none
      | some lhs, some rhs =>
        Array.replicate numResults <| some <|
          applyReduction op (IntegerRangeLattice.mul lhs rhs) irCtx
      | _, _ => pessimisticUpdates
    | _ => pessimisticUpdates

end IntegerRangeAnalysis

/-- Sparse forward integer-range analysis for supported integer-like dialects. -/
def IntegerRangeAnalysis : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new
    .integerRange
    IntegerRangeAnalysis.kind
    IntegerRangeAnalysis.transfer
    (entryState := fun value irCtx => IntegerRangeAnalysis.canonicalRange value irCtx.raw)

end Veir
