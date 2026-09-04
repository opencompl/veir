module

public import Veir.Analysis.DataFlow.Domains.IntegerRangeDomain
public import Veir.Analysis.DataFlow.SparseForwardDataFlowAnalysis

public section

namespace Veir

/-!
# ModArith range analysis

This module implements a sparse forward dataflow analysis that approximates each
ModArith SSA value with an interval of its possible unsigned integer representations.

Region entry arguments and fully reduced operation results use the canonical range
`[0, modulus - 1]`. Constants receive singleton ranges, while supported unreduced
arithmetic operations preserve their raw computed interval. Unknown operations use
`⊤` conservatively.

Ranges are joined along control flow edges.
-/

namespace ModArithRangeAnalysis

instance : SparseFactSpec .modArithRange IntegerRangeLattice where
  payloadEq := rfl

def kind : AnalysisKind :=
  .modArithRange

/-- Read the current integer range attached to an SSA value. -/
def getRange (value : ValuePtr) (dfCtx : DataFlowContext) : IntegerRangeLattice :=
  SparseFact.getElement .modArithRange value dfCtx

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
    raw
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

Unknown operations that produce ModArith values conservatively receive `⊤`; unrelated
results receive `⊥`. Operations with an uninitialized operand wait for more
information.
-/
def transfer
    (op : OperationPtr)
    (operands : Array IntegerRangeLattice)
    (irCtx : WfIRContext OpCode) : Array IntegerRangeLattice :=
  let numResults := op.getNumResults! irCtx.raw
  let pessimisticUpdates := (op.getResults! irCtx.raw).map fun result =>
    match (result.getType! irCtx.raw).val with
    | .modArithType _ => ⊤
    | _ => ⊥

  if op.getNumRegions! irCtx.raw ≠ 0 then
    pessimisticUpdates
  else
    match op.getOpType! irCtx.raw with
    | OpCode.mod_arith Mod_Arith.constant =>
      Array.replicate numResults (constantRange op irCtx)
    | OpCode.mod_arith Mod_Arith.add =>
      match operands[0]?, operands[1]? with
      | some IntegerRangeLattice.bottom, _
      | _, some IntegerRangeLattice.bottom => Array.replicate numResults ⊥
      | some lhs, some rhs =>
        Array.replicate numResults <| applyReduction op (IntegerRangeLattice.add lhs rhs) irCtx
      | _, _ => pessimisticUpdates
    | OpCode.mod_arith Mod_Arith.sub =>
      match operands[0]?, operands[1]? with
      | some IntegerRangeLattice.bottom, _
      | _, some IntegerRangeLattice.bottom => Array.replicate numResults ⊥
      | some lhs, some rhs =>
        match ((op.getResult 0 : ValuePtr).getType! irCtx.raw).val with
        | .modArithType mt =>
          -- Match lowering: subtraction is formed as `(lhs + q) - rhs` to avoid
          -- unsigned underflow for canonical operands.
          let shifted := IntegerRangeLattice.add lhs <|
            IntegerRangeLattice.singleton mt.modulus.value
          Array.replicate numResults <| applyReduction op (IntegerRangeLattice.sub shifted rhs) irCtx
        | _ => pessimisticUpdates
      | _, _ => pessimisticUpdates
    | OpCode.mod_arith Mod_Arith.mul =>
      match operands[0]?, operands[1]? with
      | some IntegerRangeLattice.bottom, _
      | _, some IntegerRangeLattice.bottom => Array.replicate numResults ⊥
      | some lhs, some rhs =>
        Array.replicate numResults <| applyReduction op (IntegerRangeLattice.mul lhs rhs) irCtx
      | _, _ => pessimisticUpdates
    | _ => pessimisticUpdates

end ModArithRangeAnalysis

/-- Sparse forward range analysis for ModArith values. -/
def ModArithRangeAnalysis : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new
    .modArithRange
    ModArithRangeAnalysis.kind
    ModArithRangeAnalysis.transfer
    (entryState := fun value irCtx => ModArithRangeAnalysis.canonicalRange value irCtx.raw)

end Veir
