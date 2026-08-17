module

public import Veir.Analysis.DataFlow.Domains.AbstractDomain
public import Veir.GlobalOpInfo

public section

namespace Veir

/-!
# ModArith range analysis helpers

This file adds the lattice structure and helper functions used by ModArith range analysis.
Proofs have not been added yet.
-/

/-- A closed integer interval. -/
structure IntegerRange where
  lower : Int
  upper : Int
  lower_le_upper : lower ≤ upper
deriving BEq, DecidableEq, Repr

/-- Abstract integer range lattice element. -/
inductive IntegerRangeLattice where
  | bottom
  | top
  | interval (range : IntegerRange)
deriving BEq, DecidableEq, Repr

namespace IntegerRangeLattice

instance : Bot IntegerRangeLattice where
  bot := .bottom

instance : Top IntegerRangeLattice where
  top := .top

/-- Construct a singleton range for a known integer literal. -/
def singleton (value : Int) : IntegerRangeLattice :=
  .interval { lower := value, upper := value, lower_le_upper := by omega }

/-- Union-like merge of two abstract ranges. -/
def join : IntegerRangeLattice → IntegerRangeLattice → IntegerRangeLattice
  | .bottom, rhs => rhs
  | lhs, .bottom => lhs
  | .top, _ => .top
  | _, .top => .top
  | .interval lhs, .interval rhs =>
      let lower := min lhs.lower rhs.lower
      let upper := max lhs.upper rhs.upper
      if h : lower ≤ upper then
        .interval { lower, upper, lower_le_upper := h }
      else
        .bottom

/-- Intersection-like overlap of two abstract ranges. -/
def meet : IntegerRangeLattice → IntegerRangeLattice → IntegerRangeLattice
  | .bottom, _ => .bottom
  | _, .bottom => .bottom
  | .top, rhs => rhs
  | lhs, .top => lhs
  | .interval lhs, .interval rhs =>
      let lower := max lhs.lower rhs.lower
      let upper := min lhs.upper rhs.upper
      if h : lower ≤ upper then
        .interval { lower, upper, lower_le_upper := h }
      else
        .bottom


instance : Join IntegerRangeLattice where
  join := join

/-- Add two abstract integer ranges. -/
def addRange (lhs rhs : IntegerRangeLattice) : IntegerRangeLattice :=
  match lhs, rhs with
  | .bottom, _ | _, .bottom => .bottom
  | .top, _ | _, .top => .top
  | .interval lhs, .interval rhs =>
      .interval
        { lower := lhs.lower + rhs.lower
          upper := lhs.upper + rhs.upper
          lower_le_upper := by
            have hl := lhs.lower_le_upper
            have hr := rhs.lower_le_upper
            omega }

/-- Multiply two abstract integer ranges. -/
def mulRange (lhs rhs : IntegerRangeLattice) : IntegerRangeLattice :=
  match lhs, rhs with
  | .bottom, _ | _, .bottom => .bottom
  | .top, _ | _, .top => .top
  | .interval lhs, .interval rhs =>
      let candidates := #[
        lhs.lower * rhs.lower,
        lhs.lower * rhs.upper,
        lhs.upper * rhs.lower,
        lhs.upper * rhs.upper]
      let lo := candidates.foldl min candidates[0]!
      let hi := candidates.foldl max candidates[0]!
      if h : lo ≤ hi then
        .interval { lower := lo, upper := hi, lower_le_upper := h }
      else
        .bottom

/-- The canonical `[0, q)` range for a `!mod_arith.int<q : iN>` value. -/
def canonicalModArithRange? (ty : TypeAttr) : Option IntegerRangeLattice := do
  let .modArithType mt := ty.val | none
  let q := mt.modulus.value
  if hq : q <= 0 then
    none
  else
    have h : 0 ≤ q - 1 := by omega
    some <| .interval
      { lower := 0
        upper := q - 1
        lower_le_upper := h }

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
def inferModArithRange? (value : ValuePtr) (knownRanges : KnownRanges)
    (irCtx : IRContext OpCode) : Option IntegerRangeLattice := do
  let some op := value.definingOp? | canonicalModArithRange? (value.getType! irCtx)

  match op.getOpType! irCtx with
  | OpCode.mod_arith Mod_Arith.constant =>
    let props := op.getProperties! irCtx (OpCode.mod_arith Mod_Arith.constant)
    let .modArithType mt := ((op.getResult 0 : ValuePtr).getType! irCtx).val | none
    let q := mt.modulus.value
    if q <= 0 then
      none
    else
      some <| IntegerRangeLattice.singleton (props.value.value % q)
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

end IntegerRangeLattice

end Veir
