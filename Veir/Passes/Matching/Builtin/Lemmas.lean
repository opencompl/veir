module

public import Veir.Passes.Matching.Builtin.Basic

import all Veir.Passes.Matching.Builtin.Basic

public section

/-! This file contains lemmas that characterize the behavior of the Builtin matching functions. -/

namespace Veir

/-- What matching `builtin.unrealized_conversion_cast` (via `matchCastOp`) syntactically guarantees. -/
theorem matchCastOp_implies {op : OperationPtr} {ctx : IRContext OpCode} {operand} :
    matchCastOp op ctx = some operand →
    op.getOpType! ctx = .builtin .unrealized_conversion_cast ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[operand] := by
  intro hmatch
  simp only [matchCastOp, bind, Option.bind, pure] at hmatch
  grind
