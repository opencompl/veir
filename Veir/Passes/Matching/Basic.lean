module

public import Veir.IR.Basic
public import Veir.GlobalOpInfo
public import Veir.PatternRewriter.Basic

public section

/-! This file contains helper functions to match operations when defining a rewrite. -/

namespace Veir

/--
  Match an operation that has a single result, a specific opcode,
  and a specific number of operands.
  Returns the operands and the properties of the operation if it matches, or `none` otherwise.
-/
def matchOp (op : OperationPtr) (ctx : IRContext OpCode) (opType : OpCode) (numOperands : Nat) :
    Option (Array ValuePtr × propertiesOf opType) := do
  guard (op.getOpType! ctx = opType)
  guard (op.getNumOperands! ctx = numOperands)
  guard (op.getNumResults! ctx = 1)
  let operands := op.getOperands! ctx
  some (operands, op.getProperties! ctx opType)

/-- What the generic `matchOp` helper syntactically guarantees. -/
@[grind →]
theorem matchOp_implies {op : OperationPtr} {ctx : IRContext OpCode}
    {opType numOperands operands props} :
    matchOp op ctx opType numOperands = some (operands, props) →
    op.getOpType! ctx = opType ∧
    op.getNumOperands! ctx = numOperands ∧
    op.getNumResults! ctx = 1 ∧
    operands = op.getOperands! ctx ∧
    props = op.getProperties! ctx opType := by
  intro hmatch
  simp only [matchOp, bind, pure, Option.bind, guard, failure] at hmatch
  grind
