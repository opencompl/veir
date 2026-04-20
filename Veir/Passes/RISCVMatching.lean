import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

/-! This file contains helper functions to match operations when defining a rewrite. -/

namespace Veir

/--
  Match an operation that has a single result, a specific opcode,
  and a specific number of operands.
  Returns the operands and the properties of the operation if it matches, or `none` otherwise.
-/

def matchRISCVAdd (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (.riscv .add) 2
  return (op[0]!, op[1]!)


def matchRISCVLi (op : OperationPtr) (ctx : IRContext OpCode) : Option ( propertiesOf (.riscv .li)) := do
  let (_, properties) ← matchOp op ctx (.riscv .li) 0
  return (properties)
