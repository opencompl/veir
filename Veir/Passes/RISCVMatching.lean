import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

/-! This file contains helper functions to match RISCV operations. -/

namespace Veir.RISCV

def matchAdd (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (.riscv .add) 2
  return (op[0]!, op[1]!)


def matchLi (op : OperationPtr) (ctx : IRContext OpCode) : Option ( propertiesOf (.riscv .li)) := do
  let (_, properties) ← matchOp op ctx (.riscv .li) 0
  return (properties)
