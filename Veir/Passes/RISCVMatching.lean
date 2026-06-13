import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

/-! This file contains helper functions to match RISCV operations. -/

namespace Veir.RISCV

def matchRiscvBinop (oc : Riscv) (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr) := do
  let (op, _) ← matchOp op ctx (.riscv oc) 2
  return (op[0]!, op[1]!)

def matchAdd := matchRiscvBinop .add

def matchLi (val : ValuePtr) (ctx : IRContext OpCode) : Option (propertiesOf (.riscv .li)) := do
  let op ← val.getDefiningOp! ctx
  let (_, properties) ← matchOp op ctx (.riscv .li) 0
  return properties

/-- Match a value defined by `riscv.zextw`, returning its source operand. -/
def matchZextw (val : ValuePtr) (ctx : IRContext OpCode) : Option ValuePtr := do
  let op ← val.getDefiningOp! ctx
  let (operands, _) ← matchOp op ctx (.riscv .zextw) 1
  return operands[0]!
