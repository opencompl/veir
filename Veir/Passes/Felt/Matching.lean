import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

/-! Helper matchers for Felt-dialect ops. -/

namespace Veir.FeltPass

def matchAdd (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf (OpCode.felt Felt.add)) := do
  let (operands, properties) ← matchOp op ctx (OpCode.felt Felt.add) 2
  return (operands[0]!, operands[1]!, properties)

def matchSub (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf (OpCode.felt Felt.sub)) := do
  let (operands, properties) ← matchOp op ctx (OpCode.felt Felt.sub) 2
  return (operands[0]!, operands[1]!, properties)

def matchNeg (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × propertiesOf (OpCode.felt Felt.neg)) := do
  let (operands, properties) ← matchOp op ctx (OpCode.felt Felt.neg) 1
  return (operands[0]!, properties)

/-- Follow a ValuePtr to its defining `felt.neg` op and return its
    operand + properties. -/
def matchNegFromValue (val : ValuePtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × propertiesOf (OpCode.felt Felt.neg)) := do
  let .opResult opResultPtr := val | none
  matchNeg opResultPtr.op ctx

end Veir.FeltPass
