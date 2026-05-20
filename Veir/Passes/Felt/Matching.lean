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

def matchMul (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf (OpCode.felt Felt.mul)) := do
  let (operands, properties) ← matchOp op ctx (OpCode.felt Felt.mul) 2
  return (operands[0]!, operands[1]!, properties)

def matchNeg (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × propertiesOf (OpCode.felt Felt.neg)) := do
  let (operands, properties) ← matchOp op ctx (OpCode.felt Felt.neg) 1
  return (operands[0]!, properties)

def matchConst (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (propertiesOf (OpCode.felt Felt.const)) := do
  let (_, properties) ← matchOp op ctx (OpCode.felt Felt.const) 0
  return properties

/-- Follow a ValuePtr to its defining `felt.const` op and return its
    properties; mirrors `Veir.matchConstantVal` for LLVM. -/
def matchConstFromValue (val : ValuePtr) (ctx : IRContext OpCode) :
    Option (propertiesOf (OpCode.felt Felt.const)) := do
  let .opResult opResultPtr := val | none
  matchConst opResultPtr.op ctx

/-- Follow a ValuePtr to its defining `felt.add` op and return its
    operands + properties. -/
def matchAddFromValue (val : ValuePtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf (OpCode.felt Felt.add)) := do
  let .opResult opResultPtr := val | none
  matchAdd opResultPtr.op ctx

/-- Follow a ValuePtr to its defining `felt.sub` op and return its
    operands + properties. -/
def matchSubFromValue (val : ValuePtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf (OpCode.felt Felt.sub)) := do
  let .opResult opResultPtr := val | none
  matchSub opResultPtr.op ctx

/-- Follow a ValuePtr to its defining `felt.mul` op and return its
    operands + properties. -/
def matchMulFromValue (val : ValuePtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf (OpCode.felt Felt.mul)) := do
  let .opResult opResultPtr := val | none
  matchMul opResultPtr.op ctx

/-- Follow a ValuePtr to its defining `felt.neg` op and return its
    operand + properties. -/
def matchNegFromValue (val : ValuePtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × propertiesOf (OpCode.felt Felt.neg)) := do
  let .opResult opResultPtr := val | none
  matchNeg opResultPtr.op ctx

end Veir.FeltPass
