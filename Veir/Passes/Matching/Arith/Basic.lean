module

public import Veir.Passes.Matching.Basic
public import Veir.Dialects.Arith.OpInfo

public section

/-! This file contains helper functions to match operations when defining a rewrite in dialect. -/

namespace Veir

variable {OpCode : Type} [HasOpInfo OpCode] [HasDialect OpCode Arith]

def matchArithConstantIntVal (val : ValuePtr) (ctx : IRContext OpCode) : Option IntegerAttr := do
  let .opResult result := val | none
  let some .constant := toDialect? Arith (result.op.getOpType! ctx) | none
  let properties := result.op.getProperties! ctx Arith.constant
  return properties.value

def matchArithRemui (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf Arith.remui) := do
  let (op, properties) ← matchOp op ctx Arith.remui 2
  return (op[0]!, op[1]!, properties)
