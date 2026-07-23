module

public import Veir.Passes.Matching.Basic

public section

/-! This file contains helper functions to match operations when defining a rewrite in dialect. -/

namespace Veir

def matchArithConstantIntVal (val : ValuePtr) (ctx : IRContext OpCode) : Option IntegerAttr := do
  let .opResult result := val | none
  let .arith .constant := result.op.getOpType! ctx | none
  let properties := result.op.getProperties! ctx (.arith .constant)
  return properties.value

def matchRemui (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.arith .remui)) := do
  let (op, properties) ← matchOp op ctx (.arith .remui) 2
  return (op[0]!, op[1]!, properties)
  
