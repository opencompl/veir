module

public import Veir.Passes.Matching.Basic
public import Veir.Dialects.Builtin.OpInfo

public section

/-! This file contains helper functions to match Builtin operations when defining a rewrite. -/

namespace Veir

variable {OpCode : Type} [HasOpInfo OpCode] [HasDialect OpCode Builtin]

def matchCastOp (op : OperationPtr) (ctx : IRContext OpCode) : Option ValuePtr := do
  let (op, _) ← matchOp op ctx Builtin.unrealized_conversion_cast 1
  return op[0]!
