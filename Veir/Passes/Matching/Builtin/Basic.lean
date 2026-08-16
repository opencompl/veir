module

public import Veir.Passes.Matching.Basic

public section

/-! This file contains helper functions to match Builtin operations when defining a rewrite. -/

namespace Veir

def matchCastOp (op : OperationPtr) (ctx : IRContext OpCode) : Option ValuePtr := do
  let (op, _) ← matchOp op ctx (.builtin .unrealized_conversion_cast) 1
  return op[0]!
