module

public import Veir.Passes.Matching.Basic
public import Veir.Dialects.GMIR.OpInfo

public section

/-! This file contains helper functions to match gMIR operations when defining a rewrite. -/

namespace Veir

variable {OpCode : Type} [HasOpInfo OpCode] [HasDialect OpCode GMIR]

/--
Like `matchConstantIntVal`, for a `gmir.g_constant`.
TODO: Use this instead of `matchConstantIntVal` once instruction selection fully runs on gMIR.
-/
def matchGConstantIntVal (val : ValuePtr) (ctx : IRContext OpCode) : Option Int := do
  let .opResult opResultPtr := val | none
  let (_, props) ← matchOp opResultPtr.op ctx GMIR.g_constant 0
  let .integerType type := (val.getType! ctx).val | none
  return (BitVec.ofInt type.bitwidth props.value.value).toInt
