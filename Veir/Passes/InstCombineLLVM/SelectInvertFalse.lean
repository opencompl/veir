module

public import Veir.Passes.InstCombineLLVM.SelectSemantics

namespace Veir.Passes.InstCombineLLVM.SelectInvertFalse

open Veir Puddle
open Veir.Passes.InstCombineLLVM

/-- Scalar specialization of InstCombineSelect.cpp:3961-3966:
    `select A, false, B -> select (not A), B, false`. -/
public def selectInvertFalse : Pattern OpCode := selectInvertPattern false

public theorem selectInvertFalse_valid : Pattern.Valid selectInvertFalse :=
  selectInvertPattern_valid false

end Veir.Passes.InstCombineLLVM.SelectInvertFalse
