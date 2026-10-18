module

public import Veir.Passes.InstCombineLLVM.SelectSemantics

namespace Veir.Passes.InstCombineLLVM.SelectInvertTrue

open Veir Puddle
open Veir.Passes.InstCombineLLVM

/-- Scalar specialization of InstCombineSelect.cpp:3969-3974:
    `select A, B, true -> select (not A), true, B`. -/
public def selectInvertTrue : Pattern OpCode := selectInvertPattern true

public theorem selectInvertTrue_valid : Pattern.Valid selectInvertTrue :=
  selectInvertPattern_valid true

end Veir.Passes.InstCombineLLVM.SelectInvertTrue
