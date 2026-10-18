module

public import Veir.Passes.InstCombineLLVM.SelectSemantics

namespace Veir.Passes.InstCombineLLVM.SelectNestedFalse

open Veir Puddle
open Veir.Passes.InstCombineLLVM

/-- Scalar specialization of InstCombineSelect.cpp:4004-4006:
    `select (select A, B, false), B, false -> select A, B, false`. -/
public def selectNestedFalse : Pattern OpCode := selectNestedPattern false

public theorem selectNestedFalse_valid : Pattern.Valid selectNestedFalse :=
  selectNestedPattern_valid false

end Veir.Passes.InstCombineLLVM.SelectNestedFalse
