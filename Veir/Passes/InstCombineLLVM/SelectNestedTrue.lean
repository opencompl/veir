module

public import Veir.Passes.InstCombineLLVM.SelectSemantics

namespace Veir.Passes.InstCombineLLVM.SelectNestedTrue

open Veir Puddle
open Veir.Passes.InstCombineLLVM

/-- Scalar specialization of InstCombineSelect.cpp:4000-4002:
    `select (select A, true, B), true, B -> select A, true, B`. -/
public def selectNestedTrue : Pattern OpCode := selectNestedPattern true

public theorem selectNestedTrue_valid : Pattern.Valid selectNestedTrue :=
  selectNestedPattern_valid true

end Veir.Passes.InstCombineLLVM.SelectNestedTrue
