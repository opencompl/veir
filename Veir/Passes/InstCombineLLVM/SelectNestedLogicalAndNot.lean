module

public import Veir.Passes.InstCombineLLVM.SelectSemantics

namespace Veir.Passes.InstCombineLLVM.SelectNestedLogicalAndNot

open Veir Puddle
open Veir.Passes.InstCombineLLVM

/-- Scalar specialization of InstCombineSelect.cpp:5166:
    `select(C0, select(C1, B, A), B) -> select(C0 && !C1, A, B)`. -/
public def selectNestedLogicalAndNot : Pattern OpCode :=
  selectNestedLogicalNotPattern true

public theorem selectNestedLogicalAndNot_valid :
    Pattern.Valid selectNestedLogicalAndNot :=
  selectNestedLogicalNotPattern_valid true

end Veir.Passes.InstCombineLLVM.SelectNestedLogicalAndNot
