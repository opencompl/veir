module

public import Veir.Passes.InstCombineLLVM.SelectSemantics

namespace Veir.Passes.InstCombineLLVM.SelectNestedLogicalOrNot

open Veir Puddle
open Veir.Passes.InstCombineLLVM

/-- Scalar specialization of InstCombineSelect.cpp:5197:
    `select(C0, A, select(C1, B, A)) -> select(C0 || !C1, A, B)`. -/
public def selectNestedLogicalOrNot : Pattern OpCode :=
  selectNestedLogicalNotPattern false

public theorem selectNestedLogicalOrNot_valid : Pattern.Valid selectNestedLogicalOrNot :=
  selectNestedLogicalNotPattern_valid false

end Veir.Passes.InstCombineLLVM.SelectNestedLogicalOrNot
