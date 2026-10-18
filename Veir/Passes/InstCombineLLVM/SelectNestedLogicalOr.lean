module

public import Veir.Passes.InstCombineLLVM.SelectSemantics

namespace Veir.Passes.InstCombineLLVM.SelectNestedLogicalOr

open Veir Puddle
open Veir.Passes.InstCombineLLVM

/-- Scalar specialization of InstCombineSelect.cpp:5197:
    `select(C0, A, select(C1, A, B)) -> select(C0 || C1, A, B)`. -/
public def selectNestedLogicalOr : Pattern OpCode :=
  selectNestedLogicalPattern false

public theorem selectNestedLogicalOr_valid : Pattern.Valid selectNestedLogicalOr :=
  selectNestedLogicalPattern_valid false

end Veir.Passes.InstCombineLLVM.SelectNestedLogicalOr
