module

public import Veir.Passes.InstCombineLLVM.SelectSemantics

namespace Veir.Passes.InstCombineLLVM.SelectNestedLogicalAnd

open Veir Puddle
open Veir.Passes.InstCombineLLVM

/-- Scalar specialization of InstCombineSelect.cpp:5166:
    `select(C0, select(C1, A, B), B) -> select(C0 && C1, A, B)`. -/
public def selectNestedLogicalAnd : Pattern OpCode :=
  selectNestedLogicalPattern true

public theorem selectNestedLogicalAnd_valid : Pattern.Valid selectNestedLogicalAnd :=
  selectNestedLogicalPattern_valid true

end Veir.Passes.InstCombineLLVM.SelectNestedLogicalAnd
