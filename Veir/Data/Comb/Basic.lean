module

public import Veir.Data.LLVM.Int.Basic

namespace Veir.Data.Comb

public section

/-! # CIRCT Comb Dialect Semantics -/

/--
Variadic `add` operation returns a poison value only if any of the arguments is poison, otherwise it returns the sum of the arguments.
-/
def add {w : Nat} (l : List (LLVM.Int w)) : LLVM.Int w := Id.run do
  let mut acc : BitVec w := 0
  for x in l do
    match x with
    | .poison => return .poison
    | .val x' => acc := acc + x'
  .val acc
