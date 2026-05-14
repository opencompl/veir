module

public import Veir.Data.HW.Basic

namespace Veir.Data.COMB

public section

/-! # CIRCT Comb Dialect Semantics -/

/--
Variadic `add` operation with a list of bitvectors with width `w` as input
-/
def add {w : Nat} (l : List (BitVec w)) : BitVec w :=
  List.foldr BitVec.add (0#w) l
