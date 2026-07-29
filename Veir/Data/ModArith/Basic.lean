module

namespace Veir.Data.ModArith

public section

/-! # `mod_arith` Dialect Semantics -/

/--
The value denoted by `mod_arith.constant` is the canonical representative of
its integer attribute modulo `modulus`.
-/
@[expose]
def constant (modulus value : Int) : Int :=
  value % modulus
