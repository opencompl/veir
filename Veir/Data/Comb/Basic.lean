module

public import Veir.Data.HW.Basic

namespace Veir.Data.Comb

public section

/-! # CIRCT Comb Dialect Semantics -/

variable {w : Nat}

@[inline]
private def foldl (args : Array (HW.Int w)) (f : BitVec w → BitVec w → BitVec w) (init : BitVec w) : HW.Int w :=
  args.foldl (⟨f ·.val ·.val⟩) ⟨init⟩

/--
  Variadic `add` returns the sum of its arguments with wrapping on overflow,
  or zero if it has no arguments.
-/
def add (args : Array (HW.Int w)) : HW.Int w :=
  foldl args (· + ·) 0#w

/--
  Variadic `and` returns the bitwise AND of its arguments, or a bitvector with
  all ones if it has no arguments.
-/
def and (args : Array (HW.Int w)) : HW.Int w :=
  foldl args (· &&& ·) (.allOnes w)

/--
  Variadic `mul` returns the product of its arguments with wrapping on overflow,
  or one if it has no arguments.
-/
def mul (args : Array (HW.Int w)) : HW.Int w :=
  foldl args (· * ·) 1#w

/--
  Variadic `or` returns the bitwise OR of its arguments, or zero if it has no
  arguments.
-/
def or (args : Array (HW.Int w)) : HW.Int w :=
  foldl args (· ||| ·) 0#w

/--
  Variadic `xor` returns the bitwise XOR of its arguments, or zero if it has no
  arguments.
-/
def xor (args : Array (HW.Int w)) : HW.Int w :=
  foldl args (· ^^^ ·) 0#w

end
end Veir.Data.Comb
