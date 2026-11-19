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
  `extract` returns a range of bits to fill the output type, starting from
  `lowBit` and padding with zeros if required.
-/
def extract {w₁ : Nat} (x : HW.Int w₁) (lowBit : Nat) (w₂ : Nat) : HW.Int w₂ :=
  ⟨x.val.extractLsb' lowBit w₂⟩

/--
  Variadic `mul` returns the product of its arguments with wrapping on overflow,
  or one if it has no arguments.
-/
def mul (args : Array (HW.Int w)) : HW.Int w :=
  foldl args (· * ·) 1#w

/--
  `mux` returns `t` if the condition evaluates to one; otherwise it returns `f`.
-/
def mux (c : HW.Int 1) (t f : HW.Int w) : HW.Int w :=
  if (c.val == 1#1) then t else f

/--
  Variadic `or` returns the bitwise OR of its arguments, or zero if it has no
  arguments.
-/
def or (args : Array (HW.Int w)) : HW.Int w :=
  foldl args (· ||| ·) 0#w

/--
  `parity` returns the even parity bit of the input bitvector. If an even number
  of bits are set, this is zero; otherwise it is one.
-/
def parity (x : HW.Int w) : HW.Int 1 :=
  ⟨x.val.cpop.truncate 1⟩

/--
  `replicate` concatenates copies of the bits of the input to reach the result
  width.
-/
def replicate {w₁ : Nat} (x : HW.Int w₁) (w₂ : Nat) : HW.Int w₂ :=
  ⟨x.val.replicate (w₂ + w₁ / w₁) |>.setWidth w₂⟩

/--
  `reverse` reverses the order of the bits in the input.
-/
def reverse (x : HW.Int w) : HW.Int w :=
  ⟨x.val.reverse⟩

/--
  `shl` returns the first operand shifted to the left by the value of the
  second operand.
-/
def shl (x y : HW.Int w) : HW.Int w :=
  ⟨x.val <<< y.val⟩

/--
  `shrs` (signed/arithmetic shift right) returns the first operand shifted
  to the right with sign extension by the value of the second operand.
-/
def shrs (x y : HW.Int w) : HW.Int w :=
  ⟨x.val.sshiftRight' y.val⟩

/--
  `shru` (unsigned/logical shift right) returns the first operand shifted
  to the right with zero extension by the value of the second operand.
-/
def shru (x y : HW.Int w) : HW.Int w :=
  ⟨x.val >>> y.val⟩

/--
  `sub` returns the bitvector subtraction of the second value from the first
  with wrapping underflow.
-/
def sub (x y : HW.Int w) : HW.Int w :=
  ⟨x.val - y.val⟩

/--
  Variadic `xor` returns the bitwise XOR of its arguments, or zero if it has no
  arguments.
-/
def xor (args : Array (HW.Int w)) : HW.Int w :=
  foldl args (· ^^^ ·) 0#w

end
end Veir.Data.Comb
