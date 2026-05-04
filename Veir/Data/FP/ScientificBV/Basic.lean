module
public import Veir.Data.FP.Sign

namespace Veir.Data.FP

namespace ScientificBV

public section

/--
`ScientificBV e s` is the *working* (scientific notation) representation of a
floating-point number with `e` bits for the exponent, and 
`s` bits for the significand.

The scientific bv `s` is interpreted as the rational number
given by the formula:

```
(-1)^s.sign * 2^(s.ex.toInt) * (1 + s.sig.toNat / 2^s)
```

Crucially, this means that we can only represent *non-zero*
numbers in the scientific format,
since the  implicit leading bit of the significand is always 1,
so the significand is interpreted as a number in [1, 2).
-/
@[ext]
structure ScientificBV (e s : Nat) where
  /-- Sign of the floating-point number. -/
  sign : Bool
  /-- Unbiased exponent, interpreted as an integer. -/
  ex : BitVec e
  /-- Significand, interpreted as a number in [1, 2).-/
  sig : BitVec s
  deriving Inhabited, Repr

/--
Treat a significand bitvector as a rational number in [1, 2),
where the leading bit is implicitly 1 and the trailing bits are interpreted as a fraction.
-/
def sigToRat (s : BitVec s) : Rat :=
  1 + s.toNat / (2 ^ s.toNat)

/--
Treat an exponent bitvector as a rational number,
power of two where the exponent is the bitvector interpreted as an integer.
-/
def exToRat (e : BitVec e) : Rat :=
  2 ^ e.toInt

/--
Convert a scientific bv to a rational number.
This provides semantics to `ScientificBV e s` in terms of rational numbers.
-/
def toRat {e s : Nat} (sbv : ScientificBV e s) : Rat :=
  let sign := signToInt sbv.sign
  let exponent := exToRat sbv.ex
  let significand := sigToRat sbv.sig
  sign * exponent * significand
