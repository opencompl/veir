module
public import Veir.Data.FP.Sign

namespace Veir.Data.FP

namespace UnpackedFloat

public section

/--
`UnpackedFloat e s` is the *working* (unpacked) representation of a floating-point
number with `e` bits for the exponent and `s` bits for the significand.

The unpacked float `uf` is interpreted as the rational number
given by the formula:

```
(-1)^uf.sign * 2^(uf.ex.toInt) * (1 + uf.sig.toNat / 2^s)
```

Crucially, this means that we can only represent *non-zero*
numbers in the unpacked format,
since the  implicit leading bit of the significand is always 1,
so the significand is interpreted as a number in [1, 2).
-/
@[ext]
structure UnpackedFloat (e s : Nat) where
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
where the exponent is interpreted as an integer.
-/
def exToRat (e : BitVec e) : Rat :=
  2 ^ e.toInt

/--
Convert an unpacked float to a rational number.
This provides semantics to `UnpackedFloat e s` in terms of rational numbers.
-/
def toRat {e s : Nat} (uf : UnpackedFloat e s) : Rat :=
  let sign := signToInt uf.sign
  let exponent := exToRat uf.ex
  let significand := sigToRat uf.sig
  sign * exponent * significand
