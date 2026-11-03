module

namespace Veir.Data.FP

public section

/--
A packed floating point number of radix 2 following IEEE 754 [1],
with exponent and significand widths encoded at the type level.
This definition implements Section 3.4, Figure 3.1 of the IEEE-754 standard [1].
We recommend [2] for a comprehensive introduction.
[1] IEEE 754-2019, https://standards.ieee.org/ieee/754/6210/
[2] Muller, Jean-Michel, et al. Handbook of floating-point arithmetic.
    Vol. 1. Basel, Switzerland:: Birkhäuser, 2018.
-/
@[ext]
structure PackedFloat (exWidth sigWidth : Nat) where
    /-- Sign bit -/
    sign : Bool
    /-- Biased exponent -/
    ex : BitVec exWidth
    /-- Trailing significand (mantissa) of the packed float.
     The leading bit of the significand is implicitly encoded in the biased exponent. -/
    sig : BitVec sigWidth
deriving DecidableEq, Repr, Inhabited

namespace PackedFloat

/--
A canonical NaN `PackedFloat`.
Recall that a NaN pattern is given by a maximum exponent (all-ones)
and a nonzero significand.
The IEEE-754 standard does not specify a unique NaN bit pattern,
so this constructor returns one with significand `1`.
-/
def mkNaN (e s : Nat) : PackedFloat e s :=
  { sign := false, ex := BitVec.allOnes e, sig := BitVec.ofNat s 1 }

/--
A signed `PackedFloat` infinity: biased exponent all-ones with a zero
trailing significand.
-/
def mkInfinity (e s : Nat) (sign : Bool) : PackedFloat e s :=
  { sign := sign, ex := BitVec.allOnes e, sig := 0#s }

/--
A signed `PackedFloat` zero: biased exponent and trailing significand both zero.
-/
def mkZero (e s : Nat) (sign : Bool) : PackedFloat e s :=
  { sign := sign, ex := 0#e, sig := 0#s }


end PackedFloat
