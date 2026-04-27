module

namespace Veir.Data.FP

namespace PackedFloat

public section

/--
A packed floating point number of radix 2,
with exponent and significand widths encoded at the type level.
This definition implements Section 3.4, Figure 3.1 of the IEEE-754 standard [1].
We recommend [2] for a comprehensive introduction.
[1] IEEE 754-2019, https://standards.ieee.org/ieee/754/6210/
[2] Muller, Jean-Michel, et al. Handbook of floating-point arithmetic.
    Vol. 1. Basel, Switzerland:: Birkhäuser, 2018.
-/
@[ext]
structure PackedFloat (exWidth sigWidth : Nat) where
    /-- Sign bit. -/
    sign : Bool
    /-- Biased exponent of the packed float. -/
    ex : BitVec exWidth
    /-- Trailing significand (mantissa) of the packed float.
      Leading digit implicitly encoded by biased exponent. -/
    sig : BitVec sigWidth
deriving DecidableEq, Repr, Inhabited
