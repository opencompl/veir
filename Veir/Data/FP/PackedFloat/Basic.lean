module

namespace Veir.Data.FP

namespace PackedFloat

public section

/--
A packed floating point number,
with exponent and significand widths encoded at the type level.
This implements the IEEE-754 floating point specification [1] of the bit layout.
[1] Muller, Jean-Michel, et al. Handbook of floating-point arithmetic.
    Vol. 1. Basel, Switzerland:: Birkhäuser, 2018.

-/
@[ext]
structure PackedFloat (exWidth sigWidth : Nat) where
    /-- Sign bit. -/
    sign : Bool
    /-- Exponent of the packed float. -/
    ex : BitVec exWidth
    /-- Significand (mantissa) of the packed float. -/
    sig : BitVec sigWidth
deriving DecidableEq, Repr, Inhabited
