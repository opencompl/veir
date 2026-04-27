module

namespace Veir.Data.FP

namespace PackedFloat

public section

/--
A packed floating point number,
with exponent and significand widths encoded at the type level.
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
