module

import Veir.Data.FP.PackedFloat.ToExtRat

meta import Veir.Data.FP.PackedFloat.OfFloat
meta import Veir.Data.FP.PackedFloat.ToExtRat

namespace UnitTest.Fp.PackedFloat.ToExtRat

open Veir.Data.FP
open Veir.Data.FP.PackedFloat

/-! ## Tests against Lean's native `Float` (IEEE-754 double)

These tests check `PackedFloat.toExtRat` against the values produced by
reinterpreting Lean's native `Float` (an IEEE-754 double) via
`PackedFloat.ofFloat`. -/

#guard toExtRat (ofFloat 0.0) = .number 0
#guard toExtRat (ofFloat (-0.0)) = .number 0
#guard toExtRat (ofFloat 1.0) = .number 1
#guard toFloat (ofFloat 1.0) == 1.0

#guard toExtRat (ofFloat (-1.0)) = .number (-1)
#guard toFloat (ofFloat (-1.0)) == -1.0

#guard toExtRat (ofFloat 2.0) = .number 2
#guard toFloat (ofFloat (2.0)) == 2.0

#guard toExtRat (ofFloat 0.5) = .number (1 / 2)
#guard toFloat (ofFloat (0.5)) == 0.5

#guard toExtRat (ofFloat 1.5) = .number (3 / 2)
#guard toFloat (ofFloat (1.5)) == 1.5

#guard toExtRat (ofFloat (-1.5)) = .number (-3 / 2)
#guard toFloat (ofFloat (-1.5)) == -1.5

#guard toExtRat (ofFloat 1024.0) = .number 1024
#guard toFloat (ofFloat (1024.0)) == 1024.0

#guard toExtRat (ofFloat (1.0 / 0.0)) = .infinity false
#guard toFloat (ofFloat (1.0 / 0.0)) == 1.0 / 0.0

#guard toExtRat (ofFloat (-1.0 / 0.0)) = .infinity true
#guard toFloat (ofFloat (-1.0 / 0.0)) == -1.0 / 0.0

#guard toExtRat (ofFloat (0.0 / 0.0)) = .nan
#guard Float.isNaN <| toFloat (ofFloat (0.0 / 0.0))

/-! ## Subnormals

The smallest representable positive double is the subnormal whose biased
exponent is `0` and whose trailing significand is `1`:
`+0 * 2^(1 - 1023) * (1 / 2^52) = 2^(-1074) = 1 / 2^1074`. -/

/-- Smallest positive representable double (subnormal). -/
def smallestPositiveSubnormal : PackedFloat 11 52 :=
  PackedFloat.mk (sign := false) (ex := 0#11) (sig := 1#52)

/-
Construct the float that 'smallestPositiveSubnormal'
corresponds to as a Lean float.
The subnormal is larger than zero, but I'm not sure how to
test precisely that it is the machine epsilon.
-/
#guard toFloat smallestPositiveSubnormal > 0.0

#guard toExtRat smallestPositiveSubnormal =
  .number (1 / ((2 ^ 1074 : Nat) : Rat))
