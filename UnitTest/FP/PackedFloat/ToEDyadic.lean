module

import Veir.Data.FP.PackedFloat.ToEDyadic

meta import Veir.Data.FP.PackedFloat.OfFloat
meta import Veir.Data.FP.PackedFloat.ToEDyadic
meta import Veir.Data.FP.EDyadic.ToExtRat

namespace UnitTest.Fp.PackedFloat.ToEDyadic

open Veir.Data.FP
open Veir.Data.FP.PackedFloat

/-! ## Tests for `PackedFloat.toEDyadic` against Lean's native `Float`.

The conversion preserves the sign of `±0` (unlike `toExtRat`), and otherwise
agrees with `toExtRat` after passing through `EDyadic.toExtRat`. -/

#guard toEDyadic (ofFloat 0.0) = .zero false
#guard toEDyadic (ofFloat (-0.0)) = .zero true

#guard (toEDyadic (ofFloat 0.0)).toExtRat = .number 0
#guard (toEDyadic (ofFloat (-0.0))).toExtRat = .number 0

#guard (toEDyadic (ofFloat 1.0)).toExtRat = .number 1
#guard (toEDyadic (ofFloat (-1.0))).toExtRat = .number (-1)
#guard (toEDyadic (ofFloat 2.0)).toExtRat = .number 2
#guard (toEDyadic (ofFloat 0.5)).toExtRat = .number (1 / 2)
#guard (toEDyadic (ofFloat 1.5)).toExtRat = .number (3 / 2)
#guard (toEDyadic (ofFloat (-1.5))).toExtRat = .number (-3 / 2)
#guard (toEDyadic (ofFloat 1024.0)).toExtRat = .number 1024

#guard toEDyadic (ofFloat (1.0 / 0.0)) = .infinity false
#guard toEDyadic (ofFloat (-1.0 / 0.0)) = .infinity true
#guard toEDyadic (ofFloat (0.0 / 0.0)) = .nan

/-! ## Agreement with `PackedFloat.toExtRat`

For every finite, non-`±0` packed float, `(toEDyadic pf).toExtRat = pf.toExtRat`.
For `±0` the EDyadic preserves the sign while `toExtRat` collapses to `number 0`. -/

#guard (toEDyadic (ofFloat 1.0)).toExtRat = (ofFloat 1.0).toExtRat
#guard (toEDyadic (ofFloat (-1.0))).toExtRat = (ofFloat (-1.0)).toExtRat
#guard (toEDyadic (ofFloat 0.5)).toExtRat = (ofFloat 0.5).toExtRat
#guard (toEDyadic (ofFloat 1.5)).toExtRat = (ofFloat 1.5).toExtRat
#guard (toEDyadic (ofFloat 1024.0)).toExtRat = (ofFloat 1024.0).toExtRat
#guard (toEDyadic (ofFloat (1.0 / 0.0))).toExtRat = (ofFloat (1.0 / 0.0)).toExtRat

/-! ## Subnormals

The smallest representable positive double is the subnormal `2^(-1074)`. -/

def smallestPositiveSubnormal : PackedFloat 11 52 :=
  PackedFloat.mk (sign := false) (ex := 0#11) (sig := 1#52)

#guard (toEDyadic smallestPositiveSubnormal).toExtRat =
  .number (1 / ((2 ^ 1074 : Nat) : Rat))

/-- The negative counterpart: `-2^(-1074)`. -/
def smallestNegativeSubnormal : PackedFloat 11 52 :=
  PackedFloat.mk (sign := true) (ex := 0#11) (sig := 1#52)

#guard (toEDyadic smallestNegativeSubnormal).toExtRat =
  .number (-1 / ((2 ^ 1074 : Nat) : Rat))

end UnitTest.Fp.PackedFloat.ToEDyadic
