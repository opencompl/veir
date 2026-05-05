module

import Veir.Data.FP.PackedFloat.ToExtRat
import Veir.Data.FP.PackedFloat.Unpack
import Veir.Data.FP.EScientificBV.ToExtRat

meta import Veir.Data.FP.PackedFloat.OfFloat
meta import Veir.Data.FP.PackedFloat.ToExtRat
public meta import Veir.Data.FP.PackedFloat.Unpack
public meta import Veir.Data.FP.EScientificBV.ToExtRat

namespace UnitTest.Fp.PackedFloat.Unpack

open Veir.Data.FP
open Veir.Data.FP.PackedFloat
open Veir.Data.FP.EScientificBV

/-! ## Tests for `PackedFloat.unpack`

For each test float `f`, we create a `PackedFloat` via `ofFloat f` and then
verify that `toExtRat pf = pf.unpack.toExtRat`.  This checks that `unpack`
preserves the mathematical value of the float. -/

-- zero
#guard toExtRat (ofFloat 0.0) = (ofFloat 0.0).unpack.toExtRat
-- negative zero (both should map to 0)
#guard toExtRat (ofFloat (-0.0)) = (ofFloat (-0.0)).unpack.toExtRat

-- positive one (sig = 0, normal)
#guard toExtRat (ofFloat 1.0) = (ofFloat 1.0).unpack.toExtRat
-- negative one (sig = 0, normal)
#guard toExtRat (ofFloat (-1.0)) = (ofFloat (-1.0)).unpack.toExtRat

-- two (sig = 0, normal)
#guard toExtRat (ofFloat 2.0) = (ofFloat 2.0).unpack.toExtRat

-- 0.5 (sig = 0, normal)
#guard toExtRat (ofFloat 0.5) = (ofFloat 0.5).unpack.toExtRat

-- 1.5 (sig ≠ 0, normal)
#guard toExtRat (ofFloat 1.5) = (ofFloat 1.5).unpack.toExtRat
-- negative 1.5 (sig ≠ 0, normal)
#guard toExtRat (ofFloat (-1.5)) = (ofFloat (-1.5)).unpack.toExtRat

-- 1024.0 (sig = 0, normal)
#guard toExtRat (ofFloat 1024.0) = (ofFloat 1024.0).unpack.toExtRat

-- positive infinity
#guard toExtRat (ofFloat (1.0 / 0.0)) = (ofFloat (1.0 / 0.0)).unpack.toExtRat
-- negative infinity
#guard toExtRat (ofFloat (-1.0 / 0.0)) = (ofFloat (-1.0 / 0.0)).unpack.toExtRat

-- NaN
#guard toExtRat (ofFloat (0.0 / 0.0)) = (ofFloat (0.0 / 0.0)).unpack.toExtRat

/-! ## Subnormals -/

/-- Smallest positive representable double (subnormal).
The biased exponent is `0` and the trailing significand is `1`,
so its exact value is `2^(1-1023) * 1/2^52 = 2^(-1074)`. -/
def smallestPositiveSubnormal : PackedFloat 11 52 :=
  PackedFloat.mk (sign := false) (ex := 0#11) (sig := 1#52)

#guard toExtRat smallestPositiveSubnormal = smallestPositiveSubnormal.unpack.toExtRat

end UnitTest.Fp.PackedFloat.Unpack
