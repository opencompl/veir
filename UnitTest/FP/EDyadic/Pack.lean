module

import Veir.Data.FP.EDyadic.Pack
import Veir.Data.FP.PackedFloat.ToEDyadic

meta import Veir.Data.FP.EDyadic.Pack
meta import Veir.Data.FP.PackedFloat.OfFloat
meta import Veir.Data.FP.PackedFloat.ToEDyadic
meta import Veir.Data.FP.PackedFloat.State

namespace UnitTest.Fp.EDyadic.Pack

open Veir.Data.FP
open Veir.Data.FP.PackedFloat

#guard EDyadic.pack (e := 11) (s := 52) (toEDyadic (ofFloat 0.0)) = ofFloat 0.0
#guard EDyadic.pack (e := 11) (s := 52) (toEDyadic (ofFloat (-0.0))) = ofFloat (-0.0)

#guard EDyadic.pack (e := 11) (s := 52) (toEDyadic (ofFloat 1.0)) = ofFloat 1.0
#guard EDyadic.pack (e := 11) (s := 52) (toEDyadic (ofFloat (-1.0))) = ofFloat (-1.0)
#guard EDyadic.pack (e := 11) (s := 52) (toEDyadic (ofFloat 2.0)) = ofFloat 2.0
#guard EDyadic.pack (e := 11) (s := 52) (toEDyadic (ofFloat 0.5)) = ofFloat 0.5
#guard EDyadic.pack (e := 11) (s := 52) (toEDyadic (ofFloat 1.5)) = ofFloat 1.5
#guard EDyadic.pack (e := 11) (s := 52) (toEDyadic (ofFloat (-1.5))) = ofFloat (-1.5)
#guard EDyadic.pack (e := 11) (s := 52) (toEDyadic (ofFloat 1024.0)) = ofFloat 1024.0

#guard EDyadic.pack (e := 11) (s := 52) (toEDyadic (ofFloat (1.0 / 0.0))) = ofFloat (1.0 / 0.0)
#guard EDyadic.pack (e := 11) (s := 52) (toEDyadic (ofFloat (-1.0 / 0.0))) = ofFloat (-1.0 / 0.0)

#guard (EDyadic.pack (e := 11) (s := 52) .nan).state = .nan

#guard EDyadic.pack (e := 11) (s := 52) (.zero false) =
  PackedFloat.mk (sign := false) (ex := 0#11) (sig := 0#52)
#guard EDyadic.pack (e := 11) (s := 52) (.zero true) =
  PackedFloat.mk (sign := true) (ex := 0#11) (sig := 0#52)
#guard EDyadic.pack (e := 11) (s := 52) (.infinity false) =
  PackedFloat.mk (sign := false) (ex := BitVec.allOnes 11) (sig := 0#52)
#guard EDyadic.pack (e := 11) (s := 52) (.infinity true) =
  PackedFloat.mk (sign := true) (ex := BitVec.allOnes 11) (sig := 0#52)

/-- Smallest positive representable double (subnormal `2^(-1074)`). -/
def smallestPositiveSubnormal : PackedFloat 11 52 :=
  PackedFloat.mk (sign := false) (ex := 0#11) (sig := 1#52)

#guard EDyadic.pack (e := 11) (s := 52) (toEDyadic smallestPositiveSubnormal) =
  smallestPositiveSubnormal

/-- The negative counterpart: `-2^(-1074)`. -/
def smallestNegativeSubnormal : PackedFloat 11 52 :=
  PackedFloat.mk (sign := true) (ex := 0#11) (sig := 1#52)

#guard EDyadic.pack (e := 11) (s := 52) (toEDyadic smallestNegativeSubnormal) =
  smallestNegativeSubnormal

/-- A larger subnormal with several bits set in the significand. -/
def someSubnormal : PackedFloat 11 52 :=
  PackedFloat.mk (sign := false) (ex := 0#11) (sig := 7#52)

#guard EDyadic.pack (e := 11) (s := 52) (toEDyadic someSubnormal) = someSubnormal

/-- The packed value `1.0` in `(e, s) = (5, 10)`: bias `15`, biased exponent `15`. -/
def oneHalfPrec : PackedFloat 5 10 :=
  PackedFloat.mk (sign := false) (ex := 15#5) (sig := 0#10)

#guard EDyadic.pack (e := 5) (s := 10) (toEDyadic oneHalfPrec) = oneHalfPrec

/-- Smallest positive subnormal in `(5, 10)`: `2^(-24)`. -/
def smallestPositiveSubnormalHalf : PackedFloat 5 10 :=
  PackedFloat.mk (sign := false) (ex := 0#5) (sig := 1#10)

#guard EDyadic.pack (e := 5) (s := 10) (toEDyadic smallestPositiveSubnormalHalf) =
  smallestPositiveSubnormalHalf

/-- Largest finite normal in `(5, 10)`: biased exponent `30`, all significand bits set. -/
def largestNormalHalf : PackedFloat 5 10 :=
  PackedFloat.mk (sign := false) (ex := 30#5) (sig := BitVec.allOnes 10)

#guard EDyadic.pack (e := 5) (s := 10) (toEDyadic largestNormalHalf) = largestNormalHalf

end UnitTest.Fp.EDyadic.Pack
