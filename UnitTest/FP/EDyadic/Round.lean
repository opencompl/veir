module

import Veir.Data.FP.EDyadic.Round
import Veir.Data.FP.EDyadic.Pack
import Veir.Data.FP.PackedFloat.ToEDyadic

meta import Veir.Data.FP.EDyadic.Round
meta import Veir.Data.FP.EDyadic.Pack
meta import Veir.Data.FP.PackedFloat.OfFloat
meta import Veir.Data.FP.PackedFloat.ToEDyadic

namespace UnitTest.Fp.EDyadic.Round

open Veir.Data.FP
open Veir.Data.FP.PackedFloat

/-! ## Identity on representable values

A `Dyadic` whose precision already fits in the target format rounds to
itself. -/

#guard Dyadic.round .RNE 0 11 52 = .zero false
#guard Dyadic.round .RNE (Dyadic.ofIntWithPrec 1 0) 11 52 =
  .nonzeroFinite (Dyadic.ofIntWithPrec 1 0)
#guard Dyadic.round .RNE (Dyadic.ofIntWithPrec 3 1) 11 52 =
  .nonzeroFinite (Dyadic.ofIntWithPrec 3 1)
#guard Dyadic.round .RNE (Dyadic.ofIntWithPrec (-3) 1) 11 52 =
  .nonzeroFinite (Dyadic.ofIntWithPrec (-3) 1)

/-! ## Tie-break to even (RNE)

At an integer-grade format `(e, s) = (4, 0)`, the only representable
finite values are integers. Tie cases (`x.5`) round to the even integer. -/

-- 1.5 → 2 (between 1 and 2; pick even = 2)
#guard Dyadic.round .RNE (Dyadic.ofIntWithPrec 3 1) 4 0 = .nonzeroFinite 2
-- 2.5 → 2 (between 2 and 3; pick even = 2)
#guard Dyadic.round .RNE (Dyadic.ofIntWithPrec 5 1) 4 0 = .nonzeroFinite 2
-- 3.5 → 4 (between 3 and 4; pick even = 4)
#guard Dyadic.round .RNE (Dyadic.ofIntWithPrec 7 1) 4 0 = .nonzeroFinite 4
-- −1.5 → −2
#guard Dyadic.round .RNE (Dyadic.ofIntWithPrec (-3) 1) 4 0 = .nonzeroFinite (-2)
-- −2.5 → −2
#guard Dyadic.round .RNE (Dyadic.ofIntWithPrec (-5) 1) 4 0 = .nonzeroFinite (-2)

/-! ## Strict closer-of-two (non-tie)

Values strictly closer to one bracket round there. -/

-- 1.25 → 1 (closer to 1 than 2)
#guard Dyadic.round .RNE (Dyadic.ofIntWithPrec 5 2) 4 0 = .nonzeroFinite 1
-- 1.75 → 2 (closer to 2 than 1)
#guard Dyadic.round .RNE (Dyadic.ofIntWithPrec 7 2) 4 0 = .nonzeroFinite 2
-- −1.75 → −2
#guard Dyadic.round .RNE (Dyadic.ofIntWithPrec (-7) 2) 4 0 = .nonzeroFinite (-2)

/-! ## `lower` and `upper` bracket the input -/

-- lower(1.5) = 1, upper(1.5) = 2 in integer format
#guard Dyadic.lower (Dyadic.ofIntWithPrec 3 1) 4 0 = .nonzeroFinite 1
#guard Dyadic.upper (Dyadic.ofIntWithPrec 3 1) 4 0 = .nonzeroFinite 2

-- lower/upper of an exactly representable value collapse to the value.
#guard Dyadic.lower (Dyadic.ofIntWithPrec 2 0) 4 0 = .nonzeroFinite 2
#guard Dyadic.upper (Dyadic.ofIntWithPrec 2 0) 4 0 = .nonzeroFinite 2

-- lower/upper for negative: lower(-1.5) = -2, upper(-1.5) = -1.
#guard Dyadic.lower (Dyadic.ofIntWithPrec (-3) 1) 4 0 = .nonzeroFinite (-2)
#guard Dyadic.upper (Dyadic.ofIntWithPrec (-3) 1) 4 0 = .nonzeroFinite (-1)

/-! ## Overflow / infinity

Values beyond `maxFinite + half_ulp` (RNE boundary) round to ±∞.
For `(e, s) = (4, 3)`: bias = 7, maxFinite = (2^4 − 1) · 2^4 = 240.
Half-ulp = 2^3 = 8. RNE boundary = 248. -/

-- 256 = 2^8 is past the boundary → +∞.
#guard Dyadic.round .RNE (Dyadic.ofIntWithPrec 1 (-8 : Int)) 4 3 = .infinity false
-- −256 → −∞.
#guard Dyadic.round .RNE (Dyadic.ofIntWithPrec (-1) (-8 : Int)) 4 3 = .infinity true

-- lower(256) = +maxFinite = 240 in (4, 3); upper(256) = +∞.
#guard Dyadic.lower (Dyadic.ofIntWithPrec 1 (-8 : Int)) 4 3 =
  .nonzeroFinite 240
#guard Dyadic.upper (Dyadic.ofIntWithPrec 1 (-8 : Int)) 4 3 = .infinity false

-- lower(-256) = -∞; upper(-256) = -maxFinite = -240.
#guard Dyadic.lower (Dyadic.ofIntWithPrec (-1) (-8 : Int)) 4 3 = .infinity true
#guard Dyadic.upper (Dyadic.ofIntWithPrec (-1) (-8 : Int)) 4 3 =
  .nonzeroFinite (-240)

/-! ## Subnormals

Format `(4, 3)`: bias = 7, smallest subnormal = `2^(1 − 7 − 3) = 2^(-9)`.
A value smaller than half-min-subnormal rounds to `+0`. -/

-- 2^(-9): the smallest representable positive value, rounds to itself.
#guard Dyadic.round .RNE (Dyadic.ofIntWithPrec 1 9) 4 3 =
  .nonzeroFinite (Dyadic.ofIntWithPrec 1 9)

-- 2^(-10) is half the smallest subnormal: tie between 0 and 2^(-9).
-- Tie to even: 0 is even, so round to +0.
#guard Dyadic.round .RNE (Dyadic.ofIntWithPrec 1 10) 4 3 = .zero false

-- 3 · 2^(-11) = 2^(-9) · 3/4: closer to 2^(-9) than to 0, rounds up.
#guard Dyadic.round .RNE (Dyadic.ofIntWithPrec 3 11) 4 3 =
  .nonzeroFinite (Dyadic.ofIntWithPrec 1 9)

/-! ## Round-trip via `pack ∘ round` against IEEE-754 doubles

For doubles already representable in the format, `round` is the identity
on the dyadic value, and `pack` recovers the original bit pattern. -/

def asDyadic (pf : PackedFloat 11 52) : Dyadic :=
  match toEDyadic pf with
  | .nonzeroFinite d => d
  | _ => 0

#guard EDyadic.pack 11 52 (Dyadic.round .RNE (asDyadic (ofFloat 1.0)) 11 52) =
  ofFloat 1.0
#guard EDyadic.pack 11 52 (Dyadic.round .RNE (asDyadic (ofFloat 1.5)) 11 52) =
  ofFloat 1.5
#guard EDyadic.pack 11 52 (Dyadic.round .RNE (asDyadic (ofFloat (-1.5))) 11 52) =
  ofFloat (-1.5)
#guard EDyadic.pack 11 52 (Dyadic.round .RNE (asDyadic (ofFloat 0.5)) 11 52) =
  ofFloat 0.5
#guard EDyadic.pack 11 52 (Dyadic.round .RNE (asDyadic (ofFloat 1024.0)) 11 52) =
  ofFloat 1024.0

end UnitTest.Fp.EDyadic.Round
