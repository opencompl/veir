module

import Veir.Data.FP.EDyadic.DivRound

meta import Veir.Data.FP.EDyadic.DivRound

namespace UnitTest.Fp.EDyadic.DivRound

open Veir.Data.FP

/-! ## Exact quotients (representable, no rounding)

When `a / b` is exactly representable in `(e, s)`, `divRound` returns it exactly. -/

-- 6 / 2 = 3
#guard EDyadic.divRound .RNE 11 52 (EDyadic.ofDyadic false 6) (EDyadic.ofDyadic false 2) =
  EDyadic.ofDyadic false 3
-- 1 / 2 = 0.5
#guard EDyadic.divRound .RNE 11 52 (EDyadic.ofDyadic false 1) (EDyadic.ofDyadic false 2) =
  EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 1 1)
-- 3 / 2 = 1.5
#guard EDyadic.divRound .RNE 11 52 (EDyadic.ofDyadic false 3) (EDyadic.ofDyadic false 2) =
  EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 3 1)
-- 7 / 4 = 1.75
#guard EDyadic.divRound .RNE 11 52 (EDyadic.ofDyadic false 7) (EDyadic.ofDyadic false 4) =
  EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 7 2)
-- -6 / 2 = -3
#guard EDyadic.divRound .RNE 11 52 (EDyadic.ofDyadic false (-6)) (EDyadic.ofDyadic false 2) =
  EDyadic.ofDyadic false (-3)
-- 6 / -4 = -1.5
#guard EDyadic.divRound .RNE 11 52 (EDyadic.ofDyadic false 6) (EDyadic.ofDyadic false (-4)) =
  EDyadic.ofDyadic false (Dyadic.ofIntWithPrec (-3) 1)

/-! ## Inexact quotients, correctly rounded (RNE) at a tiny format `(e, s) = (4, 2)`

`1/3 = 0.0101010…₂`. Normalized `1.0101…×2⁻²`; keeping 2 fraction bits with
guard bit `0` rounds down to `1.01×2⁻² = 0.3125 = 5·2⁻⁴`. -/

-- 1 / 3 → 0.3125
#guard EDyadic.divRound .RNE 4 2 (EDyadic.ofDyadic false 1) (EDyadic.ofDyadic false 3) =
  EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 5 4)
-- -1 / 3 → -0.3125
#guard EDyadic.divRound .RNE 4 2 (EDyadic.ofDyadic false (-1)) (EDyadic.ofDyadic false 3) =
  EDyadic.ofDyadic false (Dyadic.ofIntWithPrec (-5) 4)
-- 2 / 3 ≈ 0.6667 → 1.01×2⁻¹ = 0.625 = 5·2⁻³
#guard EDyadic.divRound .RNE 4 2 (EDyadic.ofDyadic false 2) (EDyadic.ofDyadic false 3) =
  EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 5 3)

/-! ## Special values (IEEE-754) -/

-- finite / 0 = ±∞
#guard EDyadic.divRound .RNE 11 52 (EDyadic.ofDyadic false 1) (EDyadic.zero false) =
  EDyadic.infinity false
#guard EDyadic.divRound .RNE 11 52 (EDyadic.ofDyadic false (-1)) (EDyadic.zero false) =
  EDyadic.infinity true
#guard EDyadic.divRound .RNE 11 52 (EDyadic.ofDyadic false 1) (EDyadic.zero true) =
  EDyadic.infinity true
-- 0 / 0 = NaN, ∞ / ∞ = NaN
#guard EDyadic.divRound .RNE 11 52 (EDyadic.zero false) (EDyadic.zero false) = EDyadic.nan
#guard EDyadic.divRound .RNE 11 52 (EDyadic.infinity false) (EDyadic.infinity false) = EDyadic.nan
-- finite / ∞ = ±0
#guard EDyadic.divRound .RNE 11 52 (EDyadic.ofDyadic false 1) (EDyadic.infinity false) =
  EDyadic.zero false
#guard EDyadic.divRound .RNE 11 52 (EDyadic.ofDyadic false 1) (EDyadic.infinity true) =
  EDyadic.zero true
-- 0 / finite = ±0
#guard EDyadic.divRound .RNE 11 52 (EDyadic.zero false) (EDyadic.ofDyadic false (-2)) =
  EDyadic.zero true
-- ∞ / finite = ±∞, ∞ / 0 = ±∞
#guard EDyadic.divRound .RNE 11 52 (EDyadic.infinity false) (EDyadic.ofDyadic false 2) =
  EDyadic.infinity false
#guard EDyadic.divRound .RNE 11 52 (EDyadic.infinity true) (EDyadic.zero false) =
  EDyadic.infinity true
-- NaN propagates
#guard EDyadic.divRound .RNE 11 52 EDyadic.nan (EDyadic.ofDyadic false 1) = EDyadic.nan
#guard EDyadic.divRound .RNE 11 52 (EDyadic.ofDyadic false 1) EDyadic.nan = EDyadic.nan

end UnitTest.Fp.EDyadic.DivRound
