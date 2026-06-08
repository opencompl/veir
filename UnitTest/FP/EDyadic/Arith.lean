module

import Veir.Data.FP.EDyadic.Arith

meta import Veir.Data.FP.EDyadic.Arith

namespace UnitTest.Fp.EDyadic.Arith

open Veir.Data.FP

/-! ## Exact addition

Finite dyadics add exactly (no rounding). We compare against the dyadic
value built directly with `Dyadic.ofIntWithPrec n prec` (value `n · 2^(-prec)`). -/

-- 1 + 2 = 3
#guard EDyadic.add (EDyadic.ofDyadic false 1) (EDyadic.ofDyadic false 2) =
  EDyadic.ofDyadic false 3
-- 0.5 + 0.5 = 1   (0.5 = 1·2^-1)
#guard EDyadic.add (EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 1 1))
    (EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 1 1)) = EDyadic.ofDyadic false 1
-- 1.5 + 2.5 = 4
#guard EDyadic.add (EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 3 1))
    (EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 5 1)) = EDyadic.ofDyadic false 4
-- 0.25 + 0.5 = 0.75   (3·2^-2)
#guard EDyadic.add (EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 1 2))
    (EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 1 1)) =
  EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 3 2)
-- exact cancellation 1 + (-1) = +0
#guard EDyadic.add (EDyadic.ofDyadic false 1) (EDyadic.ofDyadic false (-1)) =
  EDyadic.zero false
-- `+` instance
#guard (EDyadic.ofDyadic false 1) + (EDyadic.ofDyadic false 2) = EDyadic.ofDyadic false 3

/-! ## Exact subtraction -/

-- 3 - 1 = 2
#guard EDyadic.sub (EDyadic.ofDyadic false 3) (EDyadic.ofDyadic false 1) =
  EDyadic.ofDyadic false 2
-- 1 - 2 = -1
#guard (EDyadic.ofDyadic false 1) - (EDyadic.ofDyadic false 2) = EDyadic.ofDyadic false (-1)
-- 0.5 - 0.25 = 0.25
#guard EDyadic.sub (EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 1 1))
    (EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 1 2)) =
  EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 1 2)

/-! ## Exact multiplication -/

-- 1.5 * 2 = 3
#guard EDyadic.mul (EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 3 1))
    (EDyadic.ofDyadic false 2) = EDyadic.ofDyadic false 3
-- 1.5 * 1.5 = 2.25   (9·2^-2)
#guard EDyadic.mul (EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 3 1))
    (EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 3 1)) =
  EDyadic.ofDyadic false (Dyadic.ofIntWithPrec 9 2)
-- (-2) * 3 = -6
#guard (EDyadic.ofDyadic false (-2)) * (EDyadic.ofDyadic false 3) =
  EDyadic.ofDyadic false (-6)
-- (-2) * (-3) = 6
#guard EDyadic.mul (EDyadic.ofDyadic false (-2)) (EDyadic.ofDyadic false (-3)) =
  EDyadic.ofDyadic false 6

/-! ## Special values (IEEE-754) -/

-- NaN propagates
#guard EDyadic.add EDyadic.nan (EDyadic.ofDyadic false 1) = EDyadic.nan
#guard EDyadic.mul (EDyadic.ofDyadic false 1) EDyadic.nan = EDyadic.nan
-- ∞ + ∞ = ∞ (same sign); ∞ + (-∞) = NaN
#guard EDyadic.add (EDyadic.infinity false) (EDyadic.infinity false) = EDyadic.infinity false
#guard EDyadic.add (EDyadic.infinity false) (EDyadic.infinity true) = EDyadic.nan
-- ∞ + finite = ∞
#guard EDyadic.add (EDyadic.infinity true) (EDyadic.ofDyadic false 5) = EDyadic.infinity true
-- signed zeros
#guard EDyadic.add (EDyadic.zero true) (EDyadic.zero true) = EDyadic.zero true
#guard EDyadic.add (EDyadic.zero false) (EDyadic.zero true) = EDyadic.zero false
#guard EDyadic.add (EDyadic.zero true) (EDyadic.ofDyadic false 2) = EDyadic.ofDyadic false 2
-- ∞ * 0 = NaN
#guard EDyadic.mul (EDyadic.infinity false) (EDyadic.zero false) = EDyadic.nan
-- ∞ * finite = ∞ with xor sign
#guard EDyadic.mul (EDyadic.infinity false) (EDyadic.ofDyadic false (-2)) = EDyadic.infinity true
-- ∞ * ∞ sign
#guard EDyadic.mul (EDyadic.infinity true) (EDyadic.infinity true) = EDyadic.infinity false
-- 0 * finite = signed 0
#guard EDyadic.mul (EDyadic.zero false) (EDyadic.ofDyadic false (-3)) = EDyadic.zero true
#guard EDyadic.mul (EDyadic.zero true) (EDyadic.ofDyadic false (-3)) = EDyadic.zero false

end UnitTest.Fp.EDyadic.Arith
