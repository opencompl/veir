module

import Veir.Data.FP.EDyadic.Round

meta import Veir.Data.FP.EDyadic.Round

namespace UnitTest.Fp.EDyadic.Position

open Veir.Data.FP

/-! ## `computeIsLowerHalf` -/

-- `mag = 4 = 0b100`, source `k = 3`, target `prec = 0`, format `e = 11`:
-- guard bit at position 2 is `1`, so the value `4/8 = 0.5` is at the
-- midpoint — *not* in the strict lower half.
#guard Dyadic.computeIsLowerHalf false 4 3 0 11 = false
-- `mag = 3 = 0b011`: guard bit at position 2 is `0`, so `3/8` is in the strict lower half.
#guard Dyadic.computeIsLowerHalf false 3 3 0 11 = true
-- For negative inputs lower and upper swap, so the lower-half check is inverted.
#guard Dyadic.computeIsLowerHalf true 4 3 0 11 = true
-- For overflow: `mag = 1`, `k = -8` (= `2^8 = 256`) in `(e = 4, …)` where
-- `maxFinite ≈ 240`. The Nonneg/Neg variants' override fires.
#guard Dyadic.computeIsLowerHalf false 1 (-8) (-5) 4 = false
#guard Dyadic.computeIsLowerHalf true 1 (-8) (-5) 4 = true

/-! ## `computeIsTieBreak` -/

-- `4 = 0b100`: guard `= 1`, sticky `= 0` ⇒ exact midpoint.
#guard Dyadic.computeIsTieBreak 4 3 0 11 = true
-- `5 = 0b101`: guard `= 1` but sticky `= 1` ⇒ past midpoint, not a tie.
#guard Dyadic.computeIsTieBreak 5 3 0 11 = false
-- `3 = 0b011`: guard `= 0` ⇒ below midpoint, not a tie.
#guard Dyadic.computeIsTieBreak 3 3 0 11 = false
-- Overflow is never a tie.
#guard Dyadic.computeIsTieBreak 1 (-8) (-5) 4 = false

/-! ## `computeIsLowerEven` / `computeIsUpperEven` -/

-- `mag = 6 = 0b110`, `k = 2`, `prec = 0`: truncated mantissa bit (position 2) is `1`
-- ⇒ truncated mag (`= 1`) is odd; for nonneg `x`, lower = trunc is odd,
-- so `isLowerEven` is `false` and `isUpperEven` (trunc+1 = 2) is `true`.
#guard Dyadic.computeIsLowerEven false 6 2 0 = false
#guard Dyadic.computeIsUpperEven false 6 2 0 = true
-- For negative `x`, lower and upper swap roles, so the parities flip.
#guard Dyadic.computeIsLowerEven true 6 2 0 = true
#guard Dyadic.computeIsUpperEven true 6 2 0 = false

end UnitTest.Fp.EDyadic.Position
