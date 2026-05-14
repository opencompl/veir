module

import Veir.Data.FP.PackedFloat.State
public import Veir.Data.FP.PackedFloat.ToExtRat
import Veir.Data.FP.Sign
public import Veir.Data.FP.EDyadic.Basic

namespace Veir.Data.FP.PackedFloat

public section

/--
Convert a `PackedFloat e s` to its precise mathematical value as an `EDyadic`,
following the IEEE-754 interpretation:
- biased exponent `allOnes` with non-zero significand → `nan`
- biased exponent `allOnes` with zero significand → signed `infinity`
- biased exponent `0` with zero significand → signed `zero`
- biased exponent `0` with non-zero significand → subnormal:
  `sig.toNat * 2^(1 - bias - s)` (with sign on the integer)
- otherwise normal:
  `(2^s + sig.toNat) * 2^(ex.toNat - bias - s)` (with sign on the integer)

Unlike `toExtRat`, this preserves the sign of `±0`.
-/
def toEDyadic {e s : Nat} (pf : PackedFloat e s) : EDyadic :=
  if pf.state = .nan then .nan
  else if pf.state = .infinite then .infinity pf.sign
  else if pf.state = .zero then .zero pf.sign
  else
    -- normal, subnormal.
    EDyadic.ofDyadic pf.sign
      (Dyadic.ofIntWithPrec (signToInt pf.sign * sig) prec)
  where
    sig := pf.sig.toNat  + 2 ^ s * (decide (pf.state = .normal)).toNat
    prec := (FloatFormat.bias e : Int) + (s : Int) - (Nat.max pf.ex.toNat 1)


end

end Veir.Data.FP.PackedFloat
