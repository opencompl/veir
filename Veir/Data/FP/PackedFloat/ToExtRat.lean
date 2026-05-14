module

public import Veir.Data.FP.ExtRat.Basic
public import Veir.Data.FP.FloatFormat
public import Veir.Data.FP.PackedFloat.Basic
public import Veir.Data.FP.Sign
public import Veir.ForLean

namespace Veir.Data.FP.PackedFloat

public section

open FloatFormat (bias)

/--
The fractional contribution of the trailing significand: `sig.toNat / 2^s`.
For a normal float this lies in `[0, 1)` and is added to the implicit leading
`1`; for a subnormal float this is multiplied by the minimum exponent directly.
-/
def sigFrac {s : Nat} (sig : BitVec s) : Rat :=
  (sig.toNat : Rat) / ((2 ^ s : Nat) : Rat)

/--
Convert a `PackedFloat e s` to its precise mathematical value as an `ExtRat`,
following the IEEE-754 interpretation (Section 3.4 of the IEEE-754 standard,
https://standards.ieee.org/ieee/754/6210/):
- biased exponent `allOnes` with non-zero significand → `NaN`
- biased exponent `allOnes` with zero significand → signed `Infinity`
- biased exponent `0` with zero significand → `Number 0` (sign discarded)
- biased exponent `0` with non-zero significand → subnormal:
  `(-1)^sign * 2^(1 - bias) * (sig / 2^s)`
- otherwise normal:
  `(-1)^sign * 2^(ex - bias) * (1 + sig / 2^s)`
-/
def toExtRat {e s : Nat} (pf : PackedFloat e s) : ExtRat :=
  if pf.ex = BitVec.allOnes e then
    if pf.sig = 0#s then .infinity pf.sign
    else .nan
  else if pf.ex = 0#e then
    if pf.sig = 0#s then .number 0
    else
      .number (signToInt pf.sign * Rat.twoPow (1 - (bias e : Int)) * sigFrac pf.sig)
  else
    .number (signToInt pf.sign *
      Rat.twoPow ((pf.ex.toNat : Int) - (bias e : Int)) * (1 + sigFrac pf.sig))
