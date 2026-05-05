module

public import Veir.Data.FP.ExtRat.Basic
public import Veir.Data.FP.PackedFloat.Basic
public import Veir.Data.FP.PackedFloat.State
public import Veir.Data.FP.Sign
public import Veir.ForLean

namespace Veir.Data.FP.PackedFloat

public section

/--
The exponent bias for a packed float with `e` exponent bits.
For a double (`e = 11`), this is `2^10 - 1 = 1023`.
-/
def bias (e : Nat) : Nat := 2 ^ (e - 1) - 1

/--
The fractional contribution of the trailing significand: `sig.toNat / 2^s`.
For a normal float this lies in `[0, 1)` and is added to the implicit leading
`1`; for a subnormal float this is multiplied by the minimum exponent directly.
-/
def sigFrac {s : Nat} (sig : BitVec s) : Rat :=
  (sig.toNat : Rat) / ((2 ^ s : Nat) : Rat)

def expFrac {e : Nat} (ex : BitVec e) : Rat :=
  Rat.twoPow (((Nat.min ex.toNat 1) : Int) - (bias e : Int))

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
  if pf.state = .infinite then .infinity pf.sign
  else if pf.state = .nan then .nan
  else if pf.state = .zero then .number 0
  else 
    -- subnormal or normal 
    .number (signToInt pf.sign * expFrac pf.ex * sigFrac pf.sig)
