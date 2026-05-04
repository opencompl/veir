module

public import Veir.Data.FP.ExtRat.Basic
public import Veir.Data.FP.PackedFloat.Basic
public import Veir.Data.FP.PackedFloat.OfFloat
public import Veir.Data.FP.Sign

public meta import Veir.Data.FP.ExtRat.Basic
public meta import Veir.Data.FP.PackedFloat.OfFloat
public meta import Veir.Data.FP.Sign

namespace Veir.Data.FP.PackedFloat

public section

/--
The exponent bias for a packed float with `e` exponent bits.
For a double (`e = 11`), this is `2^10 - 1 = 1023`.
-/
def bias (e : Nat) : Nat := 2 ^ (e - 1) - 1

/-- `2` raised to a (possibly negative) integer power, as a `Rat`. -/
def pow2 (k : Int) : Rat :=
  if k ≥ 0 then ((2 ^ k.toNat : Nat) : Rat)
  else 1 / ((2 ^ (-k).toNat : Nat) : Rat)

/--
The fractional contribution of the trailing significand: `sig.toNat / 2^s`.
For a normal float this lies in `[0, 1)` and is added to the implicit leading
`1`; for a subnormal float it is multiplied by the minimum exponent directly.
-/
def sigFrac {s : Nat} (sig : BitVec s) : Rat :=
  (sig.toNat : Rat) / ((2 ^ s : Nat) : Rat)

/--
Convert a `PackedFloat e s` to its precise mathematical value as an `ExtRat`,
following the IEEE-754 interpretation:
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
    if pf.sig = 0#s then ExtRat.Infinity pf.sign
    else ExtRat.NaN
  else if pf.ex = 0#e then
    if pf.sig = 0#s then ExtRat.Number 0
    else
      ExtRat.Number (signToInt pf.sign * pow2 (1 - (bias e : Int)) * sigFrac pf.sig)
  else
    ExtRat.Number (signToInt pf.sign *
      pow2 ((pf.ex.toNat : Int) - (bias e : Int)) * (1 + sigFrac pf.sig))

/-! ## Tests against Lean's native `Float` (IEEE-754 double) -/

#guard toExtRat (ofFloat 0.0) = ExtRat.Number 0
#guard toExtRat (ofFloat (-0.0)) = ExtRat.Number 0
#guard toExtRat (ofFloat 1.0) = ExtRat.Number 1
#guard toExtRat (ofFloat (-1.0)) = ExtRat.Number (-1)
#guard toExtRat (ofFloat 2.0) = ExtRat.Number 2
#guard toExtRat (ofFloat (-2.0)) = ExtRat.Number (-2)
#guard toExtRat (ofFloat 0.5) = ExtRat.Number (1 / 2)
#guard toExtRat (ofFloat 0.25) = ExtRat.Number (1 / 4)
#guard toExtRat (ofFloat 1.5) = ExtRat.Number (3 / 2)
#guard toExtRat (ofFloat (-1.5)) = ExtRat.Number (-3 / 2)
#guard toExtRat (ofFloat 1024.0) = ExtRat.Number 1024
#guard toExtRat (ofFloat (1.0 / 0.0)) = ExtRat.Infinity false
#guard toExtRat (ofFloat (-1.0 / 0.0)) = ExtRat.Infinity true
#guard toExtRat (ofFloat (0.0 / 0.0)) = ExtRat.NaN
