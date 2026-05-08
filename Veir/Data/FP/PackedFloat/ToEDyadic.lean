module

public import Veir.Data.FP.PackedFloat.Basic
public import Veir.Data.FP.PackedFloat.ToExtRat
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
  if pf.ex = BitVec.allOnes e then
    if pf.sig = 0#s then .infinity pf.sign
    else .nan
  else if pf.ex = 0#e then
    if pf.sig = 0#s then .zero pf.sign
    else
      let n : Int :=
        if pf.sign then -(pf.sig.toNat : Int) else (pf.sig.toNat : Int)
      let prec : Int := (bias e : Int) + (s : Int) - 1
      .nonzeroFinite (Dyadic.ofIntWithPrec n prec)
  else
    let mantissa : Nat := 2 ^ s + pf.sig.toNat
    let n : Int := if pf.sign then -(mantissa : Int) else (mantissa : Int)
    let prec : Int := (bias e : Int) + (s : Int) - (pf.ex.toNat : Int)
    .nonzeroFinite (Dyadic.ofIntWithPrec n prec)

end -- public section

end Veir.Data.FP.PackedFloat
