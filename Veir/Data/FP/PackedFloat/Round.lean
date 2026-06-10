module

public import Veir.Data.FP.PackedFloat.Basic
public import Veir.Data.FP.PackedFloat.ToEDyadic
public import Veir.Data.FP.EDyadic.Round
public import Veir.Data.FP.EDyadic.Pack

namespace Veir.Data.FP.PackedFloat

public section

/--
Round a `PackedFloat e s` into target format `PackedFloat etarget starget`
using the given IEEE-754 rounding mode.

The implementation is the composition
`PackedFloat → EDyadic → (rounded) EDyadic → PackedFloat`:
* `PackedFloat.toEDyadic` converts the input to its precise dyadic value
  (preserving NaN, ±∞, and ±0).
* `Dyadic.round mode` rounds finite nonzero values to a representable
  value in `(etarget, starget)` per the given rounding mode.
* `EDyadic.pack` re-encodes the result in the target packed format.

NaN, ±∞, and ±0 are propagated through; only the exponent and significand
widths change.
-/
def round {e s : Nat} (mode : RoundingMode) (etarget starget : Nat)
    (pf : PackedFloat e s) : PackedFloat etarget starget :=
  let edRounded : EDyadic :=
    match pf.toEDyadic with
    | .nonzeroFinite d hne => Dyadic.round mode d etarget starget hne
    | special => special
  EDyadic.pack etarget starget edRounded

end

end Veir.Data.FP.PackedFloat
