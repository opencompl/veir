module
public import Veir.Data.FP.ScientificBV

namespace Veir.Data.FP

public section

/--
An extended dyadic number (EDyadic)
is a representation of a floating-point number
that includes the special values zero, infinity, and NaN.
-/
inductive EDyadic where
  /-- A zero with a sign bit. -/
  | zero (sign : Bool)
  /-- A nonzero finite number in dyadic notation.
  The proof `hne : d ≠ 0` enforces that `nonzeroFinite` is never used to
  represent zero: signed zeros live in the `zero` constructor.
  -/
  | nonzeroFinite (d : Dyadic) (hne : d ≠ 0)
  /-- An infinite number with a sign bit. -/
  | infinity (sign : Bool)
  /-- A NaN (not a number). -/
  | nan
  deriving Inhabited, DecidableEq

instance : Repr EDyadic where
  reprPrec
    | .zero sign,  _ => s!"EDyadic.zero {sign}"
    | .nonzeroFinite d _,  _ => s!"EDyadic.finite {repr d.toRat}"
    | .infinity sign, _ => s!"EDyadic.infinity {sign}"
    | .nan, _ => "EDyadic.nan"

namespace EDyadic

/--
Smart constructor that maps an arbitrary `Dyadic` into an `EDyadic`,
collapsing the `Dyadic.zero` case to `EDyadic.zero sign`. For nonzero
dyadics, the result is `.nonzeroFinite d _`, with the `d ≠ 0` proof
discharged automatically.
-/
def ofDyadic (sign : Bool) : Dyadic → EDyadic
  | .zero => .zero sign
  | .ofOdd n k hn => .nonzeroFinite (.ofOdd n k hn) Dyadic.of_ne_zero

end EDyadic

end -- public section

end Veir.Data.FP

