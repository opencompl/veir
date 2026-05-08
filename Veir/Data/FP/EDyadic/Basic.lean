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
  While dyadics can be zero, we use the `zero` constructor to
  represent zero values (so the sign is represent),
  and we use `nonzeroFinite` to represent nonzero values.
  Thus, there is an implicit invariant that the `nonzeroFinite`
  constructor should only be used with nonzero dyadics.
  -/
  | nonzeroFinite (d : Dyadic)
  /-- An infinite number with a sign bit. -/
  | infinity (sign : Bool)
  /-- A NaN (not a number). -/
  | nan
  deriving Inhabited, DecidableEq

instance : Repr EDyadic where
  reprPrec 
    | .zero sign,  _ => s!"EDyadic.zero {sign}"
    | .nonzeroFinite d,  _ => s!"EDyadic.finite {repr d.toRat}"
    | .infinity sign, _ => s!"EDyadic.infinity {sign}"
    | .nan, _ => "EDyadic.nan"

end -- public section

end Veir.Data.FP

