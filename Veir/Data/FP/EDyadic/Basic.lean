module
public import Veir.Data.FP.Sign
public import Veir.Data.FP.ExtRat
public import Veir.Data.FP.ScientificBV

namespace Veir.Data.FP

public section

/--
An extended dyadic number (EScientificBV)
is a representation of a floating-point number
that includes the special values zero, infinity, and NaN.
-/
inductive EDyadic where
  /-- A zero with a sign bit. -/
  | zero (sign : Bool)
  /-- A nonzero finite number in scientific notation. -/
  | nonzeroFinite (d : Dyadic)
  /-- An infinite number with a sign bit. -/
  | infinity (sign : Bool)
  /-- A NaN (not a number). -/
  | nan
  deriving Inhabited

instance : Repr EDyadic where
  reprPrec 
    | .zero sign,  _ => s!"EDyadic.zero {sign}"
    | .nonzeroFinite d,  _ => s!"EDyadic.finite {repr d.toRat}"
    | .infinity sign, _ => s!"EDyadic.infinity {sign}"
    | .nan, _ => "EDyadic.nan"

end -- public section

end Veir.Data.FP

