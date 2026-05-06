module
public import Veir.Data.FP.Sign
public import Veir.Data.FP.ExtRat
public import Veir.Data.FP.ScientificBV

namespace Veir.Data.FP

open ScientificBV

public section

/--
An extended scientific bitvector (EScientificBV)
is a representation of a floating-point number
that includes the special values zero, infinity, and NaN.
-/
inductive EScientificBV (e s : Nat) where
  /-- A zero with a sign bit. -/
  | zero (sign : Bool)
  /-- A nonzero finite number in scientific notation. -/
  | nonzeroFinite (sbv : ScientificBV e s)
  /-- An infinite number with a sign bit. -/
  | infinity (sign : Bool)
  /-- A NaN (not a number). -/
  | nan
  deriving Inhabited, Repr

end -- public section

end Veir.Data.FP
