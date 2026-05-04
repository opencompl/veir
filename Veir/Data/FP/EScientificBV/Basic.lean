module
public import Veir.Data.FP.Sign
public import Veir.Data.FP.ExtRat
public import Veir.Data.FP.ScientificBV

namespace Veir.Data.FP

namespace EScientificBV

open ScientificBV

public section

/--
An extended scientific bitvector (EScientificBV)
is a representation of floating-point numbers
that includes the special values such as zero, infinity, and NaN.
-/
inductive EScientificBV (e s : Nat) where
  /-- zero with a sign bit. -/
  | zero (sign : Bool)
  /-- a nonzero finite number in scientific notation. -/ 
  | nonzeroFinite (sbv : ScientificBV e s)
  /-- an infinite number with a sign bit. -/
  | infinite (sign : Bool)
  /-- a NaN (not a number). -/
  | nan
  deriving Inhabited, Repr

def toExtRat {e s : Nat} : EScientificBV e s → Option ExtRat
  | .zero sign => some (ExtRat.zero)
  | .nonzeroFinite sbv => some (ExtRat.nonzeroFinite (toRat sbv))
  | .infinite sign => some (ExtRat.infinite sign)
  | .nan => none

end -- public section

end Veir.Data.FP.EScientificBV

