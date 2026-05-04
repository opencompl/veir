module

namespace Veir.Data.FP

public section

/--
Extended rational numbers: rationals augmented with `NaN` and signed infinities.
This is the mathematical model that an IEEE-754 floating-point number is
interpreted as: every bit pattern of a `PackedFloat` corresponds to either
`NaN`, a signed infinity (where sign=true indicates negative infinity),
or a precise rational number.
-/
inductive ExtRat where
  | nan : ExtRat
  | infinity : (sign : Bool) → ExtRat
  | number : Rat → ExtRat
deriving DecidableEq, Repr, Inhabited
