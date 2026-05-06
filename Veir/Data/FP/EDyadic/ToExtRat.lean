module

public import Veir.Data.FP.EDyadic
public import Veir.Data.FP.ExtRat

namespace Veir.Data.FP.EDyadic

public section

/--
Compute the extended rational value of an `EDyadic`.
The result is a rational number if the value is finite
and is either infinity or NaN otherwise.

There is one place where this function is not injective:
When the input is ±0, the result is `0`, losing the sign bit.
Everywhere else, the function is injective.
-/
def toExtRat : EDyadic → ExtRat
  | .zero _ => .number 0
  | .nonzeroFinite d => .number d.toRat
  | .infinity sign => .infinity sign
  | .nan => .nan

  end

