module

public import Veir.Data.FP.PackedFloat.Basic
public import Veir.Data.FP.EScientificBV

public section

namespace Veir.Data.FP

/--
When unpacking a `PackedFloat`, the exponent is represented in scientific notation,
Which requires `ceil(log2(s))` bits to represent the significand.
We approximate the `ceil(log2(s))` with (s.log2 + 1) to ensure we have
enough bits to represent the significand.
-/
def scientificExpWidth (e s : Nat) : Nat := 
  e + s.log2 + 1

namespace PackedFloat

def unpack (pf : PackedFloat e s) : EScientificBV (scientificExpWidth e s) s :=
  sorry

end Veir.Data.FP.PackedFloat

end


