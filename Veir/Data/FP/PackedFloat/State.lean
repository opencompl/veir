module

public import Veir.Data.FP.PackedFloat.Basic
public import Veir.Data.FP.State

namespace Veir.Data.FP.PackedFloat

public section

/--
The state of the packed float, as defined by the exponent and significand bits,
following the IEEE-754 interpretation (Section 3.4 of the IEEE-754 standard,
https://standards.ieee.org/ieee/754/6210/):
- biased exponent `allOnes` with non-zero significand → `.nan`
- biased exponent `allOnes` with zero significand → `.infinite`
- biased exponent `0` with zero significand → `.zero`
- biased exponent `0` with non-zero significand → `.subnormal`
- biased exponent between 1 and allOnes - 1 (inclusive) → `.normal`
-/
def state (pf : PackedFloat e s) : State :=
  if pf.ex = BitVec.allOnes e then
    if pf.sig = 0#s then .infinite
    else .nan
  else if pf.ex = 0#e then
    if pf.sig = 0#s then .zero
    else .subnormal
  else .normal

end

