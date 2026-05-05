module

public import Veir.Data.FP.PackedFloat
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
  match pf.state with
  | .nan => .nan
  | .infinite => .infinity pf.sign
  | .zero => .zero pf.sign
  | .subnormal => .nonzeroFinite <|
    { sign := pf.sign, ex := subnormalExp, sig := subnormalSig }
  | .normal => .nonzeroFinite <|
     { sign := pf.sign, ex := pf.ex.signExtend (scientificExpWidth e s) - BitVec.ofInt _ (PackedFloat.bias e), sig := pf.sig }
  where
      subnormalZeros := pf.sig.clz -- number of zeros in the significand that should be shifted by.
      shiftAmt := subnormalZeros + 1 -- number we need to shift by to eat the implicit leading 1.
      -- | see that we multiply the sig by 2^(subnormalZeros + 1),
      -- and we then divide by 2^(subnormalZeros + 1) in subtracting from the 'exp',
      -- to keep the rational interpretation unchanged.
      subnormalExp := BitVec.ofInt (scientificExpWidth e s) (1 - PackedFloat.bias e) - shiftAmt.zeroExtend (scientificExpWidth e s)
      subnormalSig := pf.sig <<< shiftAmt -- clear the zeros, and eat the implicit leading 1.

end Veir.Data.FP.PackedFloat

end


