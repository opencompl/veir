module

public import Veir.Data.FP.FloatFormat
public import Veir.Data.FP.PackedFloat.Basic
public import Veir.Data.FP.PackedFloat.ToExtRat
public import Veir.Data.FP.EDyadic.Basic

namespace Veir.Data.FP.EDyadic

public section

open FloatFormat (biasedExp normalSigShift subnormalSigShift trailingSigMask
  minBiasedExponent maxBiasedExponent)

/-- Pack a nonzero dyadic `(-1)^sign * |n| * 2^(-k)` (with `n` odd) into a `PackedFloat e s`. -/
def packOfOdd (e s : Nat) (n k : Int) : PackedFloat e s :=
  -- Sign extracted from the integer numerator.
  let sign : Bool := decide (n < 0)
  -- Biased exponent of the value in the target format.
  let biasedEx : Int := biasedExp e n k
  -- Boundary between normal and overflow regimes.
  let maxEx : Int := (maxBiasedExponent e : Int)
  if (minBiasedExponent : Int) ≤ biasedEx ∧ biasedEx ≤ maxEx then
    -- Normal range. Align `|n|` so its leading bit lands at position `s`,
    -- giving the full significand (with hidden bit) in `[2^s, 2^(s+1))`.
    let alignedSig : Nat := n.natAbs <<< normalSigShift s n
    -- Mask out the implicit hidden bit to obtain the stored trailing
    -- significand (equivalent to `alignedSig - 2^s` since bit `s` is set).
    let trailingSig : Nat := alignedSig &&& trailingSigMask s
    PackedFloat.mkNumber sign (BitVec.ofInt e biasedEx) (BitVec.ofNat s trailingSig)
  else if biasedEx ≤ 0 then
    -- Subnormal range. Stored exponent is zero; shift `|n|` into the
    -- subnormal grid so its value matches `|n| * 2^(-k)` at the scale
    -- `2^(-bias - s + 1)`.
    let subnormalSig : Nat := n.natAbs <<< (subnormalSigShift e s k).toNat
    PackedFloat.mkNumber sign 0#e (BitVec.ofNat s subnormalSig)
  else
    -- Overflow: biased exponent exceeds `maxBiasedExponent`; saturate.
    PackedFloat.mkInfinity e s sign

/-- Pack an `EDyadic` value into a `PackedFloat e s`; `∀ (x : PackedFloat e s), pack (toEDyadic x) = x` on representable `x`. -/
def pack (e s : Nat) : EDyadic → PackedFloat e s
  | .nan => PackedFloat.mkNaN e s
  | .infinity sign => PackedFloat.mkInfinity e s sign
  | .zero sign => PackedFloat.mkZero e s sign
  | .nonzeroFinite (.ofOdd n k _) _ => packOfOdd e s n k

end

end Veir.Data.FP.EDyadic
