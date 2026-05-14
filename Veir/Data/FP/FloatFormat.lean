module

namespace Veir.Data.FP.FloatFormat

public section


/--
The IEEE-754 exponent bias for `e` exponent bits: `bias e = 2^(e-1) - 1`.
-/
def bias (e : Nat) : Nat := 2 ^ (e - 1) - 1

-- Single precision: `bias 8 = 2^7 - 1 = 127`.
#guard bias 8 = 127
-- Double precision: `bias 11 = 2^10 - 1 = 1023`.
#guard bias 11 = 1023

/--
The largest biased exponent representing a finite normal number: `2^e - 2`.

Recall that the all-ones bitpattern of `2^e - 1` is reserved for `±∞` / NaN.
Hence the largest finite biased exponent is `(2^e - 1) - 1 = 2^e - 2`.
-/
def maxBiasedExponent (e : Nat) : Nat := 2 ^ e - 2

-- Single precision: `maxBiasedExponent 8 = 2^8 - 2 = 254`.
#guard maxBiasedExponent 8 = 254
-- Double precision: `maxBiasedExponent 11 = 2^11 - 2 = 2046`.
#guard maxBiasedExponent 11 = 2046
/--
The smallest biased exponent representing a normal number: `1`.

Recall that the biased exponent `0` is reserved for `±0` and subnormals
The next pattern, `1`, is therefore the smallest exponent used by a normal,
as well as the exponent value for subnormals.
-/
def minBiasedExponent : Nat := 1

-- The minimum is independent of the format width.
#guard minBiasedExponent = 1

/--
The mathematical (unbiased) base-2 exponent of `n* 2^(-k)`

This gives us the exponent of `n * 2^(-k) = s * 2^unbiasedExp`,
where `s ∈ [1, 2)` is the significand after normalizing `n`.
-/
def unbiasedExp (n : Int) (k : Int) : Int :=
  (n.natAbs.log2 : Int) - k
/--
The IEEE-754 biased exponent, corresponding to a given unbiased exponent.
Obtained by adding the bias to the unbiased exponent.
-/
def biasedExp (e : Nat) (n : Int) (k : Int) : Int :=
  (bias e : Int) + unbiasedExp n k

/--
Left shift required to `n` such that when interprted as a `s`bit bitvector,
the leading `1` is in the `msb` position.

Suppose `n = 3 ~ 00011#5 (i.e. s = 5)`
Then `n.natAbs.log2 = 1`, and `normalSigShift s n = 5 - 1 = 4`.
This is because:

     n       <<< normalSigShift s n
  = 00011#5  <<< 4
  = 11000#5` [the leading `1` is at the `msb`]
-/
def normalSigShift (s : Nat) (n : Int) : Nat :=
  s - n.natAbs.log2

/--
Left shift required to align a subnormal number `n * 2^(-k)` to the `s`-bits.
Nonnegative iff `k ≤ bias e + s - 1` (subnormal representability).

Solving for `sig`:
  sig * 2^(-bias e - s + 1) = n * 2^(-k)
  sig = n * 2^(bias e + s - 1 - k)
  sig = n <<< (bias e + s - 1 - k)
               subnormal sig shift
-/
def subnormalSigShift (e s : Nat) (k : Int) : Int :=
  (bias e : Int) + (s : Int) - 1 - k

/--
Bitmask of the low `s` bits: `2^s - 1`.

Used to drop the hidden bit from a fully-aligned significand
`alignedSig ∈ [2^s, 2^(s+1))`. Since bit `s` is set and all higher bits
are clear in that range,
  `alignedSig &&& (2^s - 1) = alignedSig - 2^s`,
which is exactly the stored `s`-bit trailing significand.
-/
def trailingSigMask (s : Nat) : Nat := 2 ^ s - 1

end

end Veir.Data.FP.FloatFormat

