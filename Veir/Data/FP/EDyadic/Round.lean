module

namespace Veir.Data.FP

public section

/-- IEEE-754 rounding modes. -/
inductive RoundingMode
  /-- Round to nearest, tie away from zero. -/
  | RNA
  /-- Round to nearest, tie to even (default IEEE-754 mode). -/
  | RNE
  /-- Round toward negative infinity. -/
  | RTN
  /-- Round toward positive infinity. -/
  | RTP
  /-- Round toward zero. -/
  | RTZ
  deriving DecidableEq, Repr

namespace Dyadic

/-! ## Guard / sticky / even bits

Given the  number `x = sign * mag * 2^(-k)` (source precision `k`)
and a target precision `prec`, we wish to compute the guard, sticky, and even bits.
For these computations, the sign does not matter, so without loss of generality,
assume that sign is positive.

Suppose our number is of the form `mag = m5m4.m3m2m1m0`
(6 magnitude bits, k = 4 bits to the right of the point).

Suppose we are rounding to `prec = 1` bits of precision
(i.e., we want to keep 1 bit to the right of the point).
Then, the result must have the same `m5 m4` bits to the left of the point,
and we must choose whether to round down to `m5 m4 . 0` or up to `m5 m4 . 1`.

Therefore, we must choose between two options:
- lower = m5 m4 . 0
- upper = m5 m4 . 1

To perform this choice, we need three predicates that determine the rounding:
- Firstly, are we closer to `lower` or `upper`? See that the bit `m3` is zero
  iff we are strictly closer to `lower` , since the number
  `m5m4.0m2m1m0` is in the *lower half* of the interval `[m5m4.0, m5m4.1]`.
  The bit `m3` is called the *guard bit*.
- Next, are we *exactly* in between `lower` and `upper`?
  This happens iff `m3` is 1 and all the bits below it are zero.
  The rest of the bits below the guard bit (m3) are called *sticky bits*.
- Finally, for the rounding mode RNE, we need to know whether `lower`
  is even or odd. The rounding mode RNE rounds to the nearest even,
  to prevent statistical bias .
  For example, suppose we are rounding to 1 bit of precision. Then,
  both `01.10` (1.5) and `10.10` (2.5) will both round to `2.0` (2).
  This cancels the error of rounding up from `1.5 → 2` and the error
  of rounding down from `2.5 → 2` in the long run, preventing bias.
  This is computed by checking whether the truncated magnitude
  `m5 m4 . 0` is even or odd.


         LSB index of truncated mag.
         lsbIndex = 3 = k:4 - prec:1
         |
         v
m5 m4 . m3 m2 m1 m0
            ^ +---+
            |   |
            |   |
            guard bit index.
            guardBitIndex = 2 = (lsbIndex - 1) = k:4 - prec:1 - 1`
                |
                sticky bits indeces = [m1, m0]

  
-/

/--
The index of the LSB of the truncated magnitude
when rounding from source precision `k` to target precision `prec`.
-/
private def lsbIndex (k prec : Int) : Nat := (k - prec).toNat

/-- The bit position in `mag` of the guard bit when rounding from source
precision `k` to target precision `prec`: the highest bit strictly below
the target LSB. Equals `(k - prec) - 1`; well-defined only when `k > prec`. -/
private def guardBitIndex (k prec : Int) : Nat := lsbIndex k prec - 1

/-- The guard bit: bit of `mag` at position `guardBitIndex k prec`.
Returns `false` when `k ≤ prec` (no bits below the target LSB). -/
private def computeGuardBit (mag : Nat) (k prec : Int) : Bool :=
  if k ≤ prec then false else mag.testBit (guardBitIndex k prec)

/-- The sticky bit: `true` iff any bit of `mag` at a position strictly
below `guardBitIndex k prec` is set. Returns `false` when `k - prec ≤ 1`
(the sticky range below the guard is empty). -/
private def computeStickyBit (mag : Nat) (k prec : Int) : Bool :=
  if k - prec ≤ 1 then false
  else mag % (1 <<< guardBitIndex k prec) ≠ 0

/-- Whether the bit at the target LSB position is even.
This is used when implementing round to nearest even.
The truncated magnitude is even iff the LSB is false. -/
private def computeIsTruncatedMagEven (mag : Nat) (k prec : Int) : Bool :=
  ! mag.testBit (lsbIndex k prec)

end Dyadic

end

end Veir.Data.FP
