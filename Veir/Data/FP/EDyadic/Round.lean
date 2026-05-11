module

public import Veir.Data.FP.EDyadic.Basic
public import Veir.Data.FP.PackedFloat.Basic
public import Veir.Data.FP.PackedFloat.ToExtRat

namespace Veir.Data.FP

public section

/--
IEEE-754 rounding modes.
* `RNA`: round to nearest, tie away from zero.
* `RNE`: round to nearest, tie to even (default IEEE-754 mode).
* `RTN`: round toward negative infinity.
* `RTP`: round toward positive infinity.
* `RTZ`: round toward zero.
-/
inductive RoundingMode
  | RNA
  | RNE
  | RTN
  | RTP
  | RTZ
  deriving DecidableEq, Repr

namespace Dyadic

/-! ## Exponent classification and target precision -/

/--
The biased exponent that `x` would have when encoded in target format
`(e, _)`. The result classifies `x`'s exponent:
* `≤ 0`: subnormal range,
* `[1, 2^e - 2]`: normal range,
* `≥ 2^e - 1`: overflows the format.
-/
private def biasedExp (x : Dyadic) (e : Nat) : Int :=
  match x with
  | .zero => 0
  | .ofOdd n k _ => (PackedFloat.bias e : Int) + (n.natAbs.log2 : Int) - k

/--
Rounding precision (in the sense of `Dyadic.roundDown`/`roundUp`) used
when rounding `x` into target format `(e, s)`. Subnormals share the
precision `bias + s - 1`; normals at biased exponent `eVal` use
`bias + s - eVal`.
-/
private def targetPrec (x : Dyadic) (e s : Nat) : Int :=
  let eVal := biasedExp x e
  let eClamped := if eVal ≤ 1 then 1 else eVal
  (PackedFloat.bias e : Int) + (s : Int) - eClamped

/-! ## Guard / sticky / even bits

These mirror `UnpackedFloat.computeExtract{GuardBit,StickyBit,IsEven}`
but on the unsigned magnitude `absN` of `x = n * 2^(-k)`. The shift
count `b` is the number of bits below the target LSB: the guard bit is
at position `b - 1` of `absN`, sticky is the OR of positions below the
guard bit, and even asks whether the LSB of the truncated mantissa
(position `b`) is zero. -/

/-- Guard bit: bit at position `b - 1` of `absN`. -/
private def computeExtractGuardBit (absN : Nat) (b : Nat) : Bool :=
  if b = 0 then false else absN.testBit (b - 1)

/-- Sticky bit: any bit below position `b - 1` of `absN` is set. -/
private def computeExtractStickyBit (absN : Nat) (b : Nat) : Bool :=
  if b ≤ 1 then false
  else absN % (1 <<< (b - 1)) ≠ 0

/-- LSB of the truncated mantissa is zero. -/
private def computeExtractIsEven (absN : Nat) (b : Nat) : Bool :=
  ! absN.testBit b

/--
A value needs rounding iff some bits below the target LSB are set,
i.e., either the guard or the sticky bit is set.
-/
private def needsRounding (absN : Nat) (b : Nat) : Bool :=
  computeExtractGuardBit absN b || computeExtractStickyBit absN b

/-! ## Round-toward-zero and successor-away-from-zero

Mirror `UnpackedFloat.computeRoundTowardZero` and
`UnpackedFloat.computeSuccessorAwayFromZero`. These work on the unsigned
magnitude `absN` and produce the unsigned magnitude of the result. -/

/-- Truncated magnitude: `absN >>> b`. -/
private def computeRoundTowardZeroMag (absN : Nat) (b : Nat) : Nat :=
  absN >>> b

/-- Successor of the truncated magnitude (one ULP away from zero). -/
private def computeSuccessorAwayFromZeroMag (absN : Nat) (b : Nat) : Nat :=
  computeRoundTowardZeroMag absN b + 1

/--
The successor-or-self magnitude: the successor if rounding is needed,
otherwise the truncated magnitude (which equals the input).
-/
private def computeSuccessorAwayFromZeroNonnegAuxMag (absN : Nat) (b : Nat) : Nat :=
  if needsRounding absN b then computeSuccessorAwayFromZeroMag absN b
  else computeRoundTowardZeroMag absN b

/-! ## Building dyadics from a magnitude and sign -/

/-- Embed an unsigned magnitude as a signed `Dyadic` at precision `prec`. -/
private def magToDyadic (sign : Bool) (mag : Nat) (prec : Int) : Dyadic :=
  if sign then Dyadic.ofIntWithPrec (-(mag : Int)) prec
  else Dyadic.ofIntWithPrec (mag : Int) prec

/-! ## `lower` / `upper` magnitudes (nonneg / neg)

Mirror `UnpackedFloat.computeLower{Nonneg,Neg}` and
`UnpackedFloat.computeUpper{Nonneg,Neg}`. For `x ≥ 0` the bracketing
magnitudes are `(trunc, trunc+1?)`. For `x < 0` the brackets reverse
in sign: `lower = -upperNonneg`, `upper = -lowerNonneg`. -/

/-- For `x ≥ 0`: lower = truncated magnitude. -/
private def computeLowerNonneg (absN : Nat) (b : Nat) (prec : Int) : Dyadic :=
  magToDyadic false (computeRoundTowardZeroMag absN b) prec

/-- For `x ≥ 0`: upper = successor-or-self of the truncated magnitude. -/
private def computeUpperNonneg (absN : Nat) (b : Nat) (prec : Int) : Dyadic :=
  magToDyadic false (computeSuccessorAwayFromZeroNonnegAuxMag absN b) prec

/-- For `x < 0`: lower = `-upperNonneg`. -/
private def computeLowerNeg (absN : Nat) (b : Nat) (prec : Int) : Dyadic :=
  -(computeUpperNonneg absN b prec)

/-- For `x < 0`: upper = `-lowerNonneg`. -/
private def computeUpperNeg (absN : Nat) (b : Nat) (prec : Int) : Dyadic :=
  -(computeLowerNonneg absN b prec)

/-- Sign-aware lower of `x = ±absN * 2^(-k)`. -/
private def computeLower (sign : Bool) (absN : Nat) (b : Nat) (prec : Int) : Dyadic :=
  if sign then computeLowerNeg absN b prec else computeLowerNonneg absN b prec

/-- Sign-aware upper of `x = ±absN * 2^(-k)`. -/
private def computeUpper (sign : Bool) (absN : Nat) (b : Nat) (prec : Int) : Dyadic :=
  if sign then computeUpperNeg absN b prec else computeUpperNonneg absN b prec

/-! ## Position predicates: lower-half, tie-break, even

Mirror `UnpackedFloat.computeIs{LowerHalf,TieBreak,Even}` and the
`Lower`/`Upper` parity helpers. -/

/-- Nonneg `x`: x is in the lower half iff guard bit is zero. -/
private def computeIsLowerHalfNonneg (absN : Nat) (b : Nat) : Bool :=
  ! computeExtractGuardBit absN b

/--
Neg `x`: x is in the lower half (i.e., closer to the more-negative
bracket) iff guard bit is one. This mirrors
`uf.neg.computeExtractGuardBit` in the unpacked-float setting.
-/
private def computeIsLowerHalfNeg (absN : Nat) (b : Nat) : Bool :=
  computeExtractGuardBit absN b

/-- Sign-aware "x is in the lower half of `[lower, upper]`". -/
private def computeIsLowerHalf (sign : Bool) (absN : Nat) (b : Nat) : Bool :=
  if sign then computeIsLowerHalfNeg absN b else computeIsLowerHalfNonneg absN b

/--
Tie-break: `x` is exactly at the midpoint. This is symmetric across
sign: guard bit set with no sticky bits below.
-/
private def computeIsTieBreak (_sign : Bool) (absN : Nat) (b : Nat) : Bool :=
  computeExtractGuardBit absN b && ! computeExtractStickyBit absN b

/-- Whether the *lower* bracket's mantissa is even (sign-aware). -/
private def computeIsEven (sign : Bool) (absN : Nat) (b : Nat) : Bool :=
  if sign then ! computeExtractIsEven absN b
  else computeExtractIsEven absN b

/-- Whether the lower bracket's mantissa is even. -/
private def computeIsEvenLower (sign : Bool) (absN : Nat) (b : Nat) : Bool :=
  computeIsEven sign absN b

/-- Whether the upper bracket's mantissa is even. -/
private def computeIsEvenUpper (sign : Bool) (absN : Nat) (b : Nat) : Bool :=
  ! computeIsEven sign absN b

/-! ## Per-mode rounding (mirrors `computeSmtLibRound{RNE,RNA,RTP,RTN,RTZ}`)

Each `computeSmtLibRound*` returns the rounded `Dyadic`. Overflow on the
result (and the input early-overflow case) is handled by the
public-facing `round`. -/

/-- Round-to-nearest, tie to even. -/
private def computeSmtLibRoundRNE
    (sign : Bool) (absN : Nat) (b : Nat) (prec : Int) : Dyadic :=
  if ! computeIsLowerHalf sign absN b && ! computeIsTieBreak sign absN b then
    computeUpper sign absN b prec
  else if computeIsTieBreak sign absN b && computeIsEvenUpper sign absN b then
    computeUpper sign absN b prec
  else if computeIsTieBreak sign absN b && computeIsEvenLower sign absN b then
    computeLower sign absN b prec
  else if computeIsLowerHalf sign absN b then
    computeLower sign absN b prec
  else
    -- unreachable: the four cases partition all (lowerHalf, tieBreak)
    -- combinations except `(lowerHalf=true, tieBreak=true)`, which
    -- can't occur (lowerHalf and tieBreak demand opposite guard bits
    -- in the nonneg case; for neg both fire only together with the
    -- even/odd check covering it).
    computeLower sign absN b prec

/-- Round-to-nearest, tie away from zero. -/
private def computeSmtLibRoundRNA
    (sign : Bool) (absN : Nat) (b : Nat) (prec : Int) : Dyadic :=
  if sign = false && ! computeIsLowerHalf sign absN b then
    computeUpper sign absN b prec
  else if sign = false && computeIsLowerHalf sign absN b then
    computeLower sign absN b prec
  else if sign = true && ! computeIsLowerHalf sign absN b
        && ! computeIsTieBreak sign absN b then
    computeUpper sign absN b prec
  else if sign = true
        && (computeIsLowerHalf sign absN b || computeIsTieBreak sign absN b) then
    computeLower sign absN b prec
  else
    computeLower sign absN b prec

/-- Round toward `+∞`: pick the upper bracket. -/
private def computeSmtLibRoundRTP
    (sign : Bool) (absN : Nat) (b : Nat) (prec : Int) : Dyadic :=
  computeUpper sign absN b prec

/-- Round toward `−∞`: pick the lower bracket. -/
private def computeSmtLibRoundRTN
    (sign : Bool) (absN : Nat) (b : Nat) (prec : Int) : Dyadic :=
  computeLower sign absN b prec

/-- Round toward zero: pick the bracket whose magnitude is smaller. -/
private def computeSmtLibRoundRTZ
    (sign : Bool) (absN : Nat) (b : Nat) (prec : Int) : Dyadic :=
  if sign then computeUpper sign absN b prec
  else computeLower sign absN b prec

/--
Dispatcher: round per the given mode. Mirrors
`UnpackedFloat.computeSmtLibRoundAux`.
-/
private def computeSmtLibRoundAux (mode : RoundingMode)
    (sign : Bool) (absN : Nat) (b : Nat) (prec : Int) : Dyadic :=
  match mode with
  | .RNE => computeSmtLibRoundRNE sign absN b prec
  | .RNA => computeSmtLibRoundRNA sign absN b prec
  | .RTP => computeSmtLibRoundRTP sign absN b prec
  | .RTN => computeSmtLibRoundRTN sign absN b prec
  | .RTZ => computeSmtLibRoundRTZ sign absN b prec

/-! ## Overflow specials

Mirror `computeRounderSpecialCaseOverflow`. -/

/-- The largest finite dyadic representable in `(e, s)`. -/
private def maxFiniteDyadic (e s : Nat) : Dyadic :=
  Dyadic.ofIntWithPrec ((2 : Int)^(s+1) - 1)
    ((s : Int) - (PackedFloat.bias e : Int))

/--
Mode-aware overflow special case: depending on the rounding mode and
sign, return either infinity or the maximum normal number.
-/
private def specialCaseOverflow (mode : RoundingMode) (sign : Bool)
    (e s : Nat) : EDyadic :=
  match mode with
  | .RNE | .RNA => .infinity sign
  | .RTP =>
    if sign then EDyadic.ofDyadic true (-(maxFiniteDyadic e s))
    else .infinity false
  | .RTN =>
    if sign then .infinity true
    else EDyadic.ofDyadic false (maxFiniteDyadic e s)
  | .RTZ =>
    if sign then EDyadic.ofDyadic true (-(maxFiniteDyadic e s))
    else EDyadic.ofDyadic false (maxFiniteDyadic e s)

/-! ## Public surface: `lower`, `upper`, `round` -/

/--
Wrap a `Dyadic` as an `EDyadic` in target format `(e, s)`, dispatching
to the appropriate overflow special when the rounded magnitude exceeds
`maxFinite`. The `mode` controls the post-rounding overflow special;
`sign` is the sign of the original input (and of the result).
-/
private def wrapResult (mode : RoundingMode) (sign : Bool) (e s : Nat)
    (d : Dyadic) : EDyadic :=
  match d with
  | .zero => .zero sign
  | .ofOdd n' k' h' =>
    let biasI : Int := (PackedFloat.bias e : Int)
    let eVal' : Int := biasI + (n'.natAbs.log2 : Int) - k'
    if eVal' > (2 : Int) ^ e - 2 then specialCaseOverflow mode sign e s
    else .nonzeroFinite (.ofOdd n' k' h') Dyadic.of_ne_zero

/--
The greatest representable `EDyadic` in target format `(e, s)` that is
`≤ x`. This is round-toward-negative-infinity. For `|x| > maxFinite`:
* if `x > 0`, returns `+maxFinite`;
* if `x < 0`, returns `−∞`.
-/
def lower (x : Dyadic) (e s : Nat) : EDyadic :=
  match x with
  | .zero => .zero false
  | .ofOdd n k hn =>
    let xv : Dyadic := .ofOdd n k hn
    let sign : Bool := decide (n < 0)
    let eVal : Int := biasedExp xv e
    let maxEx : Int := (2 : Int) ^ e - 2
    if eVal > maxEx then
      specialCaseOverflow .RTN sign e s
    else
      let prec : Int := targetPrec xv e s
      let shift : Int := k - prec
      if shift ≤ 0 then
        .nonzeroFinite xv Dyadic.of_ne_zero
      else
        wrapResult .RTN sign e s
          (computeLower sign n.natAbs shift.toNat prec)

/--
The least representable `EDyadic` in target format `(e, s)` that is
`≥ x`. This is round-toward-positive-infinity. For `|x| > maxFinite`:
* if `x > 0`, returns `+∞`;
* if `x < 0`, returns `−maxFinite`.
-/
def upper (x : Dyadic) (e s : Nat) : EDyadic :=
  match x with
  | .zero => .zero false
  | .ofOdd n k hn =>
    let xv : Dyadic := .ofOdd n k hn
    let sign : Bool := decide (n < 0)
    let eVal : Int := biasedExp xv e
    let maxEx : Int := (2 : Int) ^ e - 2
    if eVal > maxEx then
      specialCaseOverflow .RTP sign e s
    else
      let prec : Int := targetPrec xv e s
      let shift : Int := k - prec
      if shift ≤ 0 then
        .nonzeroFinite xv Dyadic.of_ne_zero
      else
        wrapResult .RTP sign e s
          (computeUpper sign n.natAbs shift.toNat prec)

/--
Round `x` per IEEE-754 mode `mode` in target format `(e, s)`.

Mirrors `UnpackedFloat.computeSmtLibRound`:
* `±0`, NaN, and ±∞ are propagated (this only handles `Dyadic`, so
  `.zero` and `.ofOdd` are the cases).
* For `|x|` exceeding the format's maxFinite (early overflow), the
  result is the mode-aware overflow special.
* Otherwise we round at the precision dictated by `x`'s exponent
  class, via the per-mode `computeSmtLibRound*` family.
-/
def round (mode : RoundingMode) (x : Dyadic) (e s : Nat) : EDyadic :=
  match x with
  | .zero => .zero false
  | .ofOdd n k hn =>
    let xv : Dyadic := .ofOdd n k hn
    let sign : Bool := decide (n < 0)
    let eVal : Int := biasedExp xv e
    let maxEx : Int := (2 : Int) ^ e - 2
    if eVal > maxEx then
      specialCaseOverflow mode sign e s
    else
      let prec : Int := targetPrec xv e s
      let shift : Int := k - prec
      if shift ≤ 0 then
        .nonzeroFinite xv Dyadic.of_ne_zero
      else
        wrapResult mode sign e s
          (computeSmtLibRoundAux mode sign n.natAbs shift.toNat prec)

end Dyadic

end -- public section

end Veir.Data.FP
