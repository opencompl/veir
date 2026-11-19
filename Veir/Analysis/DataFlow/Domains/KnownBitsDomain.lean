module

public import Veir.Analysis.DataFlow.Domains.AbstractDomain
public import Veir.Interpreter.RuntimeValue
import Veir.Meta.Tactic.BVDecide

public section

namespace Veir

/-!
# Known bits domain

This file defines the abstract value used by known bits analysis. Known bits store
two masks: `zero` marks bits known to be zero and `one` marks bits known to be one.
Bits absent from both masks are unknown, and the masks are disjoint by construction.
The transfer operations follow LLVM's `KnownBits` implementation:
<https://github.com/llvm/llvm-project/blob/main/llvm/include/llvm/Support/KnownBits.h> and
<https://github.com/llvm/llvm-project/blob/main/llvm/lib/Support/KnownBits.cpp>.
-/

/-- Two masks describing the known zero and known one bits of a fixed width integer. -/
structure KnownBits where
  bitwidth : Nat
  zero : BitVec bitwidth
  one : BitVec bitwidth
  /-- No bit can be known to be both zero and one. -/
  disjoint : zero &&& one = 0
deriving DecidableEq, Repr

namespace KnownBits

/-- Construct known bits while conservatively discarding any contradictory mask bits. -/
def ofMasks {bitwidth : Nat} (zero one : BitVec bitwidth) : KnownBits :=
  let consistent := ~~~(zero &&& one)
  { bitwidth
    zero := zero &&& consistent
    one := one &&& consistent
    disjoint := by
      ext i hi
      simp [consistent]
      grind }

/-- No bits are known for an integer of the given width. -/
def unknown (bitwidth : Nat) : KnownBits :=
  ofMasks (bitwidth := bitwidth) 0 0

/-- Every bit of a concrete integer is known. -/
def constant (bitwidth : Nat) (value : Int) : KnownBits :=
  let bits := BitVec.ofInt bitwidth value
  ofMasks (~~~bits) bits

/-- Whether every bit has a known value. -/
def isConstant (bits : KnownBits) : Bool :=
  bits.zero = ~~~bits.one

/-- Render known bits from most to least significant using LLVM's `0`/`1`/`?` notation. -/
def toPattern (bits : KnownBits) : String :=
  String.ofList <| (List.range bits.bitwidth).reverse.map fun i =>
    if bits.zero.getLsbD i then '0'
    else if bits.one.getLsbD i then '1'
    else '?'

instance : ToString KnownBits where
  toString := toPattern

/-- The smallest unsigned value represented by these masks. -/
def unsignedMin (bits : KnownBits) : BitVec bits.bitwidth :=
  bits.one

/-- The largest unsigned value represented by these masks. -/
def unsignedMax (bits : KnownBits) : BitVec bits.bitwidth :=
  ~~~bits.zero

/-- The smallest signed value represented by these masks. -/
def signedMin (bits : KnownBits) : BitVec bits.bitwidth :=
  if bits.bitwidth = 0 || bits.zero.msb then bits.one
  else bits.one ||| BitVec.ofNat bits.bitwidth (2 ^ (bits.bitwidth - 1))

/-- The largest signed value represented by these masks. -/
def signedMax (bits : KnownBits) : BitVec bits.bitwidth :=
  let max := ~~~bits.zero
  if bits.bitwidth = 0 || bits.one.msb then max
  else max &&& ~~~(BitVec.ofNat bits.bitwidth (2 ^ (bits.bitwidth - 1)))

/-- A mask containing the lowest `count` bits. -/
def lowMask (bitwidth count : Nat) : BitVec bitwidth :=
  BitVec.ofNat bitwidth (2 ^ (min count bitwidth) - 1)

/-- A mask containing the highest `count` bits. -/
def highMask (bitwidth count : Nat) : BitVec bitwidth :=
  ~~~lowMask bitwidth (bitwidth - min count bitwidth)

/-- The number of consecutive one bits at the least-significant end. -/
def countTrailingOnes {bitwidth : Nat} (value : BitVec bitwidth) : Nat :=
  (~~~value).ctz.toNat

/-- The number of consecutive one bits at the most-significant end. -/
def countLeadingOnes {bitwidth : Nat} (value : BitVec bitwidth) : Nat :=
  (~~~value).clz.toNat

def countMinTrailingZeros (bits : KnownBits) : Nat := countTrailingOnes bits.zero
def countMaxTrailingZeros (bits : KnownBits) : Nat := bits.one.ctz.toNat
def countMinLeadingZeros (bits : KnownBits) : Nat := countLeadingOnes bits.zero
def countMaxLeadingZeros (bits : KnownBits) : Nat := bits.one.clz.toNat
def countMinLeadingOnes (bits : KnownBits) : Nat := countLeadingOnes bits.one
def countMaxLeadingOnes (bits : KnownBits) : Nat := bits.zero.clz.toNat

/-- Keep only facts true of both possible results. -/
def intersect (lhs rhs : KnownBits) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    some (ofMasks (lhs.zero &&& rhs.zero.cast h.symm) (lhs.one &&& rhs.one.cast h.symm))
  else
    none

/-- Known bits produced by bitwise AND. -/
def bitwiseAnd? (lhs rhs : KnownBits) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhsZero := rhs.zero.cast h.symm
    let rhsOne := rhs.one.cast h.symm
    some (ofMasks (lhs.zero ||| rhsZero) (lhs.one &&& rhsOne))
  else
    none

/-- Known bits produced by bitwise OR. -/
def bitwiseOr? (lhs rhs : KnownBits) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhsZero := rhs.zero.cast h.symm
    let rhsOne := rhs.one.cast h.symm
    some (ofMasks (lhs.zero &&& rhsZero) (lhs.one ||| rhsOne))
  else
    none

/-- Known bits produced by bitwise XOR. -/
def bitwiseXor? (lhs rhs : KnownBits) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhsZero := rhs.zero.cast h.symm
    let rhsOne := rhs.one.cast h.symm
    some (ofMasks
      ((lhs.zero &&& rhsZero) ||| (lhs.one &&& rhsOne))
      ((lhs.zero &&& rhsOne) ||| (lhs.one &&& rhsZero)))
  else
    none

/-- Combine independent facts about the same value, returning unknown on contradiction. -/
def refineWith (lhs rhs : KnownBits) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let zero := lhs.zero ||| rhs.zero.cast h.symm
    let one := lhs.one ||| rhs.one.cast h.symm
    if zero &&& one = 0 then some (ofMasks zero one) else some (unknown lhs.bitwidth)
  else
    none

/-- Known common prefix of every value in the inclusive unsigned interval `[lower, upper]`. -/
def fromUnsignedInterval {bitwidth : Nat}
    (lower upper : BitVec bitwidth) : KnownBits :=
  if upper.ult lower then
    unknown bitwidth
  else
    let differing := lower ^^^ upper
    let unknownBits := bitwidth - differing.clz.toNat
    let known := ~~~lowMask bitwidth unknownBits
    ofMasks (~~~lower &&& known) (lower &&& known)

/-- Retain the low `newWidth` bits, matching LLVM's `KnownBits::trunc`. -/
def trunc (bits : KnownBits) (newWidth : Nat) : KnownBits :=
  ofMasks (bits.zero.setWidth newWidth) (bits.one.setWidth newWidth)

/-- Extend with unknown high bits, matching LLVM's `KnownBits::anyext`. -/
def anyext (bits : KnownBits) (newWidth : Nat) : KnownBits :=
  trunc bits newWidth

/-- Zero-extend known bits, marking every new high bit as zero. -/
def zext (bits : KnownBits) (newWidth : Nat) : KnownBits :=
  let added := newWidth - bits.bitwidth
  ofMasks (bits.zero.setWidth newWidth ||| highMask newWidth added) (bits.one.setWidth newWidth)

/-- Sign-extend known bits. Unknown sign bits produce unknown extension bits. -/
def sext (bits : KnownBits) (newWidth : Nat) : KnownBits :=
  ofMasks (bits.zero.signExtend newWidth) (bits.one.signExtend newWidth)

/-- Extract `width` bits beginning at `lowBit`. -/
def extract (bits : KnownBits) (lowBit width : Nat) : KnownBits :=
  ofMasks (bits.zero.extractLsb' lowBit width) (bits.one.extractLsb' lowBit width)

/-- Concatenate two known-bit values. -/
def concat (high low : KnownBits) : KnownBits :=
  ofMasks (high.zero ++ low.zero) (high.one ++ low.one)

/-- Reverse the order of the bits. -/
def reverse (bits : KnownBits) : KnownBits :=
  ofMasks bits.zero.reverse bits.one.reverse

/-- Compute the base known bits for `lhs + rhs + carry`. -/
def addCarry? (lhs rhs : KnownBits) (carryZero carryOne : Bool) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhsZero := rhs.zero.cast h.symm
    let rhsOne := rhs.one.cast h.symm
    let possibleZero := (~~~lhs.zero) + (~~~rhsZero) + BitVec.ofNat lhs.bitwidth (!carryZero).toNat
    let possibleOne := lhs.one + rhsOne + BitVec.ofNat lhs.bitwidth carryOne.toNat
    let carryKnownZero := ~~~(possibleZero ^^^ lhs.zero ^^^ rhsZero)
    let carryKnownOne := possibleOne ^^^ lhs.one ^^^ rhsOne
    let known := (lhs.zero ||| lhs.one) &&& (rhsZero ||| rhsOne) &&&
      (carryKnownZero ||| carryKnownOne)
    some (ofMasks (~~~possibleZero &&& known) (possibleOne &&& known))
  else
    none

/-- A mask of `count` high bits immediately below the sign bit. -/
private def highBitsBelowSign (bitwidth count : Nat) : BitVec bitwidth :=
  highMask bitwidth (count + 1) &&& ~~~highMask bitwidth 1

/-- LLVM's shared transfer for addition and subtraction with no-wrap flags. -/
private def addSub? (add : Bool) (lhs rhs : KnownBits) (nsw nuw : Bool) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhs := ofMasks (rhs.zero.cast h.symm) (rhs.one.cast h.symm)
    let width := lhs.bitwidth
    if width = 0 then
      some (unknown 0)
    else
      let base :=
        if lhs.zero = 0 && lhs.one = 0 || rhs.zero = 0 && rhs.one = 0 then
          unknown width
        else if add then
          (addCarry? lhs rhs true false).getD (unknown width)
        else
          (addCarry? lhs (ofMasks rhs.one rhs.zero) false true).getD (unknown width)
      let (zero, one) := Id.run do
        let mut zero := base.zero.setWidth width
        let mut one := base.one.setWidth width
        if nuw then
          if add then
            let maximum := 2 ^ width - 1
            let minimum := BitVec.ofNat width
              (min maximum (lhs.unsignedMin.toNat + rhs.unsignedMin.toNat))
            if nsw then
              let count := countLeadingOnes (minimum.setWidth (width - 1))
              one := one ||| highBitsBelowSign width count
            one := one ||| highMask width (countLeadingOnes minimum)
          else
            let maximum := BitVec.ofNat width
              (lhs.unsignedMax.toNat - rhs.unsignedMin.toNat)
            if nsw then
              let count := (maximum.setWidth (width - 1)).clz.toNat
              zero := zero ||| highBitsBelowSign width count
            zero := zero ||| highMask width maximum.clz.toNat
        if nsw then
          let signedLower := -(2 ^ (width - 1) : Int)
          let signedUpper := (2 ^ (width - 1) : Int) - 1
          let rawMinimum := if add then lhs.signedMin.toInt + rhs.signedMin.toInt
            else lhs.signedMin.toInt - rhs.signedMax.toInt
          let rawMaximum := if add then lhs.signedMax.toInt + rhs.signedMax.toInt
            else lhs.signedMax.toInt - rhs.signedMin.toInt
          let minimum := BitVec.ofInt width (max signedLower (min signedUpper rawMinimum))
          let maximum := BitVec.ofInt width (max signedLower (min signedUpper rawMaximum))
          if !minimum.msb then
            let count := countLeadingOnes (minimum.setWidth (width - 1))
            one := one ||| highBitsBelowSign width count
            zero := zero ||| highMask width 1
          if maximum.msb then
            let count := (maximum.setWidth (width - 1)).clz.toNat
            zero := zero ||| highBitsBelowSign width count
            one := one ||| highMask width 1
        return (zero, one)
      if zero &&& one ≠ 0 then some (constant width 0)
      else some (ofMasks zero one)
  else
    none

/-- Known bits for addition, including information supplied by `nsw` and `nuw`. -/
def add? (lhs rhs : KnownBits) (nsw nuw : Bool := false) : Option KnownBits :=
  addSub? true lhs rhs nsw nuw

/-- Known bits for subtraction, including information supplied by `nsw` and `nuw`. -/
def sub? (lhs rhs : KnownBits) (nsw nuw : Bool := false) : Option KnownBits :=
  addSub? false lhs rhs nsw nuw

/-- LLVM-style known bits for multiplication. -/
def mul? (lhs rhs : KnownBits) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhsZero := rhs.zero.cast h.symm
    let rhsOne := rhs.one.cast h.symm
    let width := lhs.bitwidth
    let maxProduct := lhs.unsignedMax.toNat * (~~~rhsZero).toNat
    let leadingZeros := if maxProduct < 2 ^ width
      then (BitVec.ofNat width maxProduct).clz.toNat else 0
    let lhsKnownLow := countTrailingOnes (lhs.zero ||| lhs.one)
    let rhsKnownLow := countTrailingOnes (rhsZero ||| rhsOne)
    let lhsTrailingZeros := countMinTrailingZeros lhs
    let rhsTrailingZeros := countTrailingOnes rhsZero
    let trailingZeros := lhsTrailingZeros + rhsTrailingZeros
    let smallestKnown := min (lhsKnownLow - lhsTrailingZeros)
      (rhsKnownLow - rhsTrailingZeros)
    let resultKnownLow := min (smallestKnown + trailingZeros) width
    let bottomKnown := lhs.one * rhsOne
    let low := lowMask width resultKnownLow
    some (ofMasks (highMask width leadingZeros ||| (~~~bottomKnown &&& low)) (bottomKnown &&& low))
  else
    none

/-- Whether a concrete unsigned value satisfies the known-bit masks. -/
def containsNat (bits : KnownBits) (value : Nat) : Bool :=
  let value := BitVec.ofNat bits.bitwidth value
  value &&& bits.zero = 0 && value &&& bits.one = bits.one

/-- LLVM's upper bound for a possibly out-of-range shift amount. -/
private def maxShiftAmount (rhs : KnownBits) (bitwidth : Nat) : Nat :=
  if bitwidth = 0 then 0
  else if bitwidth &&& (bitwidth - 1) = 0 then
    let extractedWidth := min (Nat.log2 bitwidth) rhs.bitwidth
    rhs.unsignedMax.toNat % (2 ^ extractedWidth)
  else
    min rhs.unsignedMax.toNat (bitwidth - 1)

/-- Intersect the facts produced by LLVM's feasible shift-amount range. -/
private def forEachShiftAmount
    (lhs rhs : KnownBits)
    (minimum maximum : Nat)
    (transfer : Nat → Option KnownBits) : KnownBits := Id.run do
  let mut result : Option KnownBits := none
  for amount in List.range (maximum + 1) do
    if minimum ≤ amount && rhs.containsNat amount then
      if let some shifted := transfer amount then
        result := match result with
          | none => some shifted
          | some current => current.intersect shifted
  -- LLVM uses zero as the non-conflicting representative when every result is poison.
  return result.getD (constant lhs.bitwidth 0)

/-- Known bits for a left shift, including `nsw` and `nuw` constraints. -/
def shl (lhs rhs : KnownBits) (nsw nuw : Bool := false) : KnownBits :=
  let minimum := min rhs.unsignedMin.toNat lhs.bitwidth
  let initialMaximum := maxShiftAmount rhs lhs.bitwidth
  let maximum := Id.run do
    let mut maximum := initialMaximum
    if nuw && nsw then
      let count := lhs.countMaxLeadingZeros
      if count ≠ 0 then maximum := min maximum (count - 1)
    if nuw then maximum := min maximum lhs.countMaxLeadingZeros
    if nsw then
      let count := max lhs.countMaxLeadingZeros lhs.countMaxLeadingOnes
      if count ≠ 0 then maximum := min maximum (count - 1)
    return maximum
  forEachShiftAmount lhs rhs minimum maximum fun amount =>
    let shiftedZero := (lhs.zero <<< amount) ||| lowMask lhs.bitwidth amount
    let shiftedOne := lhs.one <<< amount
    if nsw then
      let shiftedOutZero :=
        nuw && amount ≠ 0 || lhs.zero &&& highMask lhs.bitwidth amount ≠ 0
      let shiftedOutOne := lhs.one &&& highMask lhs.bitwidth amount ≠ 0
      let zero := if shiftedOutZero then shiftedZero ||| highMask lhs.bitwidth 1
        else shiftedZero
      let one := if !shiftedOutZero && shiftedOutOne then
        shiftedOne ||| highMask lhs.bitwidth 1 else shiftedOne
      if zero &&& one ≠ 0 then none else some (ofMasks zero one)
    else
      some (ofMasks shiftedZero shiftedOne)

/-- Known bits for a logical right shift. -/
def lshr (lhs rhs : KnownBits) (exact : Bool := false) : KnownBits :=
  let minimum := min rhs.unsignedMin.toNat lhs.bitwidth
  let maximum := maxShiftAmount rhs lhs.bitwidth
  let maximum := if exact then min maximum lhs.countMaxTrailingZeros else maximum
  forEachShiftAmount lhs rhs minimum maximum fun amount =>
    some <| ofMasks
      ((lhs.zero >>> amount) ||| highMask lhs.bitwidth amount)
      (lhs.one >>> amount)

/-- Known bits for an arithmetic right shift. -/
def ashr (lhs rhs : KnownBits) (exact : Bool := false) : KnownBits :=
  let minimum := min rhs.unsignedMin.toNat lhs.bitwidth
  let maximum := maxShiftAmount rhs lhs.bitwidth
  let maximum := if exact then min maximum lhs.countMaxTrailingZeros else maximum
  forEachShiftAmount lhs rhs minimum maximum fun amount =>
    some <| ofMasks (lhs.zero.sshiftRight amount) (lhs.one.sshiftRight amount)

/-- Add trailing-bit facts implied by an exact division. -/
private def refineExactDivision
    (result lhs rhs : KnownBits) (exact : Bool) : KnownBits :=
  if !exact || lhs.bitwidth = 0 then
    result
  else
    let minimum : Int := lhs.countMinTrailingZeros - rhs.countMaxTrailingZeros
    let maximum : Int := lhs.countMaxTrailingZeros - rhs.countMinTrailingZeros
    if maximum < 0 then
      constant lhs.bitwidth 0
    else
      let (zero, one) := Id.run do
        let mut zero := result.zero.setWidth lhs.bitwidth
        let mut one := result.one.setWidth lhs.bitwidth
        if lhs.one.getLsbD 0 then one := one ||| BitVec.ofNat lhs.bitwidth 1
        if 0 ≤ minimum then
          let trailing := minimum.toNat
          zero := zero ||| lowMask lhs.bitwidth trailing
          if minimum = maximum then
            one := one ||| BitVec.ofNat lhs.bitwidth (2 ^ trailing)
        return (zero, one)
      if zero &&& one ≠ 0 then constant lhs.bitwidth 0 else ofMasks zero one

/-- Known bits for unsigned division, following LLVM's upper-zero-bit estimate. -/
def udiv? (lhs rhs : KnownBits) (exact : Bool := false) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhs := ofMasks (rhs.zero.cast h.symm) (rhs.one.cast h.symm)
    if lhs.isConstant && lhs.one = 0 || rhs.isConstant && rhs.one = 0 then
      some (constant lhs.bitwidth 0)
    else
      let maximumResult := if rhs.unsignedMin = 0 then lhs.unsignedMax
        else lhs.unsignedMax.udiv rhs.unsignedMin
      let result := ofMasks (highMask lhs.bitwidth maximumResult.clz.toNat) 0
      some (refineExactDivision result lhs rhs exact)
  else
    none

/-- Known bits for signed division. The non-negative case has full unsigned precision. -/
def sdiv? (lhs rhs : KnownBits) (exact : Bool := false) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhs := ofMasks (rhs.zero.cast h.symm) (rhs.one.cast h.symm)
    if lhs.isConstant && lhs.one = 0 || rhs.isConstant && rhs.one = 0 then
      some (constant lhs.bitwidth 0)
    else if lhs.zero.msb && rhs.zero.msb then
      udiv? lhs rhs exact
    else
      let estimate : Option (BitVec lhs.bitwidth) :=
        if lhs.one.msb && rhs.one.msb then
          let numerator := lhs.signedMin
          let denominator := rhs.signedMax
          let intMin := BitVec.ofNat lhs.bitwidth (2 ^ (lhs.bitwidth - 1))
          let signedMax := BitVec.ofNat lhs.bitwidth (2 ^ (lhs.bitwidth - 1) - 1)
          if numerator == intMin && denominator == ~~~(0 : BitVec lhs.bitwidth) then
            some signedMax
          else
            some (numerator.sdiv denominator)
        else if lhs.one.msb && rhs.zero.msb &&
            (exact || (-lhs.signedMax).toNat ≥ rhs.signedMax.toNat) then
          let denominator := rhs.signedMin
          some (if denominator = 0 then lhs.signedMin else lhs.signedMin.sdiv denominator)
        else if lhs.zero.msb && lhs.one ≠ 0 && rhs.one.msb &&
            (exact || lhs.signedMin.toNat ≥ (-rhs.signedMin).toNat) then
          some (lhs.signedMax.sdiv rhs.signedMax)
        else
          none
      let result := match estimate with
        | some value =>
            if value.msb then ofMasks 0 (highMask lhs.bitwidth (countLeadingOnes value))
            else ofMasks (highMask lhs.bitwidth value.clz.toNat) 0
        | none => unknown lhs.bitwidth
      some (refineExactDivision result lhs rhs exact)
  else
    none

/-- Preserve low dividend bits when the divisor is known to be even. -/
private def remLowBits (lhs rhs : KnownBits) : KnownBits :=
  if rhs.unsignedMax ≠ 0 && rhs.zero.getLsbD 0 then
    let mask := lowMask lhs.bitwidth rhs.countMinTrailingZeros
    ofMasks (lhs.zero &&& mask) (lhs.one &&& mask)
  else
    unknown lhs.bitwidth

/-- Known bits for unsigned remainder. -/
def urem? (lhs rhs : KnownBits) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhs := ofMasks (rhs.zero.cast h.symm) (rhs.one.cast h.symm)
    let low := remLowBits lhs rhs
    if rhs.isConstant && rhs.one.toNat ≠ 0 && rhs.one.toNat &&& (rhs.one.toNat - 1) = 0 then
      let high := ~~~(BitVec.ofNat lhs.bitwidth (rhs.one.toNat - 1))
      some (ofMasks (low.zero.setWidth lhs.bitwidth ||| high)
        (low.one.setWidth lhs.bitwidth))
    else
      let leaders := max lhs.countMinLeadingZeros rhs.countMinLeadingZeros
      some (ofMasks (low.zero.setWidth lhs.bitwidth ||| highMask lhs.bitwidth leaders)
        (low.one.setWidth lhs.bitwidth))
  else
    none

/-- Known bits for signed remainder, including the exact power-of-two case. -/
def srem? (lhs rhs : KnownBits) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhs := ofMasks (rhs.zero.cast h.symm) (rhs.one.cast h.symm)
    let lowFacts := remLowBits lhs rhs
    if rhs.isConstant && rhs.one.toNat ≠ 0 && rhs.one.toNat &&& (rhs.one.toNat - 1) = 0 then
      let low := BitVec.ofNat lhs.bitwidth (rhs.one.toNat - 1)
      if lhs.zero.msb || low &&& lhs.zero = low then
        some (ofMasks (lowFacts.zero.setWidth lhs.bitwidth ||| ~~~low)
          (lowFacts.one.setWidth lhs.bitwidth))
      else if lhs.one.msb && low &&& lhs.one ≠ 0 then
        some (ofMasks (lowFacts.zero.setWidth lhs.bitwidth)
          (lowFacts.one.setWidth lhs.bitwidth ||| ~~~low))
      else
        some lowFacts
    else
      let rhsSignBits := if rhs.zero.msb then rhs.countMinLeadingZeros
        else if rhs.one.msb then rhs.countMinLeadingOnes else 1
      if lhs.one.msb && lowFacts.one ≠ 0 then
        some (ofMasks (lowFacts.zero.setWidth lhs.bitwidth)
          (lowFacts.one.setWidth lhs.bitwidth ||| highMask lhs.bitwidth
            (max lhs.countMinLeadingOnes rhsSignBits)))
      else if lhs.zero.msb then
        some (ofMasks
          (lowFacts.zero.setWidth lhs.bitwidth ||| highMask lhs.bitwidth
            (max lhs.countMinLeadingZeros rhsSignBits))
          (lowFacts.one.setWidth lhs.bitwidth))
      else
        some lowFacts
  else
    none

/-- Known result of an integer comparison, when it can be decided from the masks. -/
def compare? (predicate : Data.LLVM.IntPred) (lhs rhs : KnownBits) : Option Bool :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhsZero := rhs.zero.cast h.symm
    let rhsOne := rhs.one.cast h.symm
    let rhs := ofMasks rhsZero rhsOne
    match predicate with
    | .eq =>
        if lhs.isConstant && rhs.isConstant then some (lhs.one == rhsOne)
        else if lhs.one &&& rhsZero ≠ 0 || rhsOne &&& lhs.zero ≠ 0 then some false
        else none
    | .ne =>
        if lhs.isConstant && rhs.isConstant then some (lhs.one != rhsOne)
        else if lhs.one &&& rhsZero ≠ 0 || rhsOne &&& lhs.zero ≠ 0 then some true
        else none
    | .ugt =>
        if lhs.unsignedMax.ule rhs.unsignedMin then some false
        else if rhs.unsignedMax.ult lhs.unsignedMin then some true
        else none
    | .uge =>
        if rhs.unsignedMax.ult lhs.unsignedMin then some true
        else if lhs.unsignedMax.ult rhs.unsignedMin then some false
        else none
    | .ult =>
        if rhs.unsignedMax.ule lhs.unsignedMin then some false
        else if lhs.unsignedMax.ult rhs.unsignedMin then some true
        else none
    | .ule =>
        if lhs.unsignedMax.ule rhs.unsignedMin then some true
        else if rhs.unsignedMax.ult lhs.unsignedMin then some false
        else none
    | .sgt =>
        if lhs.signedMax.sle rhs.signedMin then some false
        else if rhs.signedMax.slt lhs.signedMin then some true
        else none
    | .sge =>
        if rhs.signedMax.slt lhs.signedMin then some true
        else if lhs.signedMax.slt rhs.signedMin then some false
        else none
    | .slt =>
        if rhs.signedMax.sle lhs.signedMin then some false
        else if lhs.signedMax.slt rhs.signedMin then some true
        else none
    | .sle =>
        if lhs.signedMax.sle rhs.signedMin then some true
        else if rhs.signedMax.slt lhs.signedMin then some false
        else none
  else
    none

/-- Known bits for a comparison result. -/
def compare (predicate : Data.LLVM.IntPred) (lhs rhs : KnownBits) : KnownBits :=
  match compare? predicate lhs rhs with
  | some value => constant 1 (if value then 1 else 0)
  | none => unknown 1

/-- Known bits for unsigned maximum. -/
private def makeGE (bits : KnownBits) (value : BitVec bits.bitwidth) : KnownBits :=
  let leading := countLeadingOnes (bits.zero ||| value)
  let forcedOnes := value &&& highMask bits.bitwidth leading
  ofMasks bits.zero (bits.one ||| forcedOnes)

private def complementValue (bits : KnownBits) : KnownBits :=
  ofMasks bits.one bits.zero

private def flipSignBit (bits : KnownBits) : KnownBits :=
  let sign := highMask bits.bitwidth 1
  ofMasks
    ((bits.zero &&& ~~~sign) ||| (bits.one &&& sign))
    ((bits.one &&& ~~~sign) ||| (bits.zero &&& sign))

def umax? (lhs rhs : KnownBits) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhs := ofMasks (rhs.zero.cast h.symm) (rhs.one.cast h.symm)
    if rhs.unsignedMax.toNat ≤ lhs.unsignedMin.toNat then some lhs
    else if lhs.unsignedMax.toNat ≤ rhs.unsignedMin.toNat then some rhs
    else (lhs.makeGE rhs.unsignedMin).intersect (rhs.makeGE lhs.unsignedMin)
  else
    none

/-- Known bits for unsigned minimum. -/
def umin? (lhs rhs : KnownBits) : Option KnownBits :=
  if lhs.bitwidth ≠ rhs.bitwidth then none else do
  let maximum ← lhs.complementValue.umax? rhs.complementValue
  return maximum.complementValue

/-- Known bits for signed maximum. -/
def smax? (lhs rhs : KnownBits) : Option KnownBits :=
  if lhs.bitwidth ≠ rhs.bitwidth then none else do
  let maximum ← lhs.flipSignBit.umax? rhs.flipSignBit
  return maximum.flipSignBit

/-- Known bits for signed minimum. -/
def smin? (lhs rhs : KnownBits) : Option KnownBits :=
  if lhs.bitwidth ≠ rhs.bitwidth then none else do
  let minimum ← lhs.flipSignBit.umin? rhs.flipSignBit
  return minimum.flipSignBit

/-- Known bits for population count from the attainable result interval. -/
def ctpop (bits : KnownBits) : KnownBits :=
  let lower := bits.one.cpop.toNat
  let upper := bits.bitwidth - bits.zero.cpop.toNat
  fromUnsignedInterval (BitVec.ofNat bits.bitwidth lower) (BitVec.ofNat bits.bitwidth upper)

/-- Known bits for count-leading-zeros. -/
def ctlz (bits : KnownBits) (zeroIsPoison : Bool := false) : KnownBits :=
  let lower := bits.countMinLeadingZeros
  let upper := if zeroIsPoison && bits.one = 0 then bits.bitwidth - 1
    else bits.countMaxLeadingZeros
  fromUnsignedInterval (BitVec.ofNat bits.bitwidth lower) (BitVec.ofNat bits.bitwidth upper)

/-- Known bits for count-trailing-zeros. -/
def cttz (bits : KnownBits) (zeroIsPoison : Bool := false) : KnownBits :=
  let lower := bits.countMinTrailingZeros
  let upper := if zeroIsPoison && bits.one = 0 then bits.bitwidth - 1
    else bits.countMaxTrailingZeros
  fromUnsignedInterval (BitVec.ofNat bits.bitwidth lower) (BitVec.ofNat bits.bitwidth upper)

/-- High half of an unsigned multiplication. -/
def mulhu? (lhs rhs : KnownBits) : Option KnownBits := do
  if lhs.bitwidth ≠ rhs.bitwidth then none else
  let width := lhs.bitwidth
  let product ← (lhs.zext (2 * width)).mul? (rhs.zext (2 * width))
  return product.extract width width

/-- High half of a signed multiplication. -/
def mulhs? (lhs rhs : KnownBits) : Option KnownBits := do
  if lhs.bitwidth ≠ rhs.bitwidth then none else
  let width := lhs.bitwidth
  let product ← (lhs.sext (2 * width)).mul? (rhs.sext (2 * width))
  return product.extract width width

/-- Unsigned saturating addition. -/
def uaddSat? (lhs rhs : KnownBits) : Option KnownBits :=
  if lhs.bitwidth ≠ rhs.bitwidth then none else
  let limit := 2 ^ lhs.bitwidth - 1
  let lower := min limit (lhs.unsignedMin.toNat + rhs.unsignedMin.toNat)
  let upper := min limit (lhs.unsignedMax.toNat + rhs.unsignedMax.toNat)
  some (fromUnsignedInterval (BitVec.ofNat lhs.bitwidth lower) (BitVec.ofNat lhs.bitwidth upper))

/-- Unsigned saturating subtraction. -/
def usubSat? (lhs rhs : KnownBits) : Option KnownBits :=
  if lhs.bitwidth ≠ rhs.bitwidth then none else
  let lower := lhs.unsignedMin.toNat - rhs.unsignedMax.toNat
  let upper := lhs.unsignedMax.toNat - rhs.unsignedMin.toNat
  some (fromUnsignedInterval (BitVec.ofNat lhs.bitwidth lower) (BitVec.ofNat lhs.bitwidth upper))

private def fromSignedInterval (bitwidth : Nat) (lower upper : Int) : KnownBits :=
  let lower := BitVec.ofInt bitwidth lower
  let upper := BitVec.ofInt bitwidth upper
  if lower.msb = upper.msb then fromUnsignedInterval lower upper else unknown bitwidth

/-- Signed saturating addition. -/
def saddSat? (lhs rhs : KnownBits) : Option KnownBits :=
  if lhs.bitwidth ≠ rhs.bitwidth then none else
  if lhs.bitwidth = 0 then some (unknown 0) else
  let lowerLimit := -(2 ^ (lhs.bitwidth - 1) : Int)
  let upperLimit := (2 ^ (lhs.bitwidth - 1) : Int) - 1
  let lower := max lowerLimit (lhs.signedMin.toInt + rhs.signedMin.toInt)
  let upper := min upperLimit (lhs.signedMax.toInt + rhs.signedMax.toInt)
  some (fromSignedInterval lhs.bitwidth lower upper)

/-- Signed saturating subtraction. -/
def ssubSat? (lhs rhs : KnownBits) : Option KnownBits :=
  if lhs.bitwidth ≠ rhs.bitwidth then none else
  if lhs.bitwidth = 0 then some (unknown 0) else
  let lowerLimit := -(2 ^ (lhs.bitwidth - 1) : Int)
  let upperLimit := (2 ^ (lhs.bitwidth - 1) : Int) - 1
  let lower := max lowerLimit (lhs.signedMin.toInt - rhs.signedMax.toInt)
  let upper := min upperLimit (lhs.signedMax.toInt - rhs.signedMin.toInt)
  some (fromSignedInterval lhs.bitwidth lower upper)

/-- Absolute value, preserving LLVM's useful sign and trailing-zero facts. -/
def abs (bits : KnownBits) (intMinIsPoison : Bool := false) : KnownBits :=
  if bits.bitwidth = 0 || bits.zero.msb then
    bits
  else if bits.one.msb then
    (constant bits.bitwidth 0).sub? bits intMinIsPoison false |>.getD (unknown bits.bitwidth)
  else
    let minTrailing := bits.countMinTrailingZeros
    let maxTrailing := bits.countMaxTrailingZeros
    let sign := highMask bits.bitwidth 1
    let signZero := if intMinIsPoison || bits.one ≠ 0 && bits.one ≠ sign then sign else 0
    let lowestOne := if minTrailing = maxTrailing && minTrailing < bits.bitwidth
      then BitVec.ofNat bits.bitwidth (2 ^ minTrailing) else 0
    ofMasks (lowMask bits.bitwidth minTrailing ||| signZero) lowestOne

private def byteSwapMask {bitwidth : Nat} (value : BitVec bitwidth) : BitVec bitwidth :=
  if bitwidth % 8 ≠ 0 then value else
  let bytes := bitwidth / 8
  let swapped := (List.range bitwidth).foldl (init := 0) fun result source =>
    if value.getLsbD source then
      let target := (bytes - 1 - source / 8) * 8 + source % 8
      result ||| 2 ^ target
    else
      result
  BitVec.ofNat bitwidth swapped

/-- Reverse the byte order when the bitwidth is byte-aligned. -/
def byteSwap (bits : KnownBits) : KnownBits :=
  ofMasks (byteSwapMask bits.zero) (byteSwapMask bits.one)

/-- Repeat an input bit pattern to a requested result width. -/
def replicate (bits : KnownBits) (resultWidth : Nat) : KnownBits :=
  if bits.bitwidth = 0 || resultWidth % bits.bitwidth ≠ 0 then
    unknown resultWidth
  else
    let repetitions := resultWidth / bits.bitwidth
    let repeatMask (value : BitVec bits.bitwidth) :=
      let repeated := (List.range repetitions).foldl (init := 0) fun result index =>
        result ||| value.toNat <<< (index * bits.bitwidth)
      BitVec.ofNat resultWidth repeated
    ofMasks (repeatMask bits.zero) (repeatMask bits.one)

/-- Known bits for a funnel shift left by a concrete amount. -/
def fshl? (lhs rhs : KnownBits) (amount : Nat) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    if lhs.bitwidth = 0 then some (unknown 0) else
    let rhsZero := rhs.zero.cast h.symm
    let rhsOne := rhs.one.cast h.symm
    let amount := amount % lhs.bitwidth
    if amount = 0 then some lhs else
    some (ofMasks
      ((lhs.zero <<< amount) ||| (rhsZero >>> (lhs.bitwidth - amount)))
      ((lhs.one <<< amount) ||| (rhsOne >>> (lhs.bitwidth - amount))))
  else
    none

/-- Known bits for a funnel shift right by a concrete amount. -/
def fshr? (lhs rhs : KnownBits) (amount : Nat) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    if lhs.bitwidth = 0 then some (unknown 0) else
    let rhsZero := rhs.zero.cast h.symm
    let rhsOne := rhs.one.cast h.symm
    let amount := amount % lhs.bitwidth
    if amount = 0 then some (ofMasks rhsZero rhsOne) else
    some (ofMasks
      ((rhsZero >>> amount) ||| (lhs.zero <<< (lhs.bitwidth - amount)))
      ((rhsOne >>> amount) ||| (lhs.one <<< (lhs.bitwidth - amount))))
  else
    none

/-- Keep only facts known on both incoming control flow paths. -/
def join? (lhs rhs : KnownBits) : Option KnownBits :=
  lhs.intersect rhs

end KnownBits

/--
Sparse lattice for known bits. `bottom` is an uninitialized sparse value and `known`
contains width aware masks. A `known` value with two zero masks is the unique representation
of an integer for which no bits are known.
-/
inductive KnownBitsLattice where
  | bottom
  | known (bits : KnownBits)
deriving DecidableEq, Repr

namespace KnownBitsLattice

instance : Bot KnownBitsLattice where
  bot := .bottom

/-- No bit facts are known, but the integer width is known. -/
def unknown (bitwidth : Nat) : KnownBitsLattice :=
  .known (KnownBits.unknown bitwidth)

/-- An exact fixed width integer value. -/
def constant (bitwidth : Nat) (value : Int) : KnownBitsLattice :=
  .known (KnownBits.constant bitwidth value)

instance : ToString KnownBitsLattice where
  toString
    | .bottom => "bottom"
    | .known bits => bits.toPattern

/-- The concrete runtime values represented by a known bits lattice element. -/
@[expose] def γ : KnownBitsLattice → Set RuntimeValue
  | .bottom => ⊥
  | .known bits => fun concrete =>
      match concrete with
      | .int bitwidth (.val value) =>
        ∃ h : bitwidth = bits.bitwidth,
          let value := value.cast h
          value &&& bits.zero = 0 ∧ value &&& bits.one = bits.one
      | _ => False

@[simp] theorem not_mem_γ_bottom (value : RuntimeValue) : value ∉ γ .bottom := fun h => h.elim

/-- Normalize membership in a known-bits value to masks at the concrete value's width. -/
theorem mem_γ_known_masks_iff
    {bits : KnownBits}
    {bitwidth : Nat}
    {value : BitVec bitwidth} :
    RuntimeValue.int bitwidth (.val value) ∈ γ (.known bits) ↔
      ∃ (zero one : BitVec bitwidth) (disjoint : zero &&& one = 0),
        bits = ⟨bitwidth, zero, one, disjoint⟩ ∧
        value &&& zero = 0 ∧ value &&& one = one := by
  constructor
  · rcases bits with ⟨bitsWidth, zero, one, disjoint⟩
    rintro ⟨hwidth, hzero, hone⟩
    change bitwidth = bitsWidth at hwidth
    subst bitsWidth
    simp at hzero hone
    exact ⟨zero, one, disjoint, rfl, hzero, hone⟩
  · rintro ⟨zero, one, disjoint, rfl, hzero, hone⟩
    exact ⟨rfl, hzero, hone⟩

/-- Characterize known-bits membership as facts about each concrete bit. -/
theorem mem_γ_known_iff
    {bits : KnownBits}
    {bitwidth : Nat}
    {value : BitVec bitwidth} :
    RuntimeValue.int bitwidth (.val value) ∈ γ (.known bits) ↔
      ∃ (zero one : BitVec bitwidth) (disjoint : zero &&& one = 0),
        bits = ⟨bitwidth, zero, one, disjoint⟩ ∧
        (∀ i (hi : i < bitwidth), zero[i] = true → value[i] = false) ∧
        (∀ i (hi : i < bitwidth), one[i] = true → value[i] = true) := by
  rw [mem_γ_known_masks_iff]
  constructor
  · rintro ⟨zero, one, disjoint, hbits, hzero, hone⟩
    refine ⟨zero, one, disjoint, hbits, ?_, ?_⟩
    · intro i hi hzeroTrue
      have hzeroBit := congrArg (fun value => value[i]) hzero
      simp at hzeroBit
      veir_bv_decide
    · intro i hi honeTrue
      have honeBit := congrArg (fun value => value[i]) hone
      simp at honeBit
      veir_bv_decide
  · rintro ⟨zero, one, disjoint, hbits, hzero, hone⟩
    refine ⟨zero, one, disjoint, hbits, ?_, ?_⟩
    · ext i hi
      have hzeroBit := hzero i hi
      simp at hzeroBit ⊢
      veir_bv_decide
    · ext i hi
      have honeBit := hone i hi
      simp at honeBit ⊢
      veir_bv_decide

/-- Join facts arriving along different control flow paths. -/
def join : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice
  | .bottom, rhs => rhs
  | lhs, .bottom => lhs
  | .known lhs, .known rhs =>
      match lhs.join? rhs with
      | some bits => .known bits
      | none => .unknown lhs.bitwidth

instance : Join KnownBitsLattice where
  join := join

end KnownBitsLattice

end Veir
