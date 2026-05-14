import Fp.Basic
import Fp.Rounding
import Fp.MulInv
import Fp.Grind
import Fp.Utils.Rat
import Fp.Rounding

/-# Notation

eu: exponent unpacked
su : significand unpacked (includes hidden bit into the count, so su = 3, then number is `[x.xx]`)
ep : exponent packed
sp : significand packed (does not include hidden bit into the count, so sp = 2, then number is `x.[xx]`)

-/

@[bv_normalize]
def roundingDecision (mode : RoundingMode) (sign : Bool) (significandEven : Bool)
  (guardBit : Bool) (stickyBit : Bool) (_exact : Bool) : Bool :=
  match mode with
  | RoundingMode.RNE =>
      (guardBit && (stickyBit || !significandEven))
  | RoundingMode.RNA =>
      guardBit
  | RoundingMode.RTP =>
      (!sign && (guardBit || stickyBit))
  | RoundingMode.RTN =>
      (sign && (guardBit || stickyBit))
  | RoundingMode.RTZ =>
      false

/--
Return 'x - base', but if 'x' is less than 'base', return zero instead of a negative number.
-/
@[bv_normalize]
def BitVec.subSaturatingZero (x : BitVec w) (base : BitVec w) : BitVec w :=
  if x.slt base then 0 else x - base

/-
BitVec.toNat_sub causes agressive unfolding when I don't want it to,
so I remove it from the simp-set.
-/
attribute [-simp] BitVec.toNat_sub

/--
The 'subSaturatingZero', when interpreted as an signed numbers,
correctly keeps track of the distance from 'base' when 'x' is greater than or equal to 'base',
and returns zero when 'x' is less than 'base'.
-/
theorem BitVec.toInt_subSaturatingZero_eq_ite {w : Nat} (hw : 0 < w) (x base : BitVec w)
    (hle : - 2 ^ (w - 1) ≤ x.toInt - base.toInt)
    (hlt : x.toInt - base.toInt < 2 ^ (w - 1)) :
    (BitVec.subSaturatingZero x base).toInt =
      if x.toInt < base.toInt then 0 else x.toInt - base.toInt := by
  simp [subSaturatingZero]
  by_cases h : x.slt base
  · simp [h]
    rw [BitVec.slt_eq_decide] at h
    simp at h
    grind only
  · simp only [h]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [BitVec.slt_eq_decide] at h
    simp only [decide_eq_true_eq, Int.not_lt] at h
    simp only [show ¬x.toInt < base.toInt by grind, ↓reduceIte]
    rw [BitVec.toInt_sub]
    apply Int.bmod_eq_of_le
    · simp only [Int.natCast_pow, Int.cast_ofNat_Int, hw, Int.two_pow_div_two_eq_sub_one_of_pos]
      grind only
    · simp; grind only

/--
The output of 'subSaturatingZero' is always nonnegative.
-/
theorem BitVec.nonneg_toInt_subSaturatingZero {w : Nat} (hw : 0 < w) (x base : BitVec w)
    (hle : - 2 ^ (w - 1) ≤ x.toInt - base.toInt)
    (hlt : x.toInt - base.toInt < 2 ^ (w - 1)) :
    0 ≤ (BitVec.subSaturatingZero x base).toInt := by
  rw [BitVec.toInt_subSaturatingZero_eq_ite hw x base hle hlt]
  split <;> grind only

/--
If the integer interpretation is nonnegative, then the 'toInt' value equals to 'toNat' value.
-/
theorem BitVec.toInt_eq_toNat_of_toInt_nonneg {w : Nat}
    (x : BitVec w) (hle : 0 ≤ x.toInt) :
    x.toInt = x.toNat := by
  rw [BitVec.toInt_eq_toNat_of_msb]
  rw [BitVec.msb_eq_toInt]
  grind only

/--
The value of 'subSaturatingZero' when interpreted as a natural
number and then casted to an integer equals saturating subtraction.
-/
theorem BitVec.natCast_toNat_subSaturatingZero_eq_ite
   (hw : 0 < w) (x base : BitVec w)
    (hle : - 2 ^ (w - 1) ≤ x.toInt - base.toInt)
    (hlt : x.toInt - base.toInt < 2 ^ (w - 1)) :
    (BitVec.subSaturatingZero x base).toNat =
      if x.toInt < base.toInt then 0 else (x.toInt - base.toInt) := by
  rw [← BitVec.toInt_eq_toNat_of_toInt_nonneg (x.subSaturatingZero base)]
  · rw [BitVec.toInt_subSaturatingZero_eq_ite hw x base hle hlt]
  · apply BitVec.nonneg_toInt_subSaturatingZero hw x base hle hlt

/--
The value of 'subSaturatingZero' when interpreted as a natural
number equals  saturating subtraction.
-/
theorem BitVec.toNat_subSaturatingZero_eq_ite_toNat
   (hw : 0 < w) (x base : BitVec w)
    (hle : - 2 ^ (w - 1) ≤ x.toInt - base.toInt)
    (hlt : x.toInt - base.toInt < 2 ^ (w - 1)) :
    (BitVec.subSaturatingZero x base).toNat =
      if x.toInt < base.toInt then 0 else (x.toInt - base.toInt).toNat := by
  have := BitVec.natCast_toNat_subSaturatingZero_eq_ite hw x base hle hlt
  split <;> grind only



/--
Compute the guard bit index (from LSB) adjusted for subnormal shifting.
This is the position in the significand where the guard bit falls when
rounding to `tsp` precision with the given target exponent format.

TODO: can't we do this with 'lsbBitIndex'? Possibly!
-/
@[bv_normalize]
def UnpackedFloat.guardBitIndex {eu su : Nat}
  (uf : UnpackedFloat eu su)
  (tep tsp : Nat) : BitVec su :=
  let guardBitIndexFromLsb : BitVec su :=
    BitVec.ofNat su ((su - 1) - (tsp + 1))
  let targetMinNormalExp : BitVec eu :=
    BitVec.ofInt eu (minNormalExp tep)
  let shiftAmtPositive := BitVec.subSaturatingZero  targetMinNormalExp uf.ex
  guardBitIndexFromLsb + shiftAmtPositive.zeroExtend su

/-- Extract the guard bit from an unpacked float at the target precision. -/
@[bv_normalize]
def UnpackedFloat.blastExtractGuardBit {eu su : Nat}
  (uf : UnpackedFloat eu su)
  (tep tsp : Nat) : Bool :=
  let idx := uf.guardBitIndex tep tsp
  (uf.sig &&& BitVec.oneHotBV idx) ≠ 0#su

/-- Extract the sticky bit from an unpacked float: whether any bit below the guard bit is set. -/
@[bv_normalize]
def UnpackedFloat.blastExtractStickyBit {eu su : Nat}
  (uf : UnpackedFloat eu su)
  (tep tsp : Nat) : Bool :=
  let idx := uf.guardBitIndex tep tsp
  (uf.sig &&& BitVec.orderEncode idx) ≠ 0#su

/-- Check whether the unpacked float's significand LSB (relative to the target precision) is even. -/
@[bv_normalize]
def UnpackedFloat.blastExtractIsEven {eu su : Nat}
  (uf : UnpackedFloat eu su)
  (tep tsp : Nat) : Bool :=
  let idx := uf.guardBitIndex tep tsp
  uf.sig &&& BitVec.oneHotBV (idx + 1#su) = 0#su

/--
Handle the overflow special case: depending on the rounding mode and sign,
return either infinity or the maximum normal number.
- RNE/RNA: always return infinity.
- RTP: return infinity for positive, max normal for negative.
- RTN: return infinity for negative, max normal for positive.
- RTZ: always return max normal.
-/
@[bv_normalize]
def blastRounderSpecialCaseOverflow
  {tep tsp : Nat}
  (roundingMode : RoundingMode)
  (sign : Bool) :
  EUnpackedFloat (exponentWidth tep tsp) (tsp + 1) :=
  let returnInf : Bool :=
    match roundingMode with
    | RoundingMode.RNE => true
    | RoundingMode.RNA => true
    | RoundingMode.RTP => !sign
    | RoundingMode.RTN => sign
    | _ => false
  if returnInf then
    EUnpackedFloat.mkInfinity sign
  else
    EUnpackedFloat.mkNumber <| UnpackedFloat.maxNormal _ _ tep tsp sign

/--
Handle the underflow special case: depending on the rounding mode and sign,
return either zero or the minimum subnormal number.
- RNE/RNA/RTZ: always return zero.
- RTP: return zero for negative, min subnormal for positive.
- RTN: return zero for positive, min subnormal for negative.
-/
@[bv_normalize]
def blastRounderSpecialCaseUnderflow
  {tep tsp : Nat}
  (roundingMode : RoundingMode)
  (sign : Bool) :
  EUnpackedFloat (exponentWidth tep tsp) (tsp + 1) :=
  let returnZero : Bool :=
    match roundingMode with
    | RoundingMode.RNE => true
    | RoundingMode.RNA => true
    | RoundingMode.RTZ => true
    | RoundingMode.RTP => sign
    | RoundingMode.RTN => !sign
  if returnZero then
    EUnpackedFloat.mkZero sign
  else
    EUnpackedFloat.mkNumber <| .minSubnormalForPackedFloat _ _ tep tsp sign

/--
Truncate the exponent of an `UnpackedFloat` to the target format width,
producing an `EUnpackedFloat`.

Precondition: the exponent value must fit in the target width, i.e.,
`minSubnormalExp tep tsp ≤ uf.ex.toInt`
and `uf.ex.toInt ≤ maxNormalExp tep`.
This is guaranteed when the caller has already ruled out overflow and underflow.
-/
@[bv_normalize]
def UnpackedFloat.truncateFittingExponent {eu su : Nat} (tep tsp : Nat)
  (uf : UnpackedFloat eu su) :
  UnpackedFloat (exponentWidth tep tsp) su :=
  { sign := uf.sign,
    ex := uf.ex.signExtend (exponentWidth tep tsp),
    sig := uf.sig }

axiom AxRoundPreconditions {P : Prop} : P

def mkPackedFloats (E : Nat) (S : Nat) : Array (PackedFloat E S) := Id.run do
  let mut res := #[]
  for expVal in [0:Nat.pow 2 E] do
    for sigVal in [0:Nat.pow 2 S] do
      for sign in [true, false] do
        let pf : PackedFloat E S :=
          { sign := sign,
            ex := BitVec.ofNat E expVal,
            sig := BitVec.ofNat S sigVal }
        res := res.push pf
  res

/--
Return all representable packed floats of given exponent and significand widths,
in ascending order by their rational value.
-/
def mkPackedFloatNumsSorted (E : Nat) (S : Nat) :
    Array (PackedFloat E S × Rat) := Id.run do
  let pfs ← mkPackedFloats E S
  let mut res := #[]
  for pf in pfs do
    if let .some r := pf.toRat? then
      res := res.push (pf, r)
  res.qsort (fun a b => a.2 < b.2)

/-
Implementation of RNE rounding by finding the closest representable float, exhaustively.
Note that zero needs special handling, because toRat does not distinguish +0 and -0,
but FP does.
-/
def getClosestRNEResult {eu su : Nat}
    (tep tsp : Nat)
    (inUf : UnpackedFloat eu su) :
    EUnpackedFloat (exponentWidth tep tsp) (tsp + 1) := Id.run do
  let inRat := inUf.toRat
  let candidates := mkPackedFloatNumsSorted tep tsp
  if inRat < (candidates.getD 0 default).2 then
    EUnpackedFloat.mkInfinity true
  else if inRat > (candidates.getD (candidates.size - 1) default).2 then
    EUnpackedFloat.mkInfinity false
  else
    let candidatesWithDist := candidates.map (fun (pf, r) =>
      (pf, r, (inRat - r).abs))
    let candidatesSorted := candidatesWithDist.qsort (fun a b => a.2.2 < b.2.2)
    let out1 := candidatesSorted.getD 0 default
    let out2 := candidatesSorted.getD 1 default
    let (pf1, r1, dist1) := out1
    let (pf2, _r2, dist2) := out2
    if r1 = 0 then
      EUnpackedFloat.mkZero inUf.sign
    else
      if hlt : dist1 < dist2 then
        pf1.unpack
      else if hgt : dist2 < dist1 then
        pf2.unpack
      else
        have : dist1 = dist2 := by grind
          -- round to the nearest even number
          if r1.num % 2 == 0 then
            pf1.unpack
          else
            pf2.unpack
          -- round to nearest even.

def BitVec.toBitsStr {w : Nat} (bv : BitVec w) : String := Id.run do
  let mut s := "0b"
  for i in [0:w] do
    let bit := if bv.getMsbD i then "1" else "0"
    s := s.append bit
  s

@[bv_normalize]
def BitVec.isZero {w : Nat} (bv : BitVec w) : Bool :=
  bv = BitVec.ofNat w 0

/-- conditionally increment, and return flag of whether overflow was observed -/
@[bv_normalize]
def conditionalIncrementWithFlags (cond : Bool) (x : BitVec w) : BitVec w × Bool :=
  if cond then
    let x' := x.zeroExtend (w + 1) + 1#(w + 1)
    (x'.setWidth w, x'.msb)
  else
    (x, false)

def BitVec.smin (a b : BitVec w) : BitVec w :=
  if a.slt b then a else b

def BitVec.smax (a b : BitVec w) : BitVec w :=
  -- a > b then a else b
  -- b < a
  if b.slt a then a else b


/-- A variant of 'getLsbD' where the index is also a bitvector. -/
@[bv_normalize]
def BitVec.getLsbDBV {w : Nat} (x : BitVec w) (i : BitVec w) : Bool :=
  x &&& (1#w <<< i) ≠ 0#w

example (x y : BitVec 5) (hy : y < 3#5) : (x <<< 3#5).getLsbDBV y = false := by
  bv_decide

@[simp]
theorem BitVec.getLsbDBV_eq_getLsbD {w : Nat} (x : BitVec w) (i : BitVec w) :
    x.getLsbDBV i = x.getLsbD (i.toNat) := by
  rw [getLsbDBV]
  simp
  by_cases hx : x &&& (1#w <<< i.toNat) = 0#w
  · rw [hx]
    simp
    have : (x &&& (1#w <<< i.toNat)).getLsbD i.toNat = false := by
      grind
    grind
  · simp [hx]
    simp at hx
    have : (x &&& (1#w <<< i.toNat)).getLsbD i.toNat = true := by
      simp
      grind
    grind

def BitVec.getMsbDBV {w : Nat} (x : BitVec w) (i : BitVec w) : Bool :=
  x.getLsbDBV ((BitVec.ofNat w (w - 1)) - i)

@[simp]
theorem BitVec.getMsbDBV_eq_getMsbD {w : Nat} (x : BitVec w) (i : BitVec w)
    (hi : i.toNat < w) :
    x.getMsbDBV i = x.getMsbD (i.toNat) := by
  have : w - 1 < 2^w := by
    have : w < 2^w := by exact Nat.lt_two_pow_self
    grind
  rw [getMsbDBV, getLsbDBV_eq_getLsbD]
  rw [BitVec.toNat_sub_of_le]
  · simp
    rw [Nat.mod_eq_of_lt (by omega)]
    simp [BitVec.getMsbD]
    omega
  · rw [BitVec.le_def]
    simp only [toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/--
Extract the bits from LSB from low index `0` to high index `start` (excluded), setting other bits to zero.
-/
def BitVec.extractLsbTo0BV {w : Nat} (x : BitVec w) (start : BitVec w) : BitVec w :=
  x &&& (orderEncode start)

@[simp]
theorem BitVec.getLsbD_extractLsbTo0BV_eq_decide {w : Nat} (x : BitVec w) (start : BitVec w) (i : Nat) :
    (x.extractLsbTo0BV start).getLsbD i = (x.getLsbD i &&  decide (i < start.toNat)) := by
  rw [extractLsbTo0BV]
  rw [BitVec.getLsbD_and]
  rw [BitVec.getLsbD_orderEncode]
  by_cases hi : i < w
  · by_cases hstart : start.toNat < w
    · have : start.toNat < 2^w := by
        have : w < 2^w := by exact Nat.lt_two_pow_self
        omega
      simp [hi]
    · simp [hi]
  · simp [hi]
    intros hx
    have := BitVec.lt_of_getLsbD hx
    omega


/--
Extract out bits from 'startMsb' (excluded) down to low index `0`, setting other bits to zero.
-/
def BitVec.maskMsbTo0BV {w : Nat} (x : BitVec w) (startMsb : BitVec w) : BitVec w :=
  BitVec.extractLsbTo0BV x (BitVec.ofNat w w  - startMsb)

/--
observe that the bounds are sane.
if startMsb = 0, then we extract the full vector, and the decide is just (i < w).
if startMsb = 1, then we extract all but the MSB, and the decide is (i < w - 1).
if startMsb = w, then we extract nothing, and the decide is (i < 0) which is always false.
-/
@[simp]
theorem BitVec.getMsbD_extractMsbTo0BV_eq_decide {w : Nat}
    (x : BitVec w)
    (startMsb : BitVec w)
    (i : Nat)
    (hstart : startMsb.toNat ≤ w) :
    (x.maskMsbTo0BV startMsb).getLsbD i =
      (x.getLsbD i &&  decide (i < (w - startMsb.toNat))) := by
  rw [maskMsbTo0BV]
  rw [BitVec.getLsbD_extractLsbTo0BV_eq_decide]
  by_cases hx : x.getLsbD i
  · simp only [hx, Bool.true_and, decide_eq_decide]
    rw [BitVec.toNat_sub_of_le]
    · simp
    · rw [BitVec.le_def]
      simp
      omega
  · simp [hx]


/-- a > b -/
@[bv_normalize]
private def BitVec.sgt {w : Nat} (a b : BitVec w) : Bool :=
  b.slt a

def UnpackedFloat.reprBinary {eu su : Nat} (uf : UnpackedFloat eu su) : String :=
  let signStr := if uf.sign then "-" else "+"
  let exStr := s!"{uf.ex.toBitsStr}=int:{uf.ex.toInt}"
  let sigStr := s!"{uf.sig.toBitsStr}=nat:{uf.sig.toNat}"
  s!"{signStr} {sigStr} * 2^({exStr} - {su - 1})"

def PackedFloat.reprBinary {ep sp : Nat} (pf : PackedFloat ep sp) : String :=
  let signStr := if pf.sign then "-" else "+"
  let exStr := s!"{pf.ex.toBitsStr}=nat:{pf.ex.toInt}"
  let sigStr := s!"{pf.sig.toBitsStr}=nat:{pf.sig.toNat}"
  s!"{signStr} (subnorm:{pf.isNonzeroSubnorm}) sig:{sigStr} ex:{exStr} bias:{bias ep} expval:{pf.ex.toInt - bias ep} = {pf.toRat?}"

def EUnpackedFloat.reprBinary {eu su : Nat} (euf : EUnpackedFloat eu su) : String :=
  if euf.state = .Infinity then
    let signStr := if euf.sign then "-" else "+"
    s!"{signStr} EUInfinity"
  else if euf.state = .NaN then
    "EUENaN"
  else
    s!"EUNum({euf.num.reprBinary})"

/--
Clear guard and sticky bits from the significand of an unpacked float,
zeroing out all bits at and below the guard bit position.
The guard bit index is computed from the target exponent and significand widths.
-/
@[bv_normalize]
def UnpackedFloat.blastClearSignificand {eu su : Nat}
  (uf : UnpackedFloat eu su)
  (tep tsp : Nat) :
  UnpackedFloat eu su :=
  let guardBitIdx := uf.guardBitIndex tep tsp
  let guardBitMask : BitVec su := BitVec.oneHotBV guardBitIdx
  let stickyBitsMask : BitVec su := BitVec.orderEncode guardBitIdx
  { sign := uf.sign,
    ex := uf.ex,
    sig := uf.sig &&& (~~~(guardBitMask ||| stickyBitsMask)) }

/--
Round an unpacked float toward zero: clear guard/sticky bits, sign-extend the exponent,
and extract the top `tsp + 1` bits of the significand.
This corresponds to `lower` for nonnegative values and `upper` for negative values
in the rounding theory.

Returns an `UnpackedFloat` with exponent width `eu + 1` (sign-extended, no overflow
possible since no increment occurs) and significand width `tsp + 1`.
-/
@[bv_normalize]
def UnpackedFloat.blastRoundTowardZero {eu su : Nat}
  (uf : UnpackedFloat eu su)
  (tep tsp : Nat) :
  UnpackedFloat (eu) (tsp + 1) :=
  let ufCleared := uf.blastClearSignificand tep tsp
  { sign := ufCleared.sign,
    ex := ufCleared.ex,
    sig := ufCleared.sig.extractMsb' 0 (tsp + 1) }

/--
Increment an unpacked float by the least significant bit of the target precision
(successor away from zero): clear guard/sticky bits, then add the lsb mask to the significand.
This corresponds to `upper` for nonnegative values and `lower` for negative values
in the rounding theory.

Returns an `UnpackedFloat` with exponent width `eu + 1` (to accommodate potential
carry from significand overflow) and significand width `tsp + 1`.
-/
@[bv_normalize]
def UnpackedFloat.blastSuccessorAwayFromZero {eu su : Nat}
  (uf : UnpackedFloat eu su)
  (tep tsp : Nat) :
  UnpackedFloat (eu) (tsp + 1) :=
  let guardBitIdx := uf.guardBitIndex tep tsp
  let guardBitMask : BitVec su := BitVec.oneHotBV guardBitIdx
  let ufCleared := uf.blastClearSignificand tep tsp
  let lsbMask : BitVec (su + 1) := guardBitMask.zeroExtend (su + 1) <<< 1

  let sigDidOverflow_RoundedTargetSigWithHidden : BitVec (su + 1) :=
    ufCleared.sig.zeroExtend (su + 1) + lsbMask

  let sigDidOverflow : Bool :=
    sigDidOverflow_RoundedTargetSigWithHidden.msb

  let roundedTargetSigWithHidden : BitVec su :=
    sigDidOverflow_RoundedTargetSigWithHidden.setWidth su

  let roundedTargetSigWithHiddenOverflowAdjusted : BitVec su :=
    if sigDidOverflow then
      BitVec.leadingOne su
    else
      roundedTargetSigWithHidden

  let roundedExpExtended : BitVec (eu) :=
    if sigDidOverflow then
      ufCleared.ex + 1#eu
    else
      ufCleared.ex

  let out :=
    { sign := ufCleared.sign,
      ex := roundedExpExtended,
      sig := roundedTargetSigWithHiddenOverflowAdjusted.extractMsb' 0 (tsp + 1) }

  out

/--
Handle overflow and underflow for a rounded result, producing the final `EUnpackedFloat`.
Checks whether the rounded exponent exceeds target bounds (late overflow/underflow),
clamps the exponent, and returns the appropriate special case (underflow, overflow)
or the normal rounded number.
-/
@[bv_normalize]
def symfpuRounderHandleOverAndUnderflow {eu : Nat} {tep tsp : Nat}
  (roundedResult : UnpackedFloat eu (tsp + 1))
  (mode : RoundingMode) :
  EUnpackedFloat (exponentWidth tep tsp) (tsp + 1) :=
  let maxNormalExpBV : BitVec eu :=
    BitVec.ofInt eu (maxNormalExp tep)
  let lateOverflow : Bool := maxNormalExpBV.slt roundedResult.ex
  let minSubnormalExpBV : BitVec eu :=
    BitVec.ofInt eu (minSubnormalExp tep tsp)
  let lateUnderflow : Bool :=
    roundedResult.ex.slt minSubnormalExpBV

  if lateUnderflow then
    blastRounderSpecialCaseUnderflow mode roundedResult.sign
  else if lateOverflow then
    blastRounderSpecialCaseOverflow mode roundedResult.sign
  else
    EUnpackedFloat.mkNumber <| roundedResult.truncateFittingExponent tep tsp

@[bv_normalize]
def UnpackedFloat.blastIsUnderflowNonneg {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    Bool :=
  let minSubnormalExpBV : BitVec eu := BitVec.ofInt eu (minSubnormalExp tep tsp)
  uf.ex.slt minSubnormalExpBV

@[bv_normalize]
def UnpackedFloat.blastIsEarlyUnderflowNonneg {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    Bool :=
  let minSubnormalExpBV : BitVec eu := BitVec.ofInt eu (minSubnormalExp tep tsp - 1)
  uf.ex.slt minSubnormalExpBV


@[bv_normalize]
def UnpackedFloat.blastIsEarlyOverflowNonneg {eu su : Nat} (uf : UnpackedFloat eu su) (tep _tsp : Nat) :
    Bool :=
  let maxNormalExpBV : BitVec eu :=
    BitVec.ofInt eu (maxNormalExp tep)
  maxNormalExpBV.slt uf.ex

@[bv_normalize]
def UnpackedFloat.blastLowerNonneg {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    EUnpackedFloat (eu) (tsp + 1) :=
  let next := uf.blastRoundTowardZero tep tsp
  if uf.blastIsUnderflowNonneg tep tsp then
    -- greatest lower bound of 0 is +0
    EUnpackedFloat.mkNumber <| UnpackedFloat.mkZero false
  else if uf.blastIsEarlyOverflowNonneg tep tsp then
    EUnpackedFloat.mkNumber <| UnpackedFloat.maxNormal _ _ tep tsp false
  else
    EUnpackedFloat.mkNumber <| next

/--
If a number has a guard/sticky bit, then it needs to be rounded.
If it does not, then no rounding is necessary,
and the result is already correctly rounded for all rounding modes.
-/
def UnpackedFloat.needsRounding {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) : Bool :=
  uf.blastExtractGuardBit tep tsp || uf.blastExtractStickyBit tep tsp

/--
If the number is perfectly represented, then upper = lower,
otherwise, upper is the successor away from zero of lower.
-/
def UnpackedFloat.blastSuccessorAwayFromZeroNonnegAux {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    UnpackedFloat (eu) (tsp + 1) :=
  if uf.needsRounding tep tsp then
    uf.blastSuccessorAwayFromZero tep tsp
  else
    uf.blastRoundTowardZero tep tsp -- this will be a noop

@[bv_normalize]
def UnpackedFloat.blastUpperNonneg {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    EUnpackedFloat (eu) (tsp + 1) :=
  let next := uf.blastSuccessorAwayFromZeroNonnegAux tep tsp
  if next.blastIsUnderflowNonneg tep tsp then
    EUnpackedFloat.mkNumber <| UnpackedFloat.minSubnormalForPackedFloat _ _ tep tsp false
  else if next.blastIsEarlyOverflowNonneg tep tsp then
    EUnpackedFloat.mkInfinity false
  else
    EUnpackedFloat.mkNumber <| next

@[bv_normalize]
def UnpackedFloat.blastLowerNeg {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    EUnpackedFloat (eu) (tsp + 1) :=
  -((-uf).blastUpperNonneg tep tsp)

@[bv_normalize]
def UnpackedFloat.blastLower {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    EUnpackedFloat (eu) (tsp + 1) :=
  if uf.sign then
    uf.blastLowerNeg tep tsp
  else
    uf.blastLowerNonneg tep tsp

@[bv_normalize]
def UnpackedFloat.blastUpperNeg {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    EUnpackedFloat (eu) (tsp + 1) :=
  -((-uf).blastLowerNonneg tep tsp)

@[bv_normalize]
def UnpackedFloat.blastUpper {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    EUnpackedFloat (eu) (tsp + 1) :=
  if uf.sign then
    uf.blastUpperNeg tep tsp
  else
    uf.blastUpperNonneg tep tsp


@[bv_normalize]
def UnpackedFloat.blastIsLowerHalfNonneg {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) : Bool :=
  !uf.blastExtractGuardBit tep tsp
@[bv_normalize]
def UnpackedFloat.blastIsLowerHalfNeg {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) : Bool :=
  uf.neg.blastExtractGuardBit tep tsp

-- lowerHalf = !guardBit
@[bv_normalize]
def UnpackedFloat.blastIsLowerHalf {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) : Bool :=
  if uf.sign then
    uf.blastIsLowerHalfNeg tep tsp
  else
    uf.blastIsLowerHalfNonneg tep tsp

@[bv_normalize]
def UnpackedFloat.blastIsEvenNonneg {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) : Bool :=
  uf.blastExtractIsEven tep tsp

@[bv_normalize]
def UnpackedFloat.blastIsEvenNeg {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) : Bool :=
  !uf.blastExtractIsEven tep tsp

@[bv_normalize]
def UnpackedFloat.blastIsEven {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) : Bool :=
  if uf.sign then
    uf.blastIsEvenNeg tep tsp
  else
    uf.blastIsEvenNonneg tep tsp

-- We are in the tie break cast if we are exactly in the middle, *and are also*
-- in the normal range! If we are outside the normal range, then note that our distance to infinity
-- is much farther away.
@[bv_normalize]
def UnpackedFloat.blastIsTieBreakNonneg {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) : Bool :=
  uf.blastExtractGuardBit tep tsp && !uf.blastExtractStickyBit tep tsp

@[bv_normalize]
def UnpackedFloat.blastIsTieBreakNeg {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) : Bool :=
  uf.blastExtractGuardBit tep tsp && !uf.blastExtractStickyBit tep tsp

-- guard && !sticky
@[bv_normalize]
def UnpackedFloat.blastIsTieBreak {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) : Bool :=
  if uf.sign then
    uf.blastIsTieBreakNeg tep tsp
  else
    uf.blastIsTieBreakNonneg tep tsp


@[bv_normalize]
def UnpackedFloat.blastRounderForSign {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    EUnpackedFloat (eu) (tsp + 1) :=
  if uf.sign then
    uf.blastUpper tep tsp
  else
    uf.blastLower tep tsp


@[bv_normalize]
def UnpackedFloat.blastIsEvenLower {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) : Bool :=
  uf.blastIsEven tep tsp

@[bv_normalize]
def UnpackedFloat.blastIsEvenUpper {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) : Bool :=
  !uf.blastIsEven tep tsp


@[bv_normalize]
def UnpackedFloat.blastSmtLibRoundRNE {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    EUnpackedFloat (eu) (tsp + 1) :=
  -- NaN, infinity is handled separately, so this only handles the other cases.
  -- if uf.isZero then
  --   uf.blastRounderForSign tep tsp
  if ! uf.blastIsLowerHalf tep tsp && ! uf.blastIsTieBreak tep tsp then uf.blastUpper tep tsp
  else if uf.blastIsTieBreak tep tsp && uf.blastIsEvenUpper tep tsp then uf.blastUpper tep tsp
  else if uf.blastIsTieBreak tep tsp && uf.blastIsEvenLower tep tsp then uf.blastLower tep tsp
  else if uf.blastIsLowerHalf tep tsp then uf.blastLower tep tsp
  else EUnpackedFloat.mkNaN

@[bv_normalize]
def UnpackedFloat.blastSmtLibRoundRNA {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    EUnpackedFloat (eu) (tsp + 1) :=
  -- if uf.isZero then uf.blastRounderForSign tep tsp
  if uf.sign = false && !uf.blastIsLowerHalf tep tsp then uf.blastUpper tep tsp
  else if uf.sign = false && uf.blastIsLowerHalf tep tsp then uf.blastLower tep tsp
  else if uf.sign = true && !uf.blastIsLowerHalf tep tsp && !uf.blastIsTieBreak tep tsp then uf.blastUpper tep tsp
  else if uf.sign = true && (uf.blastIsLowerHalf tep tsp || uf.blastIsTieBreak tep tsp) then uf.blastLower tep tsp
  else EUnpackedFloat.mkNaN   -- does not occur, since NaN and infinity are handled separately.

@[bv_normalize]
def UnpackedFloat.blastSmtLibRoundRTP {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    EUnpackedFloat (eu) (tsp + 1) :=
  -- if uf.isZero then
  --   uf.blastRounderForSign tep tsp
  -- else
    uf.blastUpper tep tsp

@[bv_normalize]
def UnpackedFloat.blastSmtLibRoundRTN {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    EUnpackedFloat (eu) (tsp + 1) :=
  -- if uf.isZero then
  --   uf.blastRounderForSign tep tsp
  -- else
    uf.blastLower tep tsp

@[bv_normalize]
def UnpackedFloat.blastSmtLibRoundRTZ {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) :
    EUnpackedFloat (eu) (tsp + 1) :=
  -- if uf.isZero then
  --   EUnpackedFloat.mkNumber <| UnpackedFloat.mkZero uf.sign
  if uf.sign then
    uf.blastUpper tep tsp
  else
    uf.blastLower tep tsp


@[bv_normalize]
def UnpackedFloat.blastSmtLibRoundAux {eu su : Nat}
    (uf : UnpackedFloat eu su) (tep tsp : Nat) (mode : RoundingMode) :
    EUnpackedFloat (eu) (tsp + 1) :=
    match mode with
    | RoundingMode.RNE => blastSmtLibRoundRNE uf tep tsp
    | RoundingMode.RNA => blastSmtLibRoundRNA uf tep tsp
    | RoundingMode.RTP => blastSmtLibRoundRTP uf tep tsp
    | RoundingMode.RTN => blastSmtLibRoundRTN uf tep tsp
    | RoundingMode.RTZ => blastSmtLibRoundRTZ uf tep tsp

@[bv_normalize]
def EUnpackedFloat.truncateFittingExponent {eu su : Nat}
  (euf : EUnpackedFloat eu su) (tep tsp : Nat) :
  EUnpackedFloat (exponentWidth tep tsp) su :=
  match euf.state with
  | .Infinity => EUnpackedFloat.mkInfinity euf.sign
  | .NaN => EUnpackedFloat.mkNaN
  | .Number =>
    EUnpackedFloat.mkNumber <| euf.num.truncateFittingExponent tep tsp

@[bv_normalize]
def UnpackedFloat.blastSmtLibRound {eu su : Nat}
    (tep tsp : Nat) (mode : RoundingMode) (uf : UnpackedFloat eu su) :
    EUnpackedFloat (exponentWidth tep tsp) (tsp + 1) :=
  if uf.isZero then
    EUnpackedFloat.mkZero uf.sign
  else if uf.blastIsEarlyOverflowNonneg tep tsp then
    blastRounderSpecialCaseOverflow mode uf.sign
  else if uf.blastIsEarlyUnderflowNonneg tep tsp  then
    blastRounderSpecialCaseUnderflow mode uf.sign
  else
    let rounded := uf.truncateFittingExponent tep tsp
    let rounded := rounded.blastSmtLibRoundAux tep tsp mode
    -- | TODO: re-establish the normalized exponent.
    let rounded := rounded.normalize
    rounded

def EUnpackedFloat.blastSmtLibRound {eu su : Nat}
    (tep tsp : Nat) (mode : RoundingMode) (euf : EUnpackedFloat eu su) :
    EUnpackedFloat (exponentWidth tep tsp) (tsp + 1) :=
  match euf.state with
  | .Infinity => EUnpackedFloat.mkInfinity euf.sign
  | .NaN => EUnpackedFloat.mkNaN
  | .Number => euf.num.blastSmtLibRound tep tsp mode


def UnpackedFloat.debugBlastSmtLibRound {eu su : Nat}
    (uf : UnpackedFloat eu su) (tep tsp : Nat) (mode : RoundingMode) :
    (EUnpackedFloat (exponentWidth tep tsp) (tsp + 1) × String) :=
  let out := ""
  let out := out ++ s!"\n--- blastSmtLibRound: {repr uf} ---"
  let out := out ++ s!"\n  input: {uf.reprBinary}"
  let out := out ++ s!"\n  val (Q): {uf.toRat} = sig({uf.sig.toBitsStr}=nat:{uf.sig.toNat})) * 2 ** exp:([{uf.ex.toBitsStr}=int:{uf.ex.toInt}] - ({su - 1}))"
  let result := uf.blastSmtLibRound tep tsp mode
  let out := out ++ s!"\nresult(EUNum): {result.reprBinary} | (Q): {repr result.toExtRat}"
  let resultPacked : PackedFloat tep tsp := result.pack
  let out := out ++ s!"resultPacked: {resultPacked.reprBinary} | (Q): {repr resultPacked.toRat}"
  (result, out)


-- /--
-- The core rounding function, that rounds an `UnpackedFloat` to the target exponent and significand widths.
-- Computes the shared prefix (guard/sticky bit extraction, significand clearing),
-- then dispatches to `roundTowardZero` or `successorAwayFromZero` based on `roundingDecision`,
-- and finally handles overflow/underflow via `symfpuRounderHandleOverAndUnderflow`.
-- -/
-- @[bv_normalize]
-- def UnpackedFloat.roundSymFPU {eu su : Nat} {tep tsp : Nat}
--   (inUf : UnpackedFloat eu su)
--   (mode : RoundingMode) :
--   EUnpackedFloat (exponentWidth tep tsp) (tsp + 1) :=
--   if _hzero : inUf.isZero then
--     EUnpackedFloat.mkZero inUf.sign
--   else
--   let shouldRoundUp := roundingDecision
--     (mode := mode)
--     (sign := inUf.sign)
--     (significandEven := inUf.blastExtractIsEven tep tsp)
--     (guardBit := inUf.blastExtractGuardBit tep tsp)
--     (stickyBit := inUf.blastExtractStickyBit tep tsp)
--     (_exact := false)
--   let roundedUf := if shouldRoundUp then
--     inUf.blastSuccessorAwayFromZero tep tsp
--   else
--     inUf.blastRoundTowardZero tep tsp
--   symfpuRounderHandleOverAndUnderflow roundedUf mode

-- /-- Round an EUnpacked float, by ignoring NaN and infinity. -/
-- @[bv_normalize]
-- def EUnpackedFloat.blastRoundSymFPU {eu su : Nat} {tep tsp : Nat}
--   (inEuf : EUnpackedFloat eu su)
--   (mode : RoundingMode) :
--   EUnpackedFloat (exponentWidth tep tsp) (tsp + 1) :=
--   if inEuf.isNumber then
--     let inUf := inEuf.num
--     let out := UnpackedFloat.roundSymFPU (tep := tep) (tsp := tsp) inUf mode
--     -- let out := out.normalize
--     out
--   else if inEuf.isNaN then EUnpackedFloat.mkNaN
--   else EUnpackedFloat.mkInfinity inEuf.sign


def UnpackedFloat.blastRound {eu su : Nat} (uf : UnpackedFloat eu su) (tep tsp : Nat) (mode : RoundingMode) :
    EUnpackedFloat (exponentWidth tep tsp) (tsp + 1) :=
  uf.blastSmtLibRound tep tsp mode

-- /--
-- Debug variant of rounding: mirrors `UnpackedFloat.round` step-by-step while logging
-- each intermediate value to a string.

-- Preconditions for rounding to succeed:

-- (hs : su >= tsp + 1 + 2)
-- (he : eu >= tep)
-- (hs' : su >= 1) :
-- -/
-- @[bv_normalize]
-- def UnpackedFloat.debugRoundSymFPU {eu su : Nat} {tep tsp : Nat}
--   (inUf : UnpackedFloat eu su)
--   (mode : RoundingMode) :
--   (EUnpackedFloat (exponentWidth tep tsp) (tsp + 1) × String) :=
--   let out := ""
--   let out := out ++ s!"\n--- rounding: {repr inUf} ---"
--   let out := out ++ s!"\n  input: {inUf.reprBinary}"
--   let out := out ++ s!"\n  val (Q): {inUf.toRat} = sig({inUf.sig.toBitsStr}=nat:{inUf.sig.toNat})) * 2 ** exp:([{inUf.ex.toBitsStr}=int:{inUf.ex.toInt}] - ({su - 1}))"
--   let out := out ++ s!"\ntargetMinNormalExp: int:{minNormalExp tep}"
--   let out := out ++ s!"\nmaxNormalExp: {maxNormalExp tep}"
--   let out := out ++ s!"\nminSubnormalExp: {minSubnormalExp tep tsp}"
--   if _hzero : inUf.isZero then
--     let result : EUnpackedFloat (exponentWidth tep tsp) (tsp + 1) :=
--       EUnpackedFloat.mkZero inUf.sign
--     let out := out ++ s!"\nisZero: true → early return mkZero"
--     let out := out ++ s!"\nresult(EUNum): {result.reprBinary} | (Q): {repr result.toExtRat}"
--     let resultPacked : PackedFloat tep tsp := result.pack
--     let out := out ++ s!"\nresultPacked: {resultPacked.reprBinary} | (Q): {repr resultPacked.toRat}"
--     (result, out)
--   else
--   let out := out ++ s!"\nisZero: false"

--   let guardBitIdx : BitVec su := inUf.guardBitIndex tep tsp
--   let out := out ++ s!"\nguardBitIndex: {guardBitIdx.toBitsStr} = nat:{guardBitIdx.toNat}"
--   let guardBit : Bool := inUf.blastExtractGuardBit tep tsp
--   let stickyBit : Bool := inUf.blastExtractStickyBit tep tsp
--   let isEven : Bool := inUf.blastExtractIsEven tep tsp
--   let out := out ++ s!"\nguardBit: {guardBit}"
--   let out := out ++ s!"\nstickyBit: {stickyBit}"
--   let out := out ++ s!"\nisEven: {isEven}"

--   let shouldRoundUp := roundingDecision
--     (mode := mode)
--     (sign := inUf.sign)
--     (significandEven := isEven)
--     (guardBit := guardBit)
--     (stickyBit := stickyBit)
--     (_exact := false)
--   let out := out ++ s!"\nshouldRoundUp: {shouldRoundUp}"

--   let roundedUf : UnpackedFloat (eu) (tsp + 1) :=
--     if shouldRoundUp then
--       inUf.blastSuccessorAwayFromZero tep tsp
--     else
--       inUf.blastRoundTowardZero tep tsp
--   let out := out ++ s!"\nroundedUf.ex: {roundedUf.ex.toBitsStr} = int:{roundedUf.ex.toInt}"
--   let out := out ++ s!"\nroundedUf.sig: {roundedUf.sig.toBitsStr} = nat:{roundedUf.sig.toNat}"

--   let maxNormalExpBV : BitVec (eu + 1) :=
--     BitVec.ofInt (eu + 1) (maxNormalExp tep)
--   let lateOverflow : Bool := maxNormalExpBV.slt roundedUf.ex
--   let minSubnormalExpBV : BitVec (eu + 1) :=
--     BitVec.ofInt (eu + 1) (minSubnormalExp tep tsp)
--   let lateUnderflow : Bool := roundedUf.ex.slt minSubnormalExpBV
--   let out := out ++ s!"\nlateOverflow: {lateOverflow} = roundedUf.ex({roundedUf.ex.toBitsStr}=int:{roundedUf.ex.toInt}) > maxNormalExpBV({maxNormalExpBV.toBitsStr}=int:{maxNormalExpBV.toInt})"
--   let out := out ++ s!"\nlateUnderflow: {lateUnderflow} = roundedUf.ex({roundedUf.ex.toBitsStr}=int:{roundedUf.ex.toInt}) < minSubnormalExpBV({minSubnormalExpBV.toBitsStr}=int:{minSubnormalExpBV.toInt})"

--   let result : EUnpackedFloat (exponentWidth tep tsp) (tsp + 1) :=
--     symfpuRounderHandleOverAndUnderflow roundedUf mode
--   let out := out ++ s!"\nresult(EUNum): {result.reprBinary} | (Q): {repr result.toExtRat}"

--   -- let resultNormalized : EUnpackedFloat (exponentWidth tep tsp) (tsp + 1) :=
--   --   if result.isNumber then
--   --     let num := result.num
--   --     EUnpackedFloat.mkNumber num.normalize
--   --   else result
--   -- let out := out ++ s!"\nresult normalized: {resultNormalized.reprBinary} | (Q): {repr resultNormalized.toExtRat}"

--   let resultPacked : PackedFloat tep tsp := result.pack
--   let out := out ++ s!"\nresultPacked: {resultPacked.reprBinary} | (Q): {repr resultPacked.toRat}"
--   (result, out)


-- TODO: these are expensive checks, so move them into a separate file.
def checkRoundCorrect (EUnpacked SUnpackedNoHidden : Nat)
  (EOut SOutNoHidden : Nat)
  (mode : RoundingMode)
  : IO Bool := do
  let mut outError : String := ""
  let mut nsucceeded : Nat := 0
  let mut nfailed : Nat := 0

  for originalPacked in mkPackedFloats EUnpacked SUnpackedNoHidden do
    let originalEUnpacked := originalPacked.unpack

    if originalPacked.toExtRat ≠ originalEUnpacked.toExtRat then
      let err : String := ""
      let err := err ++ s!"\nFailed unpacking roundtrip ❌ | original {originalEUnpacked.reprBinary}"
      let err := err ++ s!"\n  original (packed) {originalPacked.reprBinary}"
      let err := err ++ s!"\n  original (Q) {repr originalPacked.toExtRat}"
      IO.println err
      outError := err
      nfailed := nfailed + 1
      continue

    if ! originalEUnpacked.isNumber then continue

    let originalUnpacked := originalEUnpacked.num
    let originalNormalized := originalUnpacked.normalize
    let (outputRoundedEUnpacked, log) :=
      -- UnpackedFloat.debugRoundSymFPU (tep := EOut) (tsp := SOutNoHidden)
      UnpackedFloat.debugBlastSmtLibRound (tep := EOut) (tsp := SOutNoHidden)
        originalNormalized mode
    let outputRoundedPacked := outputRoundedEUnpacked.pack

    -- check that I produce a result that packs properly.
    if ! outputRoundedEUnpacked.pack.unpack.pack.equal_denotation outputRoundedEUnpacked.pack then
      let err : String := ""
      let err := err ++ s!"\nFailed packing roundtrip ❌ | original {repr originalEUnpacked}"
      let err := err ++ s!"\n  original (packed) {repr originalPacked}"
      let err := err ++ s!"\n  output rounded (eunpacked) {repr outputRoundedEUnpacked}"
      let err := err ++ s!"\n  output rounded (eunpacked.Q) {repr outputRoundedEUnpacked.toExtRat}"
      let err := err ++ s!"\n  output rounded (unpacked(packed(eunpacked))) {repr outputRoundedEUnpacked.pack.unpack}"
      let err := err ++ s!"\n  output rounded (unpacked(packed(eunpacked)).Q) {repr outputRoundedEUnpacked.pack.unpack.toExtRat}"
      IO.println err
      outError := err
      nfailed := nfailed + 1
      continue

    let expectedPacked : PackedFloat EOut SOutNoHidden :=
       originalPacked.toEFixed.round (exWidth := EOut) (sigWidth := SOutNoHidden) mode
    let expectedEUnpacked := expectedPacked.unpack
    if outputRoundedPacked.equal_denotation expectedPacked then
      IO.println s!"Succeeded ✅ | original {repr originalEUnpacked}"
      nsucceeded := nsucceeded + 1
    else
      let err : String := ""
      let err := err ++ s!"\nFailed ❌ | original {originalEUnpacked.reprBinary}"
      let err := err ++ s!"\n  original (packed) {originalPacked.reprBinary}"
      let err := err ++ s!"\n  original (Q) {repr originalPacked.toRat?}"
      let err := err ++ s!"\n  original (eunpacked) {repr originalEUnpacked.reprBinary}"
      let err := err ++ s!"\n  --"
      let err := err ++ s!"\n  output rounded (eunpacked) {outputRoundedEUnpacked.reprBinary}"
      let err := err ++ s!"\n  output rounded (eunpacked.Q) {repr outputRoundedEUnpacked.toExtRat}"
      let err := err ++ s!"\n  output rounded (packed) {outputRoundedPacked.reprBinary}"
      let err := err ++ s!"\n  output rounded (packed.Q) {repr outputRoundedPacked.toExtRat}"
      let err := err ++ s!"\n  --"
      let err := err ++ s!"\n  expected (packed) {expectedPacked.reprBinary}"
      let err := err ++ s!"\n  expected (Q) {repr expectedPacked.toExtRat}"
      let err := err ++ s!"\n  expected (eunpacked) {expectedEUnpacked.reprBinary}"
      let err := err ++ s!"\n\n{log}"
      IO.println err
      outError := err
      nfailed := nfailed + 1
  if nfailed = 0 then
    IO.println "All succeeded ✅"
  else
    -- | this is fixed point, with two digits of precision.
    let fracSuccess : Float := (nsucceeded.toFloat * 100.0) / ((nsucceeded + nfailed).toFloat)
    throw (IO.Error.userError s!"({nsucceeded} succeeded / {nsucceeded + nfailed} total) ({fracSuccess}% succeeded) ({nfailed} failures) ❌\n{outError}")
  return nfailed = 0


-- TODO: these are expensive checks, so move them into a separate file.
-- All of these should succeed with zero failures (the ExtRat round matches
-- the bitblasted UnpackedFloat round for every input).
#guard_msgs(error, drop info) in #eval checkRoundCorrect 4 5 4 2 .RNA
#guard_msgs(error, drop info) in #eval checkRoundCorrect 4 5 4 2 .RNE
#guard_msgs(error, drop info) in #eval checkRoundCorrect 4 5 4 2 .RTZ
#guard_msgs(error, drop info) in #eval checkRoundCorrect 2 6 2 4 .RTP
#guard_msgs(error, drop info) in #eval checkRoundCorrect 4 5 4 2 .RTP
#guard_msgs(error, drop info) in #eval checkRoundCorrect 4 5 4 2 .RTN
