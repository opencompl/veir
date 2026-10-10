module

public import Veir.Analysis.DataFlow.Domains.KnownBitsDomain
public import Veir.Analysis.DataFlow.SparseForwardDataFlowAnalysis

import Veir.Interfaces.FoldInterfaces

public section

namespace Veir

/-!
# Known bits analysis

This sparse forward analysis tracks fixed width integer bits that are provably zero
or one. Its transfer functions follow LLVM's `KnownBits` algorithms for arithmetic,
bitwise operations, shifts, casts, comparisons, division, remainder, and structural
bit operations across the Arith, Comb, and LLVM dialects.
-/

namespace KnownBitsAnalysis

instance : SparseFactSpec .knownBits KnownBitsLattice where
  Metadata := Unit
  payloadEq := rfl

/-- Return the width of the first integer result, if one exists. -/
private def resultWidth? (resultTypes : Array TypeAttr) : Option Nat := do
  let resultType ← resultTypes[0]?
  let .integerType intType := resultType.val | none
  return intType.bitwidth

/-- Lift a unary known bits operation to the sparse lattice, preserving bottom. -/
private def liftUnary
    (operation : KnownBits → KnownBits) : KnownBitsLattice → KnownBitsLattice
  | .bottom => .bottom
  | .known operand => .known (operation operand)

/--
Lift a partial binary known bits operation to the sparse lattice. A width mismatch
produces an unknown value at the left operand's width.
-/
private def liftBinary
    (operation : KnownBits → KnownBits → Option KnownBits) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice
  | .bottom, _ | _, .bottom => .bottom
  | .known lhs, .known rhs =>
      (operation lhs rhs).map (.known ·) |>.getD (.unknown lhs.bitwidth)

/-- Lift a total binary known bits operation to the sparse lattice, preserving bottom. -/
private def liftBinaryTotal
    (operation : KnownBits → KnownBits → KnownBits) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice
  | .bottom, _ | _, .bottom => .bottom
  | .known lhs, .known rhs => .known (operation lhs rhs)

/-- Apply a unary lattice operation, returning `fallback` when the operand count is not one. -/
private def applyUnary
    (fallback operands : Array KnownBitsLattice)
    (operation : KnownBitsLattice → KnownBitsLattice) : Array KnownBitsLattice :=
  match operands.toList with
  | [operand] => #[operation operand]
  | _ => fallback

/-- Apply a binary lattice operation, returning `fallback` when the operand count is not two. -/
private def applyBinary
    (fallback operands : Array KnownBitsLattice)
    (operation : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice) :
    Array KnownBitsLattice :=
  match operands.toList with
  | [lhs, rhs] => #[operation lhs rhs]
  | _ => fallback

/-- Apply a ternary lattice operation, returning `fallback` when the operand count is not three. -/
private def applyTernary
    (fallback operands : Array KnownBitsLattice)
    (operation : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice → KnownBitsLattice) :
    Array KnownBitsLattice :=
  match operands.toList with
  | [first, second, third] => #[operation first second third]
  | _ => fallback

/-- Fold a binary lattice operation over the operands, returning `fallback` when they are empty. -/
private def applyVariadic
    (fallback operands : Array KnownBitsLattice)
    (operation : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice) :
    Array KnownBitsLattice :=
  match operands.toList with
  | [] => fallback
  | first :: rest => #[rest.foldl operation first]

/--
Apply a binary lattice operation that produces two results, returning `fallback`
when the operand count is not two.
-/
private def applyBinaryPair
    (fallback operands : Array KnownBitsLattice)
    (operation : KnownBitsLattice → KnownBitsLattice →
      KnownBitsLattice × KnownBitsLattice) : Array KnownBitsLattice :=
  match operands.toList with
  | [lhs, rhs] =>
      let (first, second) := operation lhs rhs
      #[first, second]
  | _ => fallback

/-- Whether a binary operation uses the same SSA value for both operands. -/
private def hasSameBinaryOperands (op : OperationPtr) (irCtx : WfIRContext OpCode) : Bool :=
  match (op.getOperands! irCtx.raw).toList with
  | [lhs, rhs] => lhs == rhs
  | _ => false

/-- Determine the known overflow bit for unsigned addition. -/
private def unsignedAddOverflow? (lhs rhs : KnownBits) : Option KnownBits :=
  if lhs.bitwidth ≠ rhs.bitwidth then none else
  let limit := 2 ^ lhs.bitwidth
  let minSum := lhs.unsignedMin.toNat + rhs.unsignedMin.toNat
  let maxSum := lhs.unsignedMax.toNat + rhs.unsignedMax.toNat
  if limit ≤ minSum then some (KnownBits.constant 1 1)
  else if maxSum < limit then some (KnownBits.constant 1 0)
  else some (KnownBits.unknown 1)

/-- Convert a fully known lattice value into a concrete runtime value for folding. -/
private def exactRuntimeValue? : KnownBitsLattice → Option RuntimeValue
  | .known bits =>
      if bits.isConstant then
        some (.int bits.bitwidth (.val bits.one))
      else
        none
  | .bottom => none

/-- Convert one generic fold result back into the known bits lattice. -/
private def knownBitsOfFoldResult
    (operands : Array KnownBitsLattice)
    (resultType : TypeAttr)
    (result : FoldDecision) : KnownBitsLattice :=
  match resultType.val, result with
  | .integerType intType, .useOperand index =>
      operands[index]?.getD (.unknown intType.bitwidth)
  | .integerType intType, .useConstant (.int bitwidth (.val value)) =>
      if h : bitwidth = intType.bitwidth then
        let value := value.cast h
        .known (KnownBits.ofMasks (~~~value) value)
      else
        .unknown intType.bitwidth
  | .integerType intType, .useConstant _ => .unknown intType.bitwidth
  | _, _ => ⊥

/-- Try the operation's generic fold hook, providing concrete values for exact operands. -/
private def foldOperation?
    (op : OperationPtr)
    (operands : Array KnownBitsLattice)
    (resultTypes : Array TypeAttr)
    (irCtx : WfIRContext OpCode) : Option (Array KnownBitsLattice) := do
  let opType := op.getOpType! irCtx.raw
  let exactOperands := operands.map exactRuntimeValue?
  let results ← opType.foldsTo
    (op.getProperties! irCtx.raw opType) resultTypes exactOperands
  return (results.zip resultTypes).map fun (result, resultType) =>
    knownBitsOfFoldResult operands resultType result

/-- Zero extend known bits, first refining the sign bit when `nneg` is set. -/
private def zeroExtend (resultWidth : Nat) (nneg : Bool) (bits : KnownBits) : KnownBits :=
  let bits := if nneg then
    (bits.refineWith (KnownBits.ofMasks (KnownBits.highMask bits.bitwidth 1) 0)).getD bits
  else bits
  bits.zext resultWidth

/-- Select one lattice value for a constant condition, or intersect both possible values. -/
private def selectLattice
    (condition trueValue falseValue : KnownBitsLattice) : KnownBitsLattice :=
  match condition, trueValue, falseValue with
  | .bottom, _, _ | _, .bottom, _ | _, _, .bottom => ⊥
  | .known condition, .known trueValue, .known falseValue =>
      if condition.isConstant then
        .known (if condition.one ≠ 0 then trueValue else falseValue)
      else
        .known <| (trueValue.intersect falseValue).getD (KnownBits.unknown trueValue.bitwidth)

/-- Apply a funnel shift when its shift amount is exactly known. -/
private def funnelShiftLattice
    (operation : KnownBits → KnownBits → Nat → Option KnownBits)
    (lhs rhs amount : KnownBitsLattice) : KnownBitsLattice :=
  match lhs, rhs, amount with
  | .bottom, _, _ | _, .bottom, _ | _, _, .bottom => ⊥
  | .known lhs, .known rhs, .known amount =>
      if amount.isConstant then
        (operation lhs rhs amount.one.toNat).map (.known ·) |>.getD (.unknown lhs.bitwidth)
      else
        .unknown lhs.bitwidth

private def transferArithConstant (bitwidth : Nat) (value : Int) : KnownBitsLattice :=
  .constant bitwidth value

private def transferLLVMConstant (bitwidth : Nat) (value : Int) : KnownBitsLattice :=
  .constant bitwidth value

private def transferHWConstant (bitwidth : Nat) (value : Int) : KnownBitsLattice :=
  .constant bitwidth value

private def transferArithAndI : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.bitwiseAnd?

private def transferLLVMAnd : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.bitwiseAnd?

private def transferCombAnd : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.bitwiseAnd?

private def transferArithOrI : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.bitwiseOr?

private def transferLLVMOr : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.bitwiseOr?

private def transferCombOr : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.bitwiseOr?

private def transferArithXorI : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.bitwiseXor?

private def transferLLVMXor : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.bitwiseXor?

private def transferCombXor : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.bitwiseXor?

private def transferArithAddI (selfAdd nsw nuw : Bool) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  fun lhs rhs =>
    if selfAdd then
      match lhs, rhs with
      | .bottom, _ | _, .bottom => ⊥
      | .known lhs, .known _ =>
          .known (lhs.shl (KnownBits.constant 8 1) nsw nuw)
    else
      liftBinary (fun lhs rhs => lhs.add? rhs nsw nuw) lhs rhs

private def transferLLVMAdd (selfAdd nsw nuw : Bool) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  fun lhs rhs =>
    if selfAdd then
      match lhs, rhs with
      | .bottom, _ | _, .bottom => ⊥
      | .known lhs, .known _ =>
          .known (lhs.shl (KnownBits.constant 8 1) nsw nuw)
    else
      liftBinary (fun lhs rhs => lhs.add? rhs nsw nuw) lhs rhs

private def transferCombAdd : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.add?

private def transferArithAddUIExtended
    (lhs rhs : KnownBitsLattice) : KnownBitsLattice × KnownBitsLattice :=
  match lhs, rhs with
  | .bottom, _ | _, .bottom => (⊥, ⊥)
  | .known lhs, .known rhs =>
      let sum := (lhs.add? rhs).map (.known ·) |>.getD (.unknown lhs.bitwidth)
      let overflow := unsignedAddOverflow? lhs rhs |>.map (.known ·) |>.getD (.unknown 1)
      (sum, overflow)

private def transferArithSubI (nsw nuw : Bool) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary fun lhs rhs => lhs.sub? rhs nsw nuw

private def transferLLVMSub (nsw nuw : Bool) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary fun lhs rhs => lhs.sub? rhs nsw nuw

private def transferCombSub : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.sub?

private def transferArithSubUIExtended
    (lhs rhs : KnownBitsLattice) : KnownBitsLattice × KnownBitsLattice :=
  match lhs, rhs with
  | .bottom, _ | _, .bottom => (⊥, ⊥)
  | .known lhs, .known rhs =>
      let difference := (lhs.sub? rhs).map (.known ·) |>.getD (.unknown lhs.bitwidth)
      (difference, .known (lhs.compare .ult rhs))

private def transferArithMulI : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.mul?

private def transferLLVMMul : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.mul?

private def transferCombMul : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.mul?

private def transferArithMulUIExtended
    (lhs rhs : KnownBitsLattice) : KnownBitsLattice × KnownBitsLattice :=
  match lhs, rhs with
  | .bottom, _ | _, .bottom => (⊥, ⊥)
  | .known lhs, .known rhs =>
      let low := (lhs.mul? rhs).map (.known ·) |>.getD (.unknown lhs.bitwidth)
      let high := (lhs.mulhu? rhs).map (.known ·) |>.getD (.unknown lhs.bitwidth)
      (low, high)

private def transferArithMulSIExtended
    (lhs rhs : KnownBitsLattice) : KnownBitsLattice × KnownBitsLattice :=
  match lhs, rhs with
  | .bottom, _ | _, .bottom => (⊥, ⊥)
  | .known lhs, .known rhs =>
      let low := (lhs.mul? rhs).map (.known ·) |>.getD (.unknown lhs.bitwidth)
      let high := (lhs.mulhs? rhs).map (.known ·) |>.getD (.unknown lhs.bitwidth)
      (low, high)

private def transferArithShLI (nsw nuw : Bool) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinaryTotal fun lhs rhs => lhs.shl rhs nsw nuw

private def transferLLVMShL (nsw nuw : Bool) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinaryTotal fun lhs rhs => lhs.shl rhs nsw nuw

private def transferCombShL : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinaryTotal KnownBits.shl

private def transferArithShrUI (exact : Bool) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinaryTotal fun lhs rhs => lhs.lshr rhs exact

private def transferLLVMLShr (exact : Bool) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinaryTotal fun lhs rhs => lhs.lshr rhs exact

private def transferCombShrU : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinaryTotal KnownBits.lshr

private def transferArithShrSI (exact : Bool) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinaryTotal fun lhs rhs => lhs.ashr rhs exact

private def transferLLVMAShr (exact : Bool) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinaryTotal fun lhs rhs => lhs.ashr rhs exact

private def transferCombShrS : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinaryTotal KnownBits.ashr

private def transferArithDivUI (exact : Bool) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary fun lhs rhs => lhs.udiv? rhs exact

private def transferLLVMUDiv (exact : Bool) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary fun lhs rhs => lhs.udiv? rhs exact

private def transferCombDivU : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.udiv?

private def transferArithDivSI (exact : Bool) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary fun lhs rhs => lhs.sdiv? rhs exact

private def transferLLVMSDiv (exact : Bool) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary fun lhs rhs => lhs.sdiv? rhs exact

private def transferCombDivS : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.sdiv?

private def transferArithRemUI : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.urem?

private def transferLLVMURem : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.urem?

private def transferCombModU : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.urem?

private def transferArithRemSI : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.srem?

private def transferLLVMSRem : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.srem?

private def transferCombModS : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.srem?

private def transferArithExtUI (resultWidth : Nat) (nneg : Bool) :
    KnownBitsLattice → KnownBitsLattice :=
  liftUnary (zeroExtend resultWidth nneg)

private def transferLLVMZExt (resultWidth : Nat) (nneg : Bool) :
    KnownBitsLattice → KnownBitsLattice :=
  liftUnary (zeroExtend resultWidth nneg)

private def transferArithExtSI (resultWidth : Nat) : KnownBitsLattice → KnownBitsLattice :=
  liftUnary (KnownBits.sext · resultWidth)

private def transferLLVMSExt (resultWidth : Nat) : KnownBitsLattice → KnownBitsLattice :=
  liftUnary (KnownBits.sext · resultWidth)

private def transferArithTruncI (resultWidth : Nat) : KnownBitsLattice → KnownBitsLattice :=
  liftUnary (KnownBits.trunc · resultWidth)

private def transferLLVMTrunc (resultWidth : Nat) : KnownBitsLattice → KnownBitsLattice :=
  liftUnary (KnownBits.trunc · resultWidth)

private def transferArithCmpI (predicate : Data.LLVM.IntPred) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinaryTotal fun lhs rhs => lhs.compare predicate rhs

private def transferLLVMICmp (predicate : Data.LLVM.IntPred) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinaryTotal fun lhs rhs => lhs.compare predicate rhs

private def transferCombICmp (predicate : Data.LLVM.IntPred) :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinaryTotal fun lhs rhs => lhs.compare predicate rhs

private def transferArithSelect :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  selectLattice

private def transferLLVMSelect :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  selectLattice

private def transferCombMux :
    KnownBitsLattice → KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  selectLattice

private def transferArithMaxUI : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.umax?

private def transferLLVMUMax : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.umax?

private def transferArithMinUI : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.umin?

private def transferLLVMUMin : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.umin?

private def transferArithMaxSI : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.smax?

private def transferLLVMSMax : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.smax?

private def transferArithMinSI : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.smin?

private def transferLLVMSMin : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.smin?

private def transferCombConcat : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinaryTotal KnownBits.concat

private def transferCombExtract (lowBit resultWidth : Nat) :
    KnownBitsLattice → KnownBitsLattice :=
  liftUnary fun bits => bits.extract lowBit resultWidth

private def transferCombReverse : KnownBitsLattice → KnownBitsLattice :=
  liftUnary KnownBits.reverse

private def transferLLVMBitReverse : KnownBitsLattice → KnownBitsLattice :=
  liftUnary KnownBits.reverse

private def transferCombReplicate (resultWidth : Nat) : KnownBitsLattice → KnownBitsLattice :=
  liftUnary (KnownBits.replicate · resultWidth)

private def transferLLVMByteSwap : KnownBitsLattice → KnownBitsLattice :=
  liftUnary KnownBits.byteSwap

private def transferLLVMFShL
    (lhs rhs amount : KnownBitsLattice) : KnownBitsLattice :=
  funnelShiftLattice KnownBits.fshl? lhs rhs amount

private def transferLLVMFShR
    (lhs rhs amount : KnownBitsLattice) : KnownBitsLattice :=
  funnelShiftLattice KnownBits.fshr? lhs rhs amount

private def transferLLVMCountPopulation : KnownBitsLattice → KnownBitsLattice :=
  liftUnary KnownBits.ctpop

private def transferLLVMCountLeadingZeros (isZeroPoison : Bool) :
    KnownBitsLattice → KnownBitsLattice :=
  liftUnary (KnownBits.ctlz · isZeroPoison)

private def transferLLVMCountTrailingZeros (isZeroPoison : Bool) :
    KnownBitsLattice → KnownBitsLattice :=
  liftUnary (KnownBits.cttz · isZeroPoison)

private def transferLLVMAbs (isIntMinPoison : Bool) :
    KnownBitsLattice → KnownBitsLattice :=
  liftUnary (KnownBits.abs · isIntMinPoison)

private def transferLLVMUAddSat : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.uaddSat?

private def transferLLVMUSubSat : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.usubSat?

private def transferLLVMSAddSat : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.saddSat?

private def transferLLVMSSubSat : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice :=
  liftBinary KnownBits.ssubSat?

/--
Infer known bits for one operation. Bottom operands cause the transfer to wait for
more information; unsupported integer results receive a width-aware unknown value.
-/
def transfer
    (op : OperationPtr)
    (operands : Array KnownBitsLattice)
    (irCtx : WfIRContext OpCode) : Array KnownBitsLattice :=
  let numResults := op.getNumResults! irCtx.raw
  let resultTypes := op.getResultTypes! irCtx.raw
  let pessimisticUpdates := resultTypes.map fun resultType =>
    match resultType.val with
    | .integerType intType => .unknown intType.bitwidth
    | _ => ⊥

  if op.getNumRegions! irCtx.raw ≠ 0 then
    pessimisticUpdates
  else if operands.any (· = ⊥) then
    Array.replicate numResults ⊥
  else
    let opType := op.getOpType! irCtx.raw
    let resultWidth := (resultWidth? resultTypes).getD 0
    match foldOperation? op operands resultTypes irCtx with
    | some results => results
    | none =>
        match opType with
        | OpCode.arith Arith.constant =>
          let props := op.getProperties! irCtx.raw (OpCode.arith Arith.constant)
          #[transferArithConstant props.value.type.bitwidth props.value.value]
        | OpCode.llvm Llvm.mlir__constant =>
          let props := op.getProperties! irCtx.raw (OpCode.llvm Llvm.mlir__constant)
          match props.value with
          | .integer attr => #[transferLLVMConstant attr.type.bitwidth attr.value]
          | _ => pessimisticUpdates
        | OpCode.hw HW.constant =>
          let props := op.getProperties! irCtx.raw (OpCode.hw HW.constant)
          #[transferHWConstant props.value.type.bitwidth props.value.value]
        | OpCode.arith Arith.andi =>
          applyBinary pessimisticUpdates operands transferArithAndI
        | OpCode.llvm Llvm.and =>
          applyBinary pessimisticUpdates operands transferLLVMAnd
        | OpCode.comb Comb.and =>
          applyVariadic pessimisticUpdates operands transferCombAnd
        | OpCode.arith Arith.ori =>
          applyBinary pessimisticUpdates operands transferArithOrI
        | OpCode.llvm Llvm.or =>
          applyBinary pessimisticUpdates operands transferLLVMOr
        | OpCode.comb Comb.or =>
          applyVariadic pessimisticUpdates operands transferCombOr
        | OpCode.arith Arith.xori =>
          applyBinary pessimisticUpdates operands transferArithXorI
        | OpCode.llvm Llvm.xor =>
          applyBinary pessimisticUpdates operands transferLLVMXor
        | OpCode.comb Comb.xor =>
          applyVariadic pessimisticUpdates operands transferCombXor
        | OpCode.arith Arith.addi =>
          let props := op.getProperties! irCtx.raw (OpCode.arith Arith.addi)
          applyBinary pessimisticUpdates operands <|
            transferArithAddI (hasSameBinaryOperands op irCtx) props.attr.nsw props.attr.nuw
        | OpCode.llvm Llvm.add =>
          let props := op.getProperties! irCtx.raw (OpCode.llvm Llvm.add)
          applyBinary pessimisticUpdates operands <|
            transferLLVMAdd (hasSameBinaryOperands op irCtx) props.nsw props.nuw
        | OpCode.comb Comb.add =>
          applyVariadic pessimisticUpdates operands transferCombAdd
        | OpCode.arith Arith.addui_extended =>
          applyBinaryPair pessimisticUpdates operands transferArithAddUIExtended
        | OpCode.arith Arith.subi =>
          let props := op.getProperties! irCtx.raw (OpCode.arith Arith.subi)
          applyBinary pessimisticUpdates operands <|
            transferArithSubI props.attr.nsw props.attr.nuw
        | OpCode.llvm Llvm.sub =>
          let props := op.getProperties! irCtx.raw (OpCode.llvm Llvm.sub)
          applyBinary pessimisticUpdates operands <| transferLLVMSub props.nsw props.nuw
        | OpCode.comb Comb.sub =>
          applyBinary pessimisticUpdates operands transferCombSub
        | OpCode.arith Arith.subui_extended =>
          applyBinaryPair pessimisticUpdates operands transferArithSubUIExtended
        | OpCode.arith Arith.muli =>
          applyBinary pessimisticUpdates operands transferArithMulI
        | OpCode.llvm Llvm.mul =>
          applyBinary pessimisticUpdates operands transferLLVMMul
        | OpCode.comb Comb.mul =>
          applyVariadic pessimisticUpdates operands transferCombMul
        | OpCode.arith Arith.mului_extended =>
          applyBinaryPair pessimisticUpdates operands transferArithMulUIExtended
        | OpCode.arith Arith.mulsi_extended =>
          applyBinaryPair pessimisticUpdates operands transferArithMulSIExtended
        | OpCode.arith Arith.shli =>
          let props := op.getProperties! irCtx.raw (OpCode.arith Arith.shli)
          applyBinary pessimisticUpdates operands <|
            transferArithShLI props.attr.nsw props.attr.nuw
        | OpCode.llvm Llvm.shl =>
          let props := op.getProperties! irCtx.raw (OpCode.llvm Llvm.shl)
          applyBinary pessimisticUpdates operands <| transferLLVMShL props.nsw props.nuw
        | OpCode.comb Comb.shl =>
          applyBinary pessimisticUpdates operands transferCombShL
        | OpCode.arith Arith.shrui =>
          let props := op.getProperties! irCtx.raw (OpCode.arith Arith.shrui)
          applyBinary pessimisticUpdates operands <| transferArithShrUI props.exact
        | OpCode.llvm Llvm.lshr =>
          let props := op.getProperties! irCtx.raw (OpCode.llvm Llvm.lshr)
          applyBinary pessimisticUpdates operands <| transferLLVMLShr props.exact
        | OpCode.comb Comb.shru =>
          applyBinary pessimisticUpdates operands transferCombShrU
        | OpCode.arith Arith.shrsi =>
          let props := op.getProperties! irCtx.raw (OpCode.arith Arith.shrsi)
          applyBinary pessimisticUpdates operands <| transferArithShrSI props.exact
        | OpCode.llvm Llvm.ashr =>
          let props := op.getProperties! irCtx.raw (OpCode.llvm Llvm.ashr)
          applyBinary pessimisticUpdates operands <| transferLLVMAShr props.exact
        | OpCode.comb Comb.shrs =>
          applyBinary pessimisticUpdates operands transferCombShrS
        | OpCode.arith Arith.divui =>
          let props := op.getProperties! irCtx.raw (OpCode.arith Arith.divui)
          applyBinary pessimisticUpdates operands <| transferArithDivUI props.exact
        | OpCode.llvm Llvm.udiv =>
          let props := op.getProperties! irCtx.raw (OpCode.llvm Llvm.udiv)
          applyBinary pessimisticUpdates operands <| transferLLVMUDiv props.exact
        | OpCode.comb Comb.divu =>
          applyBinary pessimisticUpdates operands transferCombDivU
        | OpCode.arith Arith.divsi =>
          let props := op.getProperties! irCtx.raw (OpCode.arith Arith.divsi)
          applyBinary pessimisticUpdates operands <| transferArithDivSI props.exact
        | OpCode.llvm Llvm.sdiv =>
          let props := op.getProperties! irCtx.raw (OpCode.llvm Llvm.sdiv)
          applyBinary pessimisticUpdates operands <| transferLLVMSDiv props.exact
        | OpCode.comb Comb.divs =>
          applyBinary pessimisticUpdates operands transferCombDivS
        | OpCode.arith Arith.remui =>
          applyBinary pessimisticUpdates operands transferArithRemUI
        | OpCode.llvm Llvm.urem =>
          applyBinary pessimisticUpdates operands transferLLVMURem
        | OpCode.comb Comb.modu =>
          applyBinary pessimisticUpdates operands transferCombModU
        | OpCode.arith Arith.remsi =>
          applyBinary pessimisticUpdates operands transferArithRemSI
        | OpCode.llvm Llvm.srem =>
          applyBinary pessimisticUpdates operands transferLLVMSRem
        | OpCode.comb Comb.mods =>
          applyBinary pessimisticUpdates operands transferCombModS
        | OpCode.arith Arith.extui =>
          let props := op.getProperties! irCtx.raw (OpCode.arith Arith.extui)
          applyUnary pessimisticUpdates operands <| transferArithExtUI resultWidth props.nneg
        | OpCode.llvm Llvm.zext =>
          let props := op.getProperties! irCtx.raw (OpCode.llvm Llvm.zext)
          applyUnary pessimisticUpdates operands <| transferLLVMZExt resultWidth props.nneg
        | OpCode.arith Arith.extsi =>
          applyUnary pessimisticUpdates operands <| transferArithExtSI resultWidth
        | OpCode.llvm Llvm.sext =>
          applyUnary pessimisticUpdates operands <| transferLLVMSExt resultWidth
        | OpCode.arith Arith.trunci =>
          applyUnary pessimisticUpdates operands <| transferArithTruncI resultWidth
        | OpCode.llvm Llvm.trunc =>
          applyUnary pessimisticUpdates operands <| transferLLVMTrunc resultWidth
        | OpCode.arith Arith.cmpi =>
          let props := op.getProperties! irCtx.raw (OpCode.arith Arith.cmpi)
          applyBinary pessimisticUpdates operands <| transferArithCmpI props.predicate
        | OpCode.llvm Llvm.icmp =>
          let props := op.getProperties! irCtx.raw (OpCode.llvm Llvm.icmp)
          applyBinary pessimisticUpdates operands <| transferLLVMICmp props.predicate
        | OpCode.comb Comb.icmp =>
          let props := op.getProperties! irCtx.raw (OpCode.comb Comb.icmp)
          match Data.LLVM.IntPred.fromNat props.predicate.value.toNat with
          | some predicate =>
            applyBinary pessimisticUpdates operands <| transferCombICmp predicate
          | none => pessimisticUpdates
        | OpCode.arith Arith.select =>
          applyTernary pessimisticUpdates operands transferArithSelect
        | OpCode.llvm Llvm.select =>
          applyTernary pessimisticUpdates operands transferLLVMSelect
        | OpCode.comb Comb.mux =>
          applyTernary pessimisticUpdates operands transferCombMux
        | OpCode.arith Arith.maxui =>
          applyBinary pessimisticUpdates operands transferArithMaxUI
        | OpCode.llvm Llvm.intr__umax =>
          applyBinary pessimisticUpdates operands transferLLVMUMax
        | OpCode.arith Arith.minui =>
          applyBinary pessimisticUpdates operands transferArithMinUI
        | OpCode.llvm Llvm.intr__umin =>
          applyBinary pessimisticUpdates operands transferLLVMUMin
        | OpCode.arith Arith.maxsi =>
          applyBinary pessimisticUpdates operands transferArithMaxSI
        | OpCode.llvm Llvm.intr__smax =>
          applyBinary pessimisticUpdates operands transferLLVMSMax
        | OpCode.arith Arith.minsi =>
          applyBinary pessimisticUpdates operands transferArithMinSI
        | OpCode.llvm Llvm.intr__smin =>
          applyBinary pessimisticUpdates operands transferLLVMSMin
        | OpCode.comb Comb.concat =>
          applyVariadic pessimisticUpdates operands transferCombConcat
        | OpCode.comb Comb.extract =>
          let props := op.getProperties! irCtx.raw (OpCode.comb Comb.extract)
          applyUnary pessimisticUpdates operands <|
            transferCombExtract props.lowBit.value.toNat resultWidth
        | OpCode.comb Comb.reverse =>
          applyUnary pessimisticUpdates operands transferCombReverse
        | OpCode.llvm Llvm.intr__bitreverse =>
          applyUnary pessimisticUpdates operands transferLLVMBitReverse
        | OpCode.comb Comb.replicate =>
          applyUnary pessimisticUpdates operands <| transferCombReplicate resultWidth
        | OpCode.llvm Llvm.intr__bswap =>
          applyUnary pessimisticUpdates operands transferLLVMByteSwap
        | OpCode.llvm Llvm.intr__fshl =>
          applyTernary pessimisticUpdates operands transferLLVMFShL
        | OpCode.llvm Llvm.intr__fshr =>
          applyTernary pessimisticUpdates operands transferLLVMFShR
        | OpCode.llvm Llvm.intr__ctpop =>
          applyUnary pessimisticUpdates operands transferLLVMCountPopulation
        | OpCode.llvm Llvm.intr__ctlz =>
          let props := op.getProperties! irCtx.raw (OpCode.llvm Llvm.intr__ctlz)
          applyUnary pessimisticUpdates operands <|
            transferLLVMCountLeadingZeros props.is_zero_poison
        | OpCode.llvm Llvm.intr__cttz =>
          let props := op.getProperties! irCtx.raw (OpCode.llvm Llvm.intr__cttz)
          applyUnary pessimisticUpdates operands <|
            transferLLVMCountTrailingZeros props.is_zero_poison
        | OpCode.llvm Llvm.intr__abs =>
          let props := op.getProperties! irCtx.raw (OpCode.llvm Llvm.intr__abs)
          applyUnary pessimisticUpdates operands <|
            transferLLVMAbs props.is_int_min_poison
        | OpCode.llvm Llvm.intr__uadd__sat =>
          applyBinary pessimisticUpdates operands transferLLVMUAddSat
        | OpCode.llvm Llvm.intr__usub__sat =>
          applyBinary pessimisticUpdates operands transferLLVMUSubSat
        | OpCode.llvm Llvm.intr__sadd__sat =>
          applyBinary pessimisticUpdates operands transferLLVMSAddSat
        | OpCode.llvm Llvm.intr__ssub__sat =>
          applyBinary pessimisticUpdates operands transferLLVMSSubSat
        | _ => pessimisticUpdates

end KnownBitsAnalysis

/-- Sparse forward known bits analysis for fixed-width integer SSA values. -/
def KnownBitsAnalysis : DataFlowAnalysis :=
  SparseForwardDataFlowAnalysis.new
    .knownBits
    .knownBits
    KnownBitsAnalysis.transfer
    (entryState := fun value irCtx =>
      match (value.getType! irCtx.raw).val with
      | .integerType intType => .unknown intType.bitwidth
      | _ => ⊥)

end Veir
