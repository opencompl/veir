module

public import Veir.PatternRewriter.Puddle.Definitions
public import Veir.PatternRewriter.Basic
public import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution
import Veir.Interfaces.ControlFlowInterfaces

/-!
# Legalization Actions

This file implements the legalization actions as Puddle patterns.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/include/llvm/CodeGen/GlobalISel/LegalizerHelper.h
-/

namespace Veir

open Puddle

public section

/-- Create a `g_constant` of `type` whose value `value` computes from the metadata `inputs`. -/
def createConstantWith {Inputs : Type} [IsMetadataTuple OpCode Inputs]
    (type : Handle OpCode .type) (inputs : Inputs)
    (value : MetadataValues OpCode Inputs → Int) : CreateProg.Builder CreatedOpHandle := do
  let props ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.gmir .g_constant)))
      (type, inputs) fun (type, inputs) => do
        let .integerType type := type.val | none
        return { value := .ofInt (value inputs) type }
  CreateProg.operation (.gmir .g_constant) #[] #[type] props

/-- Create a `g_constant` of `type` with the value `value`. -/
def createConstant (type : Handle OpCode .type) (value : Int) :
    CreateProg.Builder CreatedOpHandle :=
  createConstantWith type () fun () => value

end

/--
Widens type group `typeIdx` of `opcode` to `width` bits. Its operands are extended with `extOpcode`
and its results are truncated back, as in LLVM's `LegalizerHelper::widenScalar`.
-/
def widenTypeGroup (opcode : GMIR) (typeIdx : TypeGroup) (extOpcode : GMIR) (width : Nat)
    (updateProps : propertiesOf (OpCode.gmir opcode) → propertiesOf (OpCode.gmir opcode) := id) :
    Pattern OpCode :=
  let info := opcode.genericOpInfo
  let matchType (group : TypeGroup) : MatchProg.Builder (Handle OpCode .type) :=
    -- The verifier rejects `i0`, at which `g_icmp` yields an `i1` that is not its result type.
    if group = typeIdx then
      MatchProg.type (Attr := IntegerType) fun t => 0 < t.bitwidth && t.bitwidth < width
    else MatchProg.type (Attr := TypeAttr)
  Pattern.Builder
    (do
      /- One type per type group, as in LLVM's type indices: a match whose operands and results of
      a group have different types would be rewritten wrongly, as the operation computes at the
      width of its operands but the rewrite truncates to the type of each result. -/
      let groups := (info.inOperandList ++ info.outOperandList).foldl
        (fun groups group => if groups.contains group then groups else groups.push group) #[]
      let types ← groups.mapM fun group => do return (group, ← matchType group)
      let typeOf (group : TypeGroup) : Handle OpCode .type :=
        ((types.find? (·.1 == group)).map (·.2)).getD default
      let operands ← info.inOperandList.mapM fun group => MatchProg.value (typeOf group)
      let resultTypes := info.outOperandList.map typeOf
      let root ← MatchProg.root (.gmir opcode) operands resultTypes
      return (operands, resultTypes, root.properties))
    (fun (operands, resultTypes, props) => do
      let wideType ← CreateProg.type (IntegerType.signless width)
      let wideOperands ← (info.inOperandList.zip operands).mapM fun (group, operand) => do
        if group ≠ typeIdx then return operand
        let ext ← CreateProg.operation (.gmir extOpcode) #[operand] #[wideType]
        return ext.res[0]!
      let wideResultTypes := (info.outOperandList.zip resultTypes).map fun (group, type) =>
        if group = typeIdx then wideType else type
      let wideProps ← CreateProg.applyNative props (some <| updateProps ·)
      let wide ← CreateProg.operation (.gmir opcode) wideOperands wideResultTypes (.inr wideProps)
      (info.outOperandList.zip (resultTypes.zip wide.res)).mapM fun (group, type, result) => do
        if group ≠ typeIdx then return result
        let trunc ← CreateProg.operation (.gmir .g_trunc) #[result] #[type]
        return trunc.res[0]!)
    (fun results => results)

/-- Clears the no-wrap flags, which no longer hold once the high bits are unconstrained. -/
-- NOTE: (for reviewers) we could also default construct to clear.
def clearNswNuwProperties (props : NswNuwProperties) : NswNuwProperties :=
  { props with nsw := false, nuw := false }

/-- Clears the disjoint flag, which no longer holds once the high bits are unconstrained. -/
def clearDisjointProperties (props : DisjointProperties) : DisjointProperties :=
  { props with disjoint := false }

/-- Widens `g_constant` to `width` bits and then truncates it back, extending the value as LLVM's
`LegalizerInfo::getExtOpcodeForWideningConstant` does. -/
def widenConstant (width : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth < width)
      let root ← MatchProg.root (.gmir .g_constant) #[] #[type]
      -- The value is read at the width of its attribute, which the verifier ties to the result.
      MatchProg.matchNative (type, root.properties) fun (type, props) =>
        match type.val with
        | .integerType type => props.value.type.bitwidth == type.bitwidth
        | _ => false
      return (type, root))
    (fun (type, root) => do
      let wideType ← CreateProg.type (IntegerType.signless width)
      let props ← CreateProg.applyNative root.properties fun ⟨⟨value, ⟨w, _⟩⟩⟩ =>
        let value := if w % 8 = 0 then value else (BitVec.ofInt w value).toNat
        some (GMIRConstantProperties.mk (.ofInt value (.signless width)))
      let wide ← CreateProg.operation (.gmir .g_constant) #[] #[wideType] (.inr props)
      CreateProg.operation (.gmir .g_trunc) #[wide.res[0]!] #[type])
    (fun trunc => trunc)

/-- Matches the unary `opcode` with an operand of type `srcType` and a result of type `resType`,
whose widths satisfy `srcWidth` and `resWidth`. -/
private def matchUnary (opcode : GMIR) (srcWidth resWidth : Nat → Bool := fun _ => true) :
    MatchProg.Builder (Handle OpCode .type × Handle OpCode .type × Handle OpCode .value) := do
  let srcType ← MatchProg.type (Attr := IntegerType) (srcWidth ·.bitwidth)
  let resType ← MatchProg.type (Attr := IntegerType) (resWidth ·.bitwidth)
  let src ← MatchProg.value srcType
  let _ ← MatchProg.root (.gmir opcode) #[src] #[resType]
  return (srcType, resType, src)

/-- Creates the `g_constant` `value srcWidth` of type `type`, where `srcWidth` is the width of the
integer type `srcType`. -/
private def widthConstant (srcType type : Handle OpCode .type) (value : Nat → Int) :
    CreateProg.Builder CreatedOpHandle :=
  createConstantWith type srcType fun srcType => value (srcType.cast? IntegerType).get!.bitwidth

/--
Widens the operand of `g_ctlz` to `width` bits. The operand is zero-extended, so the count is too
large by the number of added bits, which are subtracted from it, as in LLVM's
`LegalizerHelper::widenScalar`. The result must already be `width` bits wide, which the rules
ensure by widening it first.
-/
def widenCtlzSrc (width : Nat) : Pattern OpCode :=
  Pattern.Builder
    (matchUnary .g_ctlz (· < width) (· = width))
    (fun (srcType, resType, src) => do
      let ext ← CreateProg.operation (.gmir .g_zext) #[src] #[resType]
      let ctlz ← CreateProg.operation (.gmir .g_ctlz) #[ext.res[0]!] #[resType]
      let diff ← widthConstant srcType resType (width - ·)
      -- The count of the wide operand is at least `diff`, so the subtraction does not wrap.
      let subProps ← CreateProg.property (.gmir .g_sub) (NswNuwProperties.mk false true)
      CreateProg.operation (.gmir .g_sub) #[ctlz.res[0]!, diff.res[0]!] #[resType] subProps)
    (fun op => op)

/--
Widens the operand of `g_cttz` to `width` bits. The bit just above the operand is set, so that
the count of a zero operand is still its width, as in LLVM's `LegalizerHelper::widenScalar`. The
wide operand is never zero, so it is counted with `g_cttz_zero_poison`, as in LLVM. The result
must already be `width` bits wide, which the rules ensure by widening it first.
-/
def widenCttzSrc (width : Nat) : Pattern OpCode :=
  Pattern.Builder
    (matchUnary .g_cttz (· < width) (· = width))
    (fun (srcType, resType, src) => do
      let ext ← CreateProg.operation (.gmir .g_anyext) #[src] #[resType]
      let topBit ← widthConstant srcType resType (2 ^ ·)
      let wideSrc ← CreateProg.operation (.gmir .g_or) #[ext.res[0]!, topBit.res[0]!] #[resType]
      CreateProg.operation (.gmir .g_cttz_zero_poison) #[wideSrc.res[0]!] #[resType])
    (fun op => op)

/--
Widens `g_bswap` or `g_bitreverse` to `width` bits. The reversed operand ends up in the high
bits, so it is shifted back down before it is truncated, as in LLVM's `LegalizerHelper::widenScalar`.
-/
def widenReverse (opcode : GMIR) (width : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      -- The verifier rejects `i0`, at which the shift down by the whole wide width is poison.
      let type ← MatchProg.type (Attr := IntegerType) fun t => 0 < t.bitwidth && t.bitwidth < width
      let src ← MatchProg.value type
      let _ ← MatchProg.root (.gmir opcode) #[src] #[type]
      return (type, src))
    (fun (type, src) => do
      let wideType ← CreateProg.type (IntegerType.signless width)
      let ext ← CreateProg.operation (.gmir .g_anyext) #[src] #[wideType]
      let wide ← CreateProg.operation (.gmir opcode) #[ext.res[0]!] #[wideType]
      let diff ← widthConstant type wideType (width - ·)
      let shift ← CreateProg.operation (.gmir .g_lshr) #[wide.res[0]!, diff.res[0]!] #[wideType]
      CreateProg.operation (.gmir .g_trunc) #[shift.res[0]!] #[type])
    (fun op => op)

/-- Lowers the count `opcode`, whose zero input is poison, to the count `defined`, which is defined
at zero and refines it, as in LLVM's `LegalizerHelper::lowerBitCount`. -/
def lowerZeroPoisonCount (opcode defined : GMIR) : Pattern OpCode :=
  Pattern.Builder
    (matchUnary opcode)
    (fun (_, resType, src) => CreateProg.operation (.gmir defined) #[src] #[resType])
    (fun op => op)

/-- Lowers `g_sext` to a `g_anyext` followed by a `g_sext_inreg` of the source width, which is what
LLVM's artifact combiner makes of a `g_sext` of a `g_trunc`. The source width is passed as a 64-bit
size, so it must fit one. -/
def lowerSext : Pattern OpCode :=
  Pattern.Builder
    (matchUnary .g_sext (srcWidth := (· < 2 ^ 64)))
    (fun (srcType, resType, src) => do
      let extProps ← CreateProg.property (.gmir .g_anyext) default
      let ext ← CreateProg.operation (.gmir .g_anyext) #[src] #[resType] extProps
      let props ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.gmir .g_sext_inreg)))
          srcType fun type => match type.val with
            | .integerType type => some (SextInRegProperties.mk (BitVec.ofNat 64 type.bitwidth))
            | _ => none
      CreateProg.operation (.gmir .g_sext_inreg) #[ext.res[0]!] #[resType] props)
    (fun op => op)

/-- Lowers `g_zext` to a `g_anyext` followed by a `g_and` with the mask of the source width, which
is what LLVM's artifact combiner makes of a `g_zext` of a `g_trunc`. -/
def lowerZext : Pattern OpCode :=
  Pattern.Builder
    (matchUnary .g_zext)
    (fun (srcType, resType, src) => do
      let ext ← CreateProg.operation (.gmir .g_anyext) #[src] #[resType]
      let mask ← widthConstant srcType resType (2 ^ · - 1)
      CreateProg.operation (.gmir .g_and) #[ext.res[0]!, mask.res[0]!] #[resType])
    (fun op => op)

/--
Widens the condition of `g_brcond` to `width` bits with a `g_zext`, which is what LLVM's
`LegalizerHelper::widenScalar` extends it with on a target whose booleans are 0 or 1, as on RISC-V.
`g_brcond` forwards a variable number of operands to its successors, which a Puddle pattern cannot
match, so this is a local rewrite.
-/
def widenBrcondCondition (width : Nat) : LocalRewritePattern OpCode := fun ctx op => do
  -- Read `ctx` before creating operations: any later read makes the first one copy the context.
  let operands := op.getOperands! ctx.raw
  let successors := op.getSuccessors! ctx.raw
  let props := op.getProperties! ctx.raw GMIR.g_brcond
  let .integerType type := (operands[0]!.getType! ctx.raw).val | return (ctx, none)
  if width ≤ type.bitwidth then return (ctx, none)
  let (ctx, ext) ← WfRewriter.createOp! ctx GMIR.g_zext #[IntegerType.signless width]
    #[operands[0]!] #[] #[] (NnegProperties.mk false) none
  let (ctx, branch) ← WfRewriter.createOp! ctx GMIR.g_brcond #[]
    (#[ValuePtr.opResult (ext.getResult 0)] ++ operands.extract 1) successors #[] props none
  return (ctx, some (#[ext, branch], #[]))

/--
Lowers the `w`-bit funnel shift `g_fshl` (`isLeft`) or `g_fshr` to shifts, as the generic case of
LLVM's `LegalizerHelper::lowerFunnelShiftAsShifts`:

  fshl x y z = (x << (z % w)) | ((y >> 1) >> (w - 1 - z % w))
  fshr x y z = ((x << 1) << (w - 1 - z % w)) | (y >> (z % w))

Splitting the shift of the other operand into a shift by one and one by `w - 1 - z % w` keeps both
amounts below `w`. The amount computation is done in the amount's type, which must be at least `w`
bits wide so that `w` fits in it; the rules ensure this by widening the amount first.
-/
def lowerFunnelShift (isLeft : Bool) : Pattern OpCode :=
  let opcode : GMIR := if isLeft then .g_fshl else .g_fshr
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let amtType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let z ← MatchProg.value amtType
      let _ ← MatchProg.root (.gmir opcode) #[x, y, z] #[type]
      return (type, amtType, x, y, z))
    (fun (type, amtType, x, y, z) => do
      let width ← widthConstant type amtType (·)
      let widthMinusOne ← widthConstant type amtType (· - 1)
      let one ← createConstant amtType 1
      let amt ← CreateProg.operation (.gmir .g_urem) #[z, width.res[0]!] #[amtType]
      let invAmt ← CreateProg.operation (.gmir .g_sub)
        #[widthMinusOne.res[0]!, amt.res[0]!] #[amtType]
      let (shX, shY) ← if isLeft then do
          let shX ← CreateProg.operation (.gmir .g_shl) #[x, amt.res[0]!] #[type]
          let y1 ← CreateProg.operation (.gmir .g_lshr) #[y, one.res[0]!] #[type]
          let shY ← CreateProg.operation (.gmir .g_lshr) #[y1.res[0]!, invAmt.res[0]!] #[type]
          pure (shX, shY)
        else do
          let x1 ← CreateProg.operation (.gmir .g_shl) #[x, one.res[0]!] #[type]
          let shX ← CreateProg.operation (.gmir .g_shl) #[x1.res[0]!, invAmt.res[0]!] #[type]
          let shY ← CreateProg.operation (.gmir .g_lshr) #[y, amt.res[0]!] #[type]
          pure (shX, shY)
      CreateProg.operation (.gmir .g_or) #[shX.res[0]!, shY.res[0]!] #[type])
    (fun op => op)

/--
Lowers the saturating `opcode`, a signed (`isSigned`) or unsigned addition (`isAdd`) or
subtraction, to min and max operations, as LLVM's `LegalizerHelper::lowerAddSubSatToMinMax`:

  uadd.sat a b = a + umin (~a) b
  usub.sat a b = a - umin a b
  sadd.sat a b = a + smin (smax (INT_MIN - smin a 0) b) (INT_MAX - smax a 0)
  ssub.sat a b = a - smin (smax (smax a (-1) - INT_MAX) b) (smin a (-1) - INT_MIN)

The operations are created in the same order as in LLVM.
-/
def lowerAddSubSatToMinMax (opcode : GMIR) (isSigned isAdd : Bool) : Pattern OpCode :=
  let baseOp : GMIR := if isAdd then .g_add else .g_sub
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let lhs ← MatchProg.value type
      let rhs ← MatchProg.value type
      let _ ← MatchProg.root (.gmir opcode) #[lhs, rhs] #[type]
      return (type, lhs, rhs))
    (fun (type, lhs, rhs) => do
      if isSigned then
        let maxVal ← widthConstant type type fun w => 2 ^ (w - 1) - 1
        let minVal ← widthConstant type type fun w => -2 ^ (w - 1)
        let (lo, hi) ← if isAdd then do
            let zero ← createConstant type 0
            let smax ← CreateProg.operation (.gmir .g_smax) #[lhs, zero.res[0]!] #[type]
            let hi ← CreateProg.operation (.gmir .g_sub) #[maxVal.res[0]!, smax.res[0]!] #[type]
            let smin ← CreateProg.operation (.gmir .g_smin) #[lhs, zero.res[0]!] #[type]
            let lo ← CreateProg.operation (.gmir .g_sub) #[minVal.res[0]!, smin.res[0]!] #[type]
            pure (lo, hi)
          else do
            let negOne ← createConstant type (-1)
            let smax ← CreateProg.operation (.gmir .g_smax) #[lhs, negOne.res[0]!] #[type]
            let lo ← CreateProg.operation (.gmir .g_sub) #[smax.res[0]!, maxVal.res[0]!] #[type]
            let smin ← CreateProg.operation (.gmir .g_smin) #[lhs, negOne.res[0]!] #[type]
            let hi ← CreateProg.operation (.gmir .g_sub) #[smin.res[0]!, minVal.res[0]!] #[type]
            pure (lo, hi)
        let clamp ← CreateProg.operation (.gmir .g_smax) #[lo.res[0]!, rhs] #[type]
        let rhsClamped ← CreateProg.operation (.gmir .g_smin) #[clamp.res[0]!, hi.res[0]!] #[type]
        CreateProg.operation (.gmir baseOp) #[lhs, rhsClamped.res[0]!] #[type]
      else
        let notLhs ← if isAdd then do
            let allOnes ← createConstant type (-1)
            let not ← CreateProg.operation (.gmir .g_xor) #[lhs, allOnes.res[0]!] #[type]
            pure not.res[0]!
          else pure lhs
        let min ← CreateProg.operation (.gmir .g_umin) #[notLhs, rhs] #[type]
        CreateProg.operation (.gmir baseOp) #[lhs, min.res[0]!] #[type])
    (fun op => op)

/-- Matches the overflowing `opcode`, returning its result type, overflow type and operands. -/
private def matchOverflowing (opcode : GMIR) : MatchProg.Builder
    (Handle OpCode .type × Handle OpCode .type × Handle OpCode .value × Handle OpCode .value) := do
  let type ← MatchProg.type (Attr := IntegerType)
  -- The overflow flag is an `i1`, as the verifier requires; the lowerings compute it with `g_icmp`.
  let ovType ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 1)
  let lhs ← MatchProg.value type
  let rhs ← MatchProg.value type
  let _ ← MatchProg.root (.gmir opcode) #[lhs, rhs] #[type, ovType]
  return (type, ovType, lhs, rhs)

/--
Lowers `g_uaddo` (`isAdd`) or `g_usubo`, as LLVM's `LegalizerHelper::lower`. The sum wraps around
exactly when it is smaller than an operand, and the difference exactly when `lhs <u rhs`:

  uaddo a b = (a + b, a + b <u b)
  usubo a b = (a - b, a <u b)
-/
def lowerUAddSubO (isAdd : Bool) : Pattern OpCode :=
  Pattern.Builder
    (matchOverflowing (if isAdd then .g_uaddo else .g_usubo))
    (fun (type, ovType, lhs, rhs) => do
      let ultProps ← CreateProg.property (.gmir .g_icmp) { predicate := .ult }
      if isAdd then
        let sum ← CreateProg.operation (.gmir .g_add) #[lhs, rhs] #[type]
        let carry ← CreateProg.operation (.gmir .g_icmp) #[sum.res[0]!, rhs] #[ovType] ultProps
        return #[sum.res[0]!, carry.res[0]!]
      else
        let diff ← CreateProg.operation (.gmir .g_sub) #[lhs, rhs] #[type]
        let borrow ← CreateProg.operation (.gmir .g_icmp) #[lhs, rhs] #[ovType] ultProps
        return #[diff.res[0]!, borrow.res[0]!])
    (fun results => results)

/--
Lowers `g_saddo` (`isAdd`) or `g_ssubo`, as LLVM's `LegalizerHelper::lowerSADDO_SSUBO`:

  saddo a b = (a + b, (b <s 0) ^ (a + b <s a))
  ssubo a b = (a - b, (a <s b) ^ (a - b <s 0))

The sum is smaller than `a` exactly when `b` is negative, unless it overflows. The difference is
negative exactly when `a <s b`, unless it overflows. The operations are created in the same order
as in LLVM.
-/
def lowerSAddSubO (isAdd : Bool) : Pattern OpCode :=
  Pattern.Builder
    (matchOverflowing (if isAdd then .g_saddo else .g_ssubo))
    (fun (type, ovType, lhs, rhs) => do
      let res ← CreateProg.operation (.gmir (if isAdd then .g_add else .g_sub)) #[lhs, rhs] #[type]
      let zero ← createConstant type 0
      let sltProps ← CreateProg.property (.gmir .g_icmp) { predicate := .slt }
      let (cmp0, cmp1) ← if isAdd then do
          let resultLowerThanLhs ← CreateProg.operation (.gmir .g_icmp)
            #[res.res[0]!, lhs] #[ovType] sltProps
          let rhsNegative ← CreateProg.operation (.gmir .g_icmp)
            #[rhs, zero.res[0]!] #[ovType] sltProps
          pure (rhsNegative, resultLowerThanLhs)
        else do
          let lhsLessThanRhs ← CreateProg.operation (.gmir .g_icmp) #[lhs, rhs] #[ovType] sltProps
          let resultNegative ← CreateProg.operation (.gmir .g_icmp)
            #[res.res[0]!, zero.res[0]!] #[ovType] sltProps
          pure (lhsLessThanRhs, resultNegative)
      let ov ← CreateProg.operation (.gmir .g_xor) #[cmp0.res[0]!, cmp1.res[0]!] #[ovType]
      return #[res.res[0]!, ov.res[0]!])
    (fun results => results)

/--
Widens the result and operands of the overflowing `opcode` to `width` bits, as LLVM's
`LegalizerHelper::widenScalarAddSubOverflow`. The operands are extended according to the signedness
of `opcode`, and the operation overflows exactly when its wide result does not survive a truncation
and the same extension:

  [su]addo a b = let r := ext a + ext b; (trunc r, r != ext (trunc r))

LLVM builds `trunc r` twice, and its builder deduplicates them (CSE); we build it once.
-/
def widenScalarAddSubOverflow (opcode : GMIR) (width : Nat) : Pattern OpCode :=
  let (baseOp, extOp) : GMIR × GMIR := match opcode with
    | .g_saddo => (.g_add, .g_sext)
    | .g_ssubo => (.g_sub, .g_sext)
    | .g_uaddo => (.g_add, .g_zext)
    | _ => (.g_sub, .g_zext)
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth < width)
      -- The overflow flag is an `i1`, as the verifier requires; it is recomputed with `g_icmp`.
      let ovType ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 1)
      let lhs ← MatchProg.value type
      let rhs ← MatchProg.value type
      let _ ← MatchProg.root (.gmir opcode) #[lhs, rhs] #[type, ovType]
      return (type, ovType, lhs, rhs))
    (fun (type, ovType, lhs, rhs) => do
      let wideType ← CreateProg.type (IntegerType.signless width)
      let lhsExt ← CreateProg.operation (.gmir extOp) #[lhs] #[wideType]
      let rhsExt ← CreateProg.operation (.gmir extOp) #[rhs] #[wideType]
      let newOp ← CreateProg.operation (.gmir baseOp)
        #[lhsExt.res[0]!, rhsExt.res[0]!] #[wideType]
      let trunc ← CreateProg.operation (.gmir .g_trunc) #[newOp.res[0]!] #[type]
      let ext ← CreateProg.operation (.gmir extOp) #[trunc.res[0]!] #[wideType]
      let neProps ← CreateProg.property (.gmir .g_icmp) { predicate := .ne }
      let ov ← CreateProg.operation (.gmir .g_icmp)
        #[newOp.res[0]!, ext.res[0]!] #[ovType] neProps
      return #[trunc.res[0]!, ov.res[0]!])
    (fun results => results)

/--
Lowers `g_uadde` to a `g_add` of the operands, and a `g_add` of the carry-in to that sum, and
`g_usube` to the same with `g_sub`, as LLVM's `LegalizerHelper::lower` does. The first operation
carries when its result is less than either operand (for `g_add`) or greater than the left operand
(for `g_sub`). The second one only carries when the carry-in is set, and the second result (for
`g_add`) or the first result (for `g_sub`) is zero.
-/
def lowerAddSubE (isAdd : Bool) : Pattern OpCode :=
  let (opcode, arithOpcode, predicate) :=
    if isAdd then (GMIR.g_uadde, GMIR.g_add, Data.LLVM.IntPred.ult)
    else (.g_usube, .g_sub, .ugt)
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let flagType ← MatchProg.type (Attr := IntegerType)
      let lhs ← MatchProg.value type
      let rhs ← MatchProg.value type
      let flagIn ← MatchProg.value flagType
      let _ ← MatchProg.root (.gmir opcode) #[lhs, rhs, flagIn] #[type, flagType]
      -- The `i1` carry-in is zero-extended to the type of the operands, so that type must be wider.
      MatchProg.matchNative type fun type =>
        match type.val with
        | .integerType type => 1 < type.bitwidth
        | _ => false
      return (type, flagType, lhs, rhs, flagIn))
    (fun (type, flagType, lhs, rhs, flagIn) => do
      let tmp ← CreateProg.operation (.gmir arithOpcode) #[lhs, rhs] #[type]
      let flag ← CreateProg.operation (.gmir .g_icmp) #[tmp.res[0]!, lhs] #[flagType]
        (.inl { predicate })
      let ext ← CreateProg.operation (.gmir .g_zext) #[flagIn] #[type]
      let result ← CreateProg.operation (.gmir arithOpcode) #[tmp.res[0]!, ext.res[0]!] #[type]
      let zero ← createConstant type 0
      let zeroOperand := if isAdd then result.res[0]! else tmp.res[0]!
      let isZero ← CreateProg.operation (.gmir .g_icmp) #[zeroOperand, zero.res[0]!] #[flagType]
        (.inl { predicate := .eq })
      let flag2 ← CreateProg.operation (.gmir .g_and) #[isZero.res[0]!, flagIn] #[flagType]
      let flagOut ← CreateProg.operation (.gmir .g_or) #[flag.res[0]!, flag2.res[0]!] #[flagType]
      return #[result.res[0]!, flagOut.res[0]!])
    (fun results => results)

/--
Narrows a `2 * width`-bit `g_add` to a `g_uaddo` of the low halves and a `g_uadde` of the high
halves, and `g_sub` to the same with `g_usubo` and `g_usube`, as LLVM's
`LegalizerHelper::narrowScalarAddSub` does.
-/
def narrowAddSub (isAdd : Bool) (width : Nat) : Pattern OpCode :=
  let (opcode, loOpcode, hiOpcode) :=
    if isAdd then (GMIR.g_add, GMIR.g_uaddo, GMIR.g_uadde) else (.g_sub, .g_usubo, .g_usube)
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 2 * width)
      let lhs ← MatchProg.value type
      let rhs ← MatchProg.value type
      let _ ← MatchProg.root (.gmir opcode) #[lhs, rhs] #[type]
      return (type, lhs, rhs))
    (fun (type, lhs, rhs) => do
      let halfType ← CreateProg.type (IntegerType.signless width)
      let carryType ← CreateProg.type (IntegerType.signless 1)
      let lhsHalves ← CreateProg.operation (.gmir .g_unmerge_values) #[lhs] #[halfType, halfType]
      let rhsHalves ← CreateProg.operation (.gmir .g_unmerge_values) #[rhs] #[halfType, halfType]
      let lo ← CreateProg.operation (.gmir loOpcode) #[lhsHalves.res[0]!, rhsHalves.res[0]!]
        #[halfType, carryType]
      let hi ← CreateProg.operation (.gmir hiOpcode)
        #[lhsHalves.res[1]!, rhsHalves.res[1]!, lo.res[1]!] #[halfType, carryType]
      CreateProg.operation (.gmir .g_merge_values) #[lo.res[0]!, hi.res[0]!] #[type])
    (fun merge => merge)

public section

/--
Lowers the saturating `opcode`, a signed (`isSigned`) or unsigned addition (`isAdd`) or
subtraction, to the matching overflowing operation and a `g_select`, as LLVM's
`LegalizerHelper::lowerAddSubSatToAddoSubo`:

  uadd.sat a b = let (r, ov) := uaddo a b; ov ? -1 : r
  usub.sat a b = let (r, ov) := usubo a b; ov ? 0 : r
  sadd.sat a b = let (r, ov) := saddo a b; ov ? (r >>s (w - 1)) + INT_MIN : r
  ssub.sat a b = let (r, ov) := ssubo a b; ov ? (r >>s (w - 1)) + INT_MIN : r

On signed overflow, the wrapped result has the opposite sign of the exact one, so `r >>s (w - 1)`
is `0` when it saturates to `INT_MAX` and `-1` when it saturates to `INT_MIN`.

The operations are created in the same order as in LLVM. LLVM's `lower` picks this lowering when
min and max are not legal, which `lower?` cannot query, so targets use it as a custom legalization
instead.
-/
def lowerAddSubSatToAddoSubo (opcode : GMIR) (isSigned isAdd : Bool) : Pattern OpCode :=
  let overflowOp : GMIR := match isSigned, isAdd with
    | false, true => .g_uaddo
    | true, true => .g_saddo
    | false, false => .g_usubo
    | true, false => .g_ssubo
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let lhs ← MatchProg.value type
      let rhs ← MatchProg.value type
      let _ ← MatchProg.root (.gmir opcode) #[lhs, rhs] #[type]
      return (type, lhs, rhs))
    (fun (type, lhs, rhs) => do
      let boolType ← CreateProg.type (IntegerType.signless 1)
      let overflowRes ← CreateProg.operation (.gmir overflowOp) #[lhs, rhs] #[type, boolType]
      let tmp := overflowRes.res[0]!
      let ov := overflowRes.res[1]!
      let clamp ← if isSigned then do
          let shiftAmount ← widthConstant type type (· - 1)
          let sign ← CreateProg.operation (.gmir .g_ashr) #[tmp, shiftAmount.res[0]!] #[type]
          let minVal ← widthConstant type type fun w => -2 ^ (w - 1)
          CreateProg.operation (.gmir .g_add) #[sign.res[0]!, minVal.res[0]!] #[type]
        else createConstant type (if isAdd then -1 else 0)
      CreateProg.operation (.gmir .g_select) #[ov, clamp.res[0]!, tmp] #[type])
    (fun op => op)

/--
Lowers the saturating left shift `g_sshlsat` (`isSigned`) or `g_ushlsat`, as LLVM's
`LegalizerHelper::lowerShlSat`. The shift overflows if shifting the result back does not give the
shifted value:

  sshl.sat a b = a != (a << b) >>s b ? (a <s 0 ? INT_MIN : INT_MAX) : a << b
  ushl.sat a b = a != (a << b) >>u b ? UINT_MAX : a << b

The operations are created in the same order as in LLVM.
-/
def lowerShlSat (isSigned : Bool) : Pattern OpCode :=
  let opcode : GMIR := if isSigned then .g_sshlsat else .g_ushlsat
  let shiftBack : GMIR := if isSigned then .g_ashr else .g_lshr
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let amtType ← MatchProg.type (Attr := IntegerType)
      let lhs ← MatchProg.value type
      let rhs ← MatchProg.value amtType
      let _ ← MatchProg.root (.gmir opcode) #[lhs, rhs] #[type]
      return (type, lhs, rhs))
    (fun (type, lhs, rhs) => do
      let boolType ← CreateProg.type (IntegerType.signless 1)
      let result ← CreateProg.operation (.gmir .g_shl) #[lhs, rhs] #[type]
      let orig ← CreateProg.operation (.gmir shiftBack) #[result.res[0]!, rhs] #[type]
      let satVal ← if isSigned then do
          let satMin ← widthConstant type type fun w => -2 ^ (w - 1)
          let satMax ← widthConstant type type fun w => 2 ^ (w - 1) - 1
          let zero ← createConstant type 0
          let cmpProps ← CreateProg.property (.gmir .g_icmp) { predicate := .slt }
          let cmp ← CreateProg.operation (.gmir .g_icmp) #[lhs, zero.res[0]!] #[boolType] cmpProps
          CreateProg.operation (.gmir .g_select)
            #[cmp.res[0]!, satMin.res[0]!, satMax.res[0]!] #[type]
        else createConstant type (-1)
      let ovProps ← CreateProg.property (.gmir .g_icmp) { predicate := .ne }
      let ov ← CreateProg.operation (.gmir .g_icmp) #[lhs, orig.res[0]!] #[boolType] ovProps
      CreateProg.operation (.gmir .g_select)
        #[ov.res[0]!, satVal.res[0]!, result.res[0]!] #[type])
    (fun op => op)

/-- The pattern that lowers `opcode`, if it can be lowered. -/
def lower? : GMIR → Option (Pattern OpCode)
  | .g_sext => lowerSext
  -- Unproven (`widthDependent`), so not run:
  -- | .g_fshl => lowerFunnelShift true
  -- | .g_fshr => lowerFunnelShift false
  | .g_zext => lowerZext
  | .g_ctlz_zero_poison => lowerZeroPoisonCount .g_ctlz_zero_poison .g_ctlz
  | .g_cttz_zero_poison => lowerZeroPoisonCount .g_cttz_zero_poison .g_cttz
  | .g_uaddsat => lowerAddSubSatToMinMax .g_uaddsat false true
  | .g_usubsat => lowerAddSubSatToMinMax .g_usubsat false false
  | .g_saddsat => lowerAddSubSatToMinMax .g_saddsat true true
  | .g_ssubsat => lowerAddSubSatToMinMax .g_ssubsat true false
  | .g_sshlsat => lowerShlSat true
  | .g_ushlsat => lowerShlSat false
  | .g_uaddo => lowerUAddSubO true
  | .g_usubo => lowerUAddSubO false
  | .g_saddo => lowerSAddSubO true
  | .g_ssubo => lowerSAddSubO false
  | .g_uadde => lowerAddSubE true
  | .g_usube => lowerAddSubE false
  | _ => none

/-- The Puddle pattern that widens type group `typeIdx` of `opcode` to `width` bits, if any. -/
def widenScalarPattern? : GMIR → (typeIdx : TypeGroup) → (width : Nat) → Option (Pattern OpCode)
  -- The high bits of the operands never reach the low bits of the result, so any extension is
  -- fine.
  | .g_add, .type 0, width => widenTypeGroup .g_add (.type 0) .g_anyext width clearNswNuwProperties
  | .g_sub, .type 0, width => widenTypeGroup .g_sub (.type 0) .g_anyext width clearNswNuwProperties
  -- The result has no operands in its group, so `g_anyext` is not used.
  | .g_icmp, .type 0, width => widenTypeGroup .g_icmp (.type 0) .g_anyext width
  -- The high bits matter for the comparison, and sign extension preserves both the signed and
  -- the unsigned order.
  | .g_icmp, .type 1, width => widenTypeGroup .g_icmp (.type 1) .g_sext width
  -- The high bits of the selected values never reach the low bits of the result.
  | .g_select, .type 0, width => widenTypeGroup .g_select (.type 0) .g_anyext width
  -- The condition is true when it is nonzero, so its high bits must be zero, as with LLVM's
  -- `getBoolExtOp` on a target whose booleans are zero or one.
  | .g_select, .type 1, width => widenTypeGroup .g_select (.type 1) .g_zext width
  -- As for `g_add`, the high bits of the shifted value never reach the low bits of the result.
  | .g_shl, .type 0, width => widenTypeGroup .g_shl (.type 0) .g_anyext width clearNswNuwProperties
  -- `ashr` shifts copies of the sign bit into the result, so the high bits must be sign bits.
  | .g_ashr, .type 0, width => widenTypeGroup .g_ashr (.type 0) .g_sext width
  -- `lshr` shifts zeros into the result, so the high bits must be zero.
  | .g_lshr, .type 0, width => widenTypeGroup .g_lshr (.type 0) .g_zext width
  -- The amount is an unsigned number of bits, so its value must be kept as such.
  | .g_shl, .type 1, width => widenTypeGroup .g_shl (.type 1) .g_zext width
  | .g_ashr, .type 1, width => widenTypeGroup .g_ashr (.type 1) .g_zext width
  | .g_lshr, .type 1, width => widenTypeGroup .g_lshr (.type 1) .g_zext width
  | .g_and, .type 0, width => widenTypeGroup .g_and (.type 0) .g_anyext width
  | .g_or, .type 0, width => widenTypeGroup .g_or (.type 0) .g_anyext width clearDisjointProperties
  | .g_xor, .type 0, width => widenTypeGroup .g_xor (.type 0) .g_anyext width
  | .g_mul, .type 0, width => widenTypeGroup .g_mul (.type 0) .g_anyext width clearNswNuwProperties
  -- The high bits matter for division and remainder, so the operands are extended according to
  -- the signedness of the operation. Exactness is preserved by both extensions.
  | .g_sdiv, .type 0, width => widenTypeGroup .g_sdiv (.type 0) .g_sext width
  | .g_srem, .type 0, width => widenTypeGroup .g_srem (.type 0) .g_sext width
  | .g_udiv, .type 0, width => widenTypeGroup .g_udiv (.type 0) .g_zext width
  | .g_urem, .type 0, width => widenTypeGroup .g_urem (.type 0) .g_zext width
  | .g_constant, .type 0, width => widenConstant width
  -- A wide poison truncates to poison.
  | .g_poison, .type 0, width => widenTypeGroup .g_poison (.type 0) .g_anyext width
  -- The memory size is kept, so the wide load is any-extended.
  | .g_load, .type 0, width => widenTypeGroup .g_load (.type 0) .g_anyext width
  -- `g_sext_inreg` only reads the low `sz` bits, so any extension is fine.
  | .g_sext_inreg, .type 0, width => widenTypeGroup .g_sext_inreg (.type 0) .g_anyext width
  -- The count fits in the wide result, so the result is just truncated back.
  | .g_ctlz, .type 0, width => widenTypeGroup .g_ctlz (.type 0) .g_anyext width
  | .g_cttz, .type 0, width => widenTypeGroup .g_cttz (.type 0) .g_anyext width
  | .g_ctpop, .type 0, width => widenTypeGroup .g_ctpop (.type 0) .g_anyext width
  | .g_ctlz, .type 1, width => widenCtlzSrc width
  | .g_cttz, .type 1, width => widenCttzSrc width
  -- Zero bits do not add to the count.
  | .g_ctpop, .type 1, width => widenTypeGroup .g_ctpop (.type 1) .g_zext width
  -- `g_bswap` is only defined at the widths 16, 32 and 64, so it is only widened to those
  -- (`widen_bswap_0_valid`).
  | .g_bswap, .type 0, width =>
    if width = 16 ∨ width = 32 ∨ width = 64 then some (widenReverse .g_bswap width) else none
  | .g_bitreverse, .type 0, width => widenReverse .g_bitreverse width
  -- Sign extension preserves the signed order, and also the unsigned order. For `g_umin` and
  -- `g_umax`, LLVM only sign-extends where it is cheaper than zero-extending (from `i32` on
  -- RISC-V), but both are correct.
  | .g_smin, .type 0, width => widenTypeGroup .g_smin (.type 0) .g_sext width
  | .g_smax, .type 0, width => widenTypeGroup .g_smax (.type 0) .g_sext width
  | .g_umin, .type 0, width => widenTypeGroup .g_umin (.type 0) .g_sext width
  | .g_umax, .type 0, width => widenTypeGroup .g_umax (.type 0) .g_sext width
  | .g_abs, .type 0, width => widenTypeGroup .g_abs (.type 0) .g_sext width
  -- The amount is an unsigned number of bits, so its value must be kept as such.
  | .g_fshl, .type 1, width => widenTypeGroup .g_fshl (.type 1) .g_zext width
  | .g_fshr, .type 1, width => widenTypeGroup .g_fshr (.type 1) .g_zext width
  | .g_uaddo, .type 0, width => widenScalarAddSubOverflow .g_uaddo width
  | .g_usubo, .type 0, width => widenScalarAddSubOverflow .g_usubo width
  | .g_saddo, .type 0, width => widenScalarAddSubOverflow .g_saddo width
  | .g_ssubo, .type 0, width => widenScalarAddSubOverflow .g_ssubo width
  | _, _, _ => none

/-- Widens type group `typeIdx` of `opcode` to `width` bits. -/
def widenScalar? : GMIR → (typeIdx : TypeGroup) → (width : Nat) →
    Option (LocalRewritePattern OpCode)
  -- `widenBrcondCondition` is unproven, so not run:
  -- | .g_brcond, .type 0, width => widenBrcondCondition width
  | opcode, typeIdx, width => (widenScalarPattern? opcode typeIdx width).map Puddle.Pattern.interpret

/-- Narrows type group `typeIdx` of `opcode` to `width` bits. -/
def narrowScalar? : GMIR → (typeIdx : TypeGroup) → (width : Nat) → Option (Pattern OpCode)
  | .g_add, .type 0, width => narrowAddSub true width
  | .g_sub, .type 0, width => narrowAddSub false width
  | _, _, _ => none

/-! ## Block arguments

  The block arguments are the phis of our gMIR MLIR-dialect, so they are legalized with the target's
  block-argument rules. A Puddle pattern cannot match a block argument and its predecessors,
  so these are local rewrites. -/

/-- The uses of `block` as a successor, one for each edge into it. -/
private def incomingEdges (ctx : IRContext OpCode) (block : BlockPtr) : List BlockOperandPtr :=
  Id.run do
    let mut edges := []
    let mut use? := block.getFirstUse! ctx
    while let some use := use? do
      edges := use :: edges
      use? := use.getNextUse! ctx
    return edges.reverse

/--
Widens argument `i` of `block` to `width` bits for each `(i, width)` in `args`, as LLVM does for
`G_PHI`: each branch to `block` passes a `g_anyext`, and a `g_trunc` restores the original type.
Returns `none` if a predecessor is not a branch.
-/
def widenBlockArguments (block : BlockPtr) (args : List (Nat × Nat))
    (ctx : WfIRContext OpCode) : Option (WfIRContext OpCode) := do
  let edges ← (incomingEdges ctx.raw block).mapM fun edge =>
    return (edge.op, ← BranchOpInterface.getSuccessorOperands? edge.op edge.index ctx.raw)
  -- The `g_trunc`s go first: a branch from the block back to itself passes a `g_anyext` of one.
  let start := InsertPoint.atStart! block ctx.raw
  let ctx ← args.foldlM (init := ctx) fun ctx (i, width) => do
    let arg : BlockArgumentPtr := { block := block, index := i }
    let type := (ValuePtr.blockArgument arg).getType! ctx.raw
    let ctx := WfRewriter.setType! ctx arg (IntegerType.signless width)
    let (ctx, trunc) ← WfRewriter.createOp! ctx GMIR.g_trunc #[type] #[] #[] #[]
      (({ nsw := false, nuw := false } : NswNuwProperties) : propertiesOf GMIR.g_trunc) start
    let ctx := WfRewriter.replaceValue! ctx arg (trunc.getResult 0)
    return WfRewriter.pushOperand! ctx trunc arg
  edges.foldlM (init := ctx) fun ctx (branch, operands) => args.foldlM (init := ctx)
    fun ctx (i, width) => do
      let operand : OpOperandPtr := { op := branch, index := operands.getOperandIndex i }
      let (ctx, ext) ← WfRewriter.createOp! ctx GMIR.g_anyext #[IntegerType.signless width]
        #[branch.getOperand! ctx.raw operand.index] #[] #[] () (InsertPoint.before branch)
      return WfRewriter.replaceOperand! ctx operand (ext.getResult 0)

end

end Veir
