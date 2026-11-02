module

public import Veir.PatternRewriter.Puddle.Definitions
public import Veir.Passes.Legalization.LegalizerInfo
public import Veir.PatternRewriter.Basic
public import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution

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
    if group = typeIdx then MatchProg.type (Attr := IntegerType) (·.bitwidth < width)
    else MatchProg.type (Attr := TypeAttr)
  Pattern.Builder
    (do
      let operands ← info.inOperandList.mapM fun group => do MatchProg.value (← matchType group)
      let resultTypes ← info.outOperandList.mapM matchType
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
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth < width)
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
LLVM's artifact combiner makes of a `g_sext` of a `g_trunc`. -/
def lowerSext : Pattern OpCode :=
  Pattern.Builder
    (matchUnary .g_sext)
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

/-- The smallest signed value of `width` bits. -/
private def intMin (width : Nat) : Int := -2 ^ (width - 1)

/-- The largest signed value of `width` bits. -/
private def intMax (width : Nat) : Int := 2 ^ (width - 1) - 1

/-- Creates the `g_icmp` `predicate lhs rhs` with result type `type`. -/
private def icmp (predicate : Data.LLVM.IntPred) (lhs rhs : Handle OpCode .value)
    (type : Handle OpCode .type) : CreateProg.Builder CreatedOpHandle :=
  CreateProg.operation (.gmir .g_icmp) #[lhs, rhs] #[type] (.inl ⟨predicate⟩)

/-- Matches the binary `opcode` operation whose operands and result have the same integer type. -/
private def matchSameTypeBinary (opcode : GMIR) :
    MatchProg.Builder (Handle OpCode .type × Handle OpCode .value × Handle OpCode .value) := do
  let type ← MatchProg.type (Attr := IntegerType)
  let lhs ← MatchProg.value type
  let rhs ← MatchProg.value type
  let _ ← MatchProg.root (.gmir opcode) #[lhs, rhs] #[type]
  return (type, lhs, rhs)

/--
Lowers `g_[su](add|sub)sat` with min and max operations, as LLVM's
`LegalizerHelper::lowerAddSubSatToMinMax`:
```
uadd.sat(a, b) = a + umin(~a, b)
usub.sat(a, b) = a - umin(a, b)
sadd.sat(a, b) = a + smin(smax(INT_MIN - smin(a, 0), b), INT_MAX - smax(a, 0))
ssub.sat(a, b) = a - smin(smax(smax(a, -1) - INT_MAX, b), smin(a, -1) - INT_MIN)
```
-/
def lowerAddSubSatToMinMax (opcode : GMIR) (signed isAdd : Bool) : Pattern OpCode :=
  let baseOp : GMIR := if isAdd then .g_add else .g_sub
  Pattern.Builder (matchSameTypeBinary opcode)
    (fun (type, lhs, rhs) => do
      let binary (opcode : GMIR) (lhs rhs : Handle OpCode .value) :=
        CreateProg.operation (.gmir opcode) #[lhs, rhs] #[type]
      if signed then
        let maxVal ← widthConstant type type intMax
        let minVal ← widthConstant type type intMin
        let (lo, hi) ← if isAdd then do
            let zero ← widthConstant type type fun _ => 0
            let smax ← binary .g_smax lhs zero.res[0]!
            let hi ← binary .g_sub maxVal.res[0]! smax.res[0]!
            let smin ← binary .g_smin lhs zero.res[0]!
            let lo ← binary .g_sub minVal.res[0]! smin.res[0]!
            pure (lo, hi)
          else do
            let negOne ← widthConstant type type fun _ => -1
            let smax ← binary .g_smax lhs negOne.res[0]!
            let lo ← binary .g_sub smax.res[0]! maxVal.res[0]!
            let smin ← binary .g_smin lhs negOne.res[0]!
            let hi ← binary .g_sub smin.res[0]! minVal.res[0]!
            pure (lo, hi)
        let rhsMax ← binary .g_smax lo.res[0]! rhs
        let rhsClamped ← binary .g_smin rhsMax.res[0]! hi.res[0]!
        binary baseOp lhs rhsClamped.res[0]!
      else
        let notLhs ← if isAdd then do
            let allOnes ← widthConstant type type fun _ => -1
            let not ← binary .g_xor lhs allOnes.res[0]!
            pure not.res[0]!
          else pure lhs
        let min ← binary .g_umin notLhs rhs
        binary baseOp lhs min.res[0]!)
    (fun op => op)

/--
Lowers `g_[su](add|sub)sat` with an operation that also computes the overflow, as LLVM's
`LegalizerHelper::lowerAddSubSatToAddoSubo`. On overflow, the unsigned result saturates to all ones
or zero, and the signed result to `(tmp >>s (width - 1)) + INT_MIN`, i.e. `INT_MAX` if the wrapped
result `tmp` is negative and `INT_MIN` otherwise.
-/
def lowerAddSubSatToAddoSubo (opcode : GMIR) (signed isAdd : Bool) : Pattern OpCode :=
  let overflowOp : GMIR := match signed, isAdd with
    | false, true => .g_uaddo
    | true, true => .g_saddo
    | false, false => .g_usubo
    | true, false => .g_ssubo
  Pattern.Builder (matchSameTypeBinary opcode)
    (fun (type, lhs, rhs) => do
      let boolType ← CreateProg.type (IntegerType.signless 1)
      let overflow ← CreateProg.operation (.gmir overflowOp) #[lhs, rhs] #[type, boolType]
      let tmp := overflow.res[0]!
      let clamp ← if signed then do
          let shiftAmount ← widthConstant type type (· - 1)
          let sign ← CreateProg.operation (.gmir .g_ashr) #[tmp, shiftAmount.res[0]!] #[type]
          let minVal ← widthConstant type type intMin
          CreateProg.operation (.gmir .g_add) #[sign.res[0]!, minVal.res[0]!] #[type]
        else
          widthConstant type type fun _ => if isAdd then -1 else 0
      CreateProg.operation (.gmir .g_select) #[overflow.res[1]!, clamp.res[0]!, tmp] #[type])
    (fun op => op)

/--
Lowers `g_[su]shlsat`, as LLVM's `LegalizerHelper::lowerShlSat`: the shift overflows if shifting the
result back does not give the operand. The unsigned result then saturates to all ones, and the
signed result to `INT_MIN` or `INT_MAX`, depending on the sign of the operand.
-/
def lowerShlSat (signed : Bool) : Pattern OpCode :=
  let opcode : GMIR := if signed then .g_sshlsat else .g_ushlsat
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let amountType ← MatchProg.type (Attr := IntegerType)
      let lhs ← MatchProg.value type
      let rhs ← MatchProg.value amountType
      let _ ← MatchProg.root (.gmir opcode) #[lhs, rhs] #[type]
      return (type, lhs, rhs))
    (fun (type, lhs, rhs) => do
      let boolType ← CreateProg.type (IntegerType.signless 1)
      let result ← CreateProg.operation (.gmir .g_shl) #[lhs, rhs] #[type]
      let orig ← CreateProg.operation (.gmir (if signed then .g_ashr else .g_lshr))
          #[result.res[0]!, rhs] #[type]
      let satVal ← if signed then do
          let satMin ← widthConstant type type intMin
          let satMax ← widthConstant type type intMax
          let zero ← widthConstant type type fun _ => 0
          let cmp ← icmp .slt lhs zero.res[0]! boolType
          CreateProg.operation (.gmir .g_select)
              #[cmp.res[0]!, satMin.res[0]!, satMax.res[0]!] #[type]
        else
          widthConstant type type fun _ => -1
      let overflow ← icmp .ne lhs orig.res[0]! boolType
      CreateProg.operation (.gmir .g_select)
          #[overflow.res[0]!, satVal.res[0]!, result.res[0]!] #[type])
    (fun op => op)

/-- Matches the `opcode` operation computing a value and whether it overflows. -/
private def matchOverflowOp (opcode : GMIR) :
    MatchProg.Builder (Handle OpCode .type × Handle OpCode .type × Handle OpCode .value ×
      Handle OpCode .value) := do
  let type ← MatchProg.type (Attr := IntegerType)
  let boolType ← MatchProg.type (Attr := IntegerType)
  let lhs ← MatchProg.value type
  let rhs ← MatchProg.value type
  let _ ← MatchProg.root (.gmir opcode) #[lhs, rhs] #[type, boolType]
  return (type, boolType, lhs, rhs)

/--
Lowers `g_uaddo` and `g_usubo`, as LLVM's `LegalizerHelper::lower`: the sum carries if it is smaller
than an operand, and the difference borrows if the left operand is smaller than the right one.
-/
def lowerUAddOUSubO (isAdd : Bool) : Pattern OpCode :=
  Pattern.Builder (matchOverflowOp (if isAdd then .g_uaddo else .g_usubo))
    (fun (type, boolType, lhs, rhs) => do
      if isAdd then
        let sum ← CreateProg.operation (.gmir .g_add) #[lhs, rhs] #[type]
        let carry ← icmp .ult sum.res[0]! rhs boolType
        return #[sum.res[0]!, carry.res[0]!]
      else
        let diff ← CreateProg.operation (.gmir .g_sub) #[lhs, rhs] #[type]
        let borrow ← icmp .ult lhs rhs boolType
        return #[diff.res[0]!, borrow.res[0]!])
    (fun results => results)

/--
Lowers `g_saddo` and `g_ssubo`, as LLVM's `LegalizerHelper::lowerSADDO_SSUBO`. The sum is smaller
than the left operand exactly when the right operand is negative, unless it overflows. The
difference is negative exactly when the left operand is smaller than the right one, unless it
overflows.
-/
def lowerSAddOSSubO (isAdd : Bool) : Pattern OpCode :=
  Pattern.Builder (matchOverflowOp (if isAdd then .g_saddo else .g_ssubo))
    (fun (type, boolType, lhs, rhs) => do
      let result ← CreateProg.operation (.gmir (if isAdd then .g_add else .g_sub))
          #[lhs, rhs] #[type]
      let zero ← widthConstant type type fun _ => 0
      let (first, second) ← if isAdd then do
          let resultLowerThanLhs ← icmp .slt result.res[0]! lhs boolType
          let rhsNegative ← icmp .slt rhs zero.res[0]! boolType
          pure (rhsNegative, resultLowerThanLhs)
        else do
          let lhsLowerThanRhs ← icmp .slt lhs rhs boolType
          let resultNegative ← icmp .slt result.res[0]! zero.res[0]! boolType
          pure (lhsLowerThanRhs, resultNegative)
      let overflow ← CreateProg.operation (.gmir .g_xor)
          #[first.res[0]!, second.res[0]!] #[boolType]
      return #[result.res[0]!, overflow.res[0]!])
    (fun results => results)

/--
Widens `g_saddo` or `g_ssubo` to `width` bits, as LLVM's `LegalizerHelper::widenScalarAddSubOverflow`.
The wide operation cannot overflow, and the narrow one overflows exactly when the wide result does
not fit in the narrow type, i.e. when sign-extending its truncation changes it.
-/
def widenAddSubOverflow (opcode : GMIR) (width : Nat) : Pattern OpCode :=
  let baseOp : GMIR := if opcode = .g_saddo then .g_add else .g_sub
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth < width)
      let boolType ← MatchProg.type (Attr := IntegerType)
      let lhs ← MatchProg.value type
      let rhs ← MatchProg.value type
      let _ ← MatchProg.root (.gmir opcode) #[lhs, rhs] #[type, boolType]
      return (type, boolType, lhs, rhs))
    (fun (type, boolType, lhs, rhs) => do
      let wideType ← CreateProg.type (IntegerType.signless width)
      let lhsExt ← CreateProg.operation (.gmir .g_sext) #[lhs] #[wideType]
      let rhsExt ← CreateProg.operation (.gmir .g_sext) #[rhs] #[wideType]
      let wide ← CreateProg.operation (.gmir baseOp) #[lhsExt.res[0]!, rhsExt.res[0]!] #[wideType]
      let trunc ← CreateProg.operation (.gmir .g_trunc) #[wide.res[0]!] #[type]
      let ext ← CreateProg.operation (.gmir .g_sext) #[trunc.res[0]!] #[wideType]
      let overflow ← icmp .ne wide.res[0]! ext.res[0]! boolType
      return #[trunc.res[0]!, overflow.res[0]!])
    (fun results => results)

/--
Lowers `g_[su](add|sub)sat` as LLVM's `LegalizerHelper::lower`: with min and max operations if they
are legal or custom for `type`, and with an overflowing operation otherwise.
-/
private def lowerAddSubSat (info : LegalizerInfo) (opcode : GMIR) (type : LLT)
    (signed isAdd : Bool) : Pattern OpCode :=
  let minMaxLegal := if signed then
      info.isLegalOrCustom (opcode := .g_smin) { types := #[type], properties := () } &&
        info.isLegalOrCustom (opcode := .g_smax) { types := #[type], properties := () }
    else
      info.isLegalOrCustom (opcode := .g_umin) { types := #[type], properties := () }
  if minMaxLegal then lowerAddSubSatToMinMax opcode signed isAdd
  else lowerAddSubSatToAddoSubo opcode signed isAdd

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

public section

/-- The pattern that lowers `query`, an `opcode` operation, if it can be lowered. -/
def lower? (info : LegalizerInfo) : (opcode : GMIR) → LegalityQuery opcode → Option (Pattern OpCode)
  | .g_sext, _ => lowerSext
  | .g_zext, _ => lowerZext
  | .g_uaddsat, query => lowerAddSubSat info .g_uaddsat (query.getLLT! (.type 0)) false true
  | .g_saddsat, query => lowerAddSubSat info .g_saddsat (query.getLLT! (.type 0)) true true
  | .g_usubsat, query => lowerAddSubSat info .g_usubsat (query.getLLT! (.type 0)) false false
  | .g_ssubsat, query => lowerAddSubSat info .g_ssubsat (query.getLLT! (.type 0)) true false
  | .g_sshlsat, _ => lowerShlSat true
  | .g_ushlsat, _ => lowerShlSat false
  | .g_uaddo, _ => lowerUAddOUSubO true
  | .g_usubo, _ => lowerUAddOUSubO false
  | .g_saddo, _ => lowerSAddOSSubO true
  | .g_ssubo, _ => lowerSAddOSSubO false
  | .g_ctlz_zero_poison, _ => lowerZeroPoisonCount .g_ctlz_zero_poison .g_ctlz
  | .g_cttz_zero_poison, _ => lowerZeroPoisonCount .g_cttz_zero_poison .g_cttz
  | _, _ => none

/-- Widens type group `typeIdx` of `opcode` to `width` bits. -/
def widenScalar? : GMIR → (typeIdx : TypeGroup) → (width : Nat) →
    Option (LocalRewritePattern OpCode)
  | .g_brcond, .type 0, width => widenBrcondCondition width
  | opcode, typeIdx, width => Option.map Puddle.Pattern.interpret <|
  match opcode, typeIdx, width with
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
  | .g_bswap, .type 0, width => widenReverse .g_bswap width
  | .g_bitreverse, .type 0, width => widenReverse .g_bitreverse width
  -- Sign extension preserves the signed order, and also the unsigned order. For `g_umin` and
  -- `g_umax`, LLVM only sign-extends where it is cheaper than zero-extending (from `i32` on
  -- RISC-V), but both are correct.
  | .g_smin, .type 0, width => widenTypeGroup .g_smin (.type 0) .g_sext width
  | .g_smax, .type 0, width => widenTypeGroup .g_smax (.type 0) .g_sext width
  | .g_umin, .type 0, width => widenTypeGroup .g_umin (.type 0) .g_sext width
  | .g_umax, .type 0, width => widenTypeGroup .g_umax (.type 0) .g_sext width
  | .g_abs, .type 0, width => widenTypeGroup .g_abs (.type 0) .g_sext width
  | .g_saddo, .type 0, width => widenAddSubOverflow .g_saddo width
  | .g_ssubo, .type 0, width => widenAddSubOverflow .g_ssubo width
  | _, _, _ => none

end

end Veir
