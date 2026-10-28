module

public import Veir.PatternRewriter.Puddle.Definitions
public import Veir.PatternRewriter.Basic
import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution

/-!
# Legalization Actions

This file implements the legalization actions as Puddle patterns.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/include/llvm/CodeGen/GlobalISel/LegalizerHelper.h
-/

namespace Veir

open Puddle

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

/-- Creates the `g_constant` `value srcWidth` of type `type`, where `srcWidth` is the width of the
integer type `srcType`. -/
private def widthConstant (srcType type : Handle OpCode .type) (value : Nat → Int) :
    CreateProg.Builder CreatedOpHandle := do
  let props ← CreateProg.applyNative (srcType, type) fun (srcType, type) =>
    match srcType.val, type.val with
    | .integerType srcType, .integerType type =>
      some (GMIRConstantProperties.mk (.ofInt (value srcType.bitwidth) type))
    | _, _ => none
  CreateProg.operation (.gmir .g_constant) #[] #[type] (.inr props)

/--
Widens the operand of `g_ctlz` to `width` bits. The operand is zero-extended, so the count is too
large by the number of added bits, which are subtracted from it, as in LLVM's
`LegalizerHelper::widenScalar`. The result must already be `width` bits wide, which the rules
ensure by widening it first.
-/
def widenCtlzSrc (width : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcType ← MatchProg.type (Attr := IntegerType) (·.bitwidth < width)
      let resType ← MatchProg.type (Attr := IntegerType) (·.bitwidth = width)
      let src ← MatchProg.value srcType
      let _ ← MatchProg.root (.gmir .g_ctlz) #[src] #[resType]
      return (srcType, resType, src))
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
result must already be `width` bits wide, which the rules ensure by widening it first.
-/
def widenCttzSrc (width : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcType ← MatchProg.type (Attr := IntegerType) (·.bitwidth < width)
      let resType ← MatchProg.type (Attr := IntegerType) (·.bitwidth = width)
      let src ← MatchProg.value srcType
      let _ ← MatchProg.root (.gmir .g_cttz) #[src] #[resType]
      return (srcType, resType, src))
    (fun (srcType, resType, src) => do
      let ext ← CreateProg.operation (.gmir .g_anyext) #[src] #[resType]
      let topBit ← widthConstant srcType resType (2 ^ ·)
      let wideSrc ← CreateProg.operation (.gmir .g_or) #[ext.res[0]!, topBit.res[0]!] #[resType]
      CreateProg.operation (.gmir .g_cttz) #[wideSrc.res[0]!] #[resType])
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

/-- Lowers `g_sext` to a `g_anyext` followed by a `g_sext_inreg` of the source width, which is what
LLVM's artifact combiner makes of a `g_sext` of a `g_trunc`. -/
def lowerSext : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcType ← MatchProg.type (Attr := IntegerType)
      let resType ← MatchProg.type (Attr := IntegerType)
      let src ← MatchProg.value srcType
      let _ ← MatchProg.root (.gmir .g_sext) #[src] #[resType]
      return (srcType, resType, src))
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
    (do
      let srcType ← MatchProg.type (Attr := IntegerType)
      let resType ← MatchProg.type (Attr := IntegerType)
      let src ← MatchProg.value srcType
      let _ ← MatchProg.root (.gmir .g_zext) #[src] #[resType]
      return (srcType, resType, src))
    (fun (srcType, resType, src) => do
      let ext ← CreateProg.operation (.gmir .g_anyext) #[src] #[resType]
      let maskProps ← CreateProg.applyNative (srcType, resType) fun (srcType, resType) =>
        match srcType.val, resType.val with
        | .integerType srcType, .integerType resType =>
          some (GMIRConstantProperties.mk (.ofInt (2 ^ srcType.bitwidth - 1) resType))
        | _, _ => none
      let mask ← CreateProg.operation (.gmir .g_constant) #[] #[resType] (.inr maskProps)
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

public section

/-- The pattern that lowers `opcode`, if it can be lowered. -/
def lower? : GMIR → Option (Pattern OpCode)
  | .g_sext => lowerSext
  | .g_zext => lowerZext
  | _ => none

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
  | _, _, _ => none

end

end Veir
