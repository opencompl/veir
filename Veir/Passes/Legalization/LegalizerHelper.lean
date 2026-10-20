module

public import Veir.PatternRewriter.Puddle.Definitions
import Veir.PatternRewriter.Puddle.Builders

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
      let extProps ← CreateProg.property (.gmir extOpcode) default
      let wideOperands ← (info.inOperandList.zip operands).mapM fun (group, operand) => do
        if group ≠ typeIdx then return operand
        let ext ← CreateProg.operation (.gmir extOpcode) #[operand] #[wideType] extProps
        return ext.res[0]!
      let wideResultTypes := (info.outOperandList.zip resultTypes).map fun (group, type) =>
        if group = typeIdx then wideType else type
      let wideProps ← CreateProg.applyNative props (some <| updateProps ·)
      let wide ← CreateProg.operation (.gmir opcode) wideOperands wideResultTypes wideProps
      let truncProps ← CreateProg.property (.gmir .g_trunc) default
      (info.outOperandList.zip (resultTypes.zip wide.res)).mapM fun (group, type, result) => do
        if group ≠ typeIdx then return result
        let trunc ← CreateProg.operation (.gmir .g_trunc) #[result] #[type] truncProps
        return trunc.res[0]!)
    (fun results => results)

/-- Clears the no-wrap flags, which no longer hold once the high bits are unconstrained. -/
-- NOTE: (for reviewers) we could also default construct to clear.
def clearNswNuwProperties (props : NswNuwProperties) : NswNuwProperties :=
  { props with nsw := false, nuw := false }

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
      let wide ← CreateProg.operation (.gmir .g_constant) #[] #[wideType] props
      let truncProps ← CreateProg.property (.gmir .g_trunc) default
      CreateProg.operation (.gmir .g_trunc) #[wide.res[0]!] #[type] truncProps)
    (fun trunc => trunc)

/--
A `g_constant` of type `iwidth` whose value is computed by `value` from the width of `type`.
-/
private def constantOfWidth (type : Handle OpCode .type) (width : Nat) (value : Nat → Int) :
    CreateProg.Builder CreatedOpHandle := do
  let wideType ← CreateProg.type (IntegerType.signless width)
  let props ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.gmir .g_constant))) type
      fun type => do
        let .integerType type := type.val | none
        return GMIRConstantProperties.mk (.ofInt (value type.bitwidth) (.signless width))
  CreateProg.operation (.gmir .g_constant) #[] #[wideType] props

/--
Widens the operand (type group 1) of a bit counting `opcode` to `width` bits, as the `G_CTLZ`,
`G_CTTZ` and `G_CTPOP` case of LLVM's `LegalizerHelper::widenScalar` does:
- The operand is extended, with `g_anyext` when its extra bits do not matter, and `g_zext` otherwise.
- `g_cttz` sets the bit just above the operand, so that a zero operand still counts the bitwidth
  of the operand.
- The count is computed in `iwidth`, and `g_ctlz` subtracts the extra leading zeros from it.
- The count is then zero-extended or truncated to the result type.
LLVM decides the latter by the result type, so there is one pattern for each ordering of the
width of the result and `width`.
TODO: LLVM also widens `G_CTLZ_ZERO_POISON` (by shifting the operand left by the extra bits) and
`G_CTTZ_ZERO_POISON` here. Do so once GMIR has `g_ctlz_zero_poison`/`g_cttz_zero_poison`.
-/
def widenBitCountOperand (opcode : GMIR) (props : propertiesOf (OpCode.gmir opcode))
    (width : Nat) : List (Pattern OpCode) :=
  [Ordering.lt, .eq, .gt].map fun order =>
    Pattern.Builder
      (do
        let operandType ← MatchProg.type (Attr := IntegerType) (·.bitwidth < width)
        let resultType ← MatchProg.type (Attr := IntegerType) (compare ·.bitwidth width == order)
        let operand ← MatchProg.value operandType
        let _ ← MatchProg.root (.gmir opcode) #[operand] #[resultType]
        return (operandType, resultType, operand))
      (fun (operandType, resultType, operand) => do
        let wideType ← CreateProg.type (IntegerType.signless width)
        let ext ← if opcode = .g_ctlz || opcode = .g_ctpop then do
            let extProps ← CreateProg.property (.gmir .g_zext) default
            CreateProg.operation (.gmir .g_zext) #[operand] #[wideType] extProps
          else do
            let extProps ← CreateProg.property (.gmir .g_anyext) default
            CreateProg.operation (.gmir .g_anyext) #[operand] #[wideType] extProps
        let count ← if opcode = .g_cttz then do
            let topBit ← constantOfWidth operandType width (2 ^ ·)
            let orProps ← CreateProg.property (.gmir .g_or) default
            let src ← CreateProg.operation (.gmir .g_or) #[ext.res[0]!, topBit.res[0]!]
                #[wideType] orProps
            /- TODO: The extended operand is non-zero, so LLVM uses `G_CTTZ_ZERO_POISON` here.
               Do so once GMIR has `g_cttz_zero_poison` and the legalizer can lower it back to
               `g_cttz`. -/
            let countProps ← CreateProg.property (.gmir .g_cttz) ()
            CreateProg.operation (.gmir .g_cttz) #[src.res[0]!] #[wideType] countProps
          else do
            let countProps ← CreateProg.property (.gmir opcode) props
            CreateProg.operation (.gmir opcode) #[ext.res[0]!] #[wideType] countProps
        let count ← if opcode = .g_ctlz then do
            /- The count is at least the number of extra bits, so the subtraction does not wrap. -/
            let sizeDiff ← constantOfWidth operandType width (width - ·)
            let subProps ← CreateProg.property (.gmir .g_sub) { nsw := false, nuw := true }
            CreateProg.operation (.gmir .g_sub) #[count.res[0]!, sizeDiff.res[0]!] #[wideType]
                subProps
          else pure count
        match order with
        | .lt => do
          let truncProps ← CreateProg.property (.gmir .g_trunc) default
          CreateProg.operation (.gmir .g_trunc) #[count.res[0]!] #[resultType] truncProps
        | .eq => pure count
        | .gt => do
          let zextProps ← CreateProg.property (.gmir .g_zext) default
          CreateProg.operation (.gmir .g_zext) #[count.res[0]!] #[resultType] zextProps)
      (fun result => result)

public section

/--
The patterns that widen type group `typeIdx` of `opcode` to `width` bits, tried in order.
-/
def widenScalar (opcode : GMIR) (typeIdx : TypeGroup) (width : Nat) : List (Pattern OpCode) :=
  match opcode, typeIdx with
  | .g_ctlz, .type 1 => widenBitCountOperand .g_ctlz () width
  | .g_cttz, .type 1 => widenBitCountOperand .g_cttz () width
  | .g_ctpop, .type 1 => widenBitCountOperand .g_ctpop () width
  | _, _ => (widenScalar? opcode typeIdx width).toList
where
  /-- Widens type group `typeIdx` of `opcode` to `width` bits with a single pattern. -/
  widenScalar? : GMIR → (typeIdx : TypeGroup) → (width : Nat) → Option (Pattern OpCode)
  -- The high bits of the operands never reach the low bits of the result, so any extension is
  -- fine.
  | .g_add, .type 0, width => widenTypeGroup .g_add (.type 0) .g_anyext width clearNswNuwProperties
  | .g_sub, .type 0, width => widenTypeGroup .g_sub (.type 0) .g_anyext width clearNswNuwProperties
  -- The result has no operands in its group, so `g_anyext` is not used.
  | .g_icmp, .type 0, width => widenTypeGroup .g_icmp (.type 0) .g_anyext width
  -- The high bits matter for the comparison, and sign extension preserves both the signed and
  -- the unsigned order.
  | .g_icmp, .type 1, width => widenTypeGroup .g_icmp (.type 1) .g_sext width
  | .g_and, .type 0, width => widenTypeGroup .g_and (.type 0) .g_anyext width
  | .g_or, .type 0, width => widenTypeGroup .g_or (.type 0) .g_anyext width
  | .g_xor, .type 0, width => widenTypeGroup .g_xor (.type 0) .g_anyext width
  | .g_mul, .type 0, width => widenTypeGroup .g_mul (.type 0) .g_anyext width clearNswNuwProperties
  -- The high bits matter for division and remainder, so the operands are extended according to
  -- the signedness of the operation. Exactness is preserved by both extensions.
  | .g_sdiv, .type 0, width => widenTypeGroup .g_sdiv (.type 0) .g_sext width
  | .g_srem, .type 0, width => widenTypeGroup .g_srem (.type 0) .g_sext width
  | .g_udiv, .type 0, width => widenTypeGroup .g_udiv (.type 0) .g_zext width
  | .g_urem, .type 0, width => widenTypeGroup .g_urem (.type 0) .g_zext width
  | .g_constant, .type 0, width => widenConstant width
  | .g_cttz, .type 0, width => widenTypeGroup .g_cttz (.type 0) .g_zext width
  | .g_ctlz , .type 0, width => widenTypeGroup .g_ctlz (.type 0) .g_zext width
  | .g_ctpop , .type 0, width => widenTypeGroup .g_ctpop (.type 0) .g_zext width
  | _, _, _ => none

end

end Veir
