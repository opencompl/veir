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

public section

/-- The pattern that lowers `opcode`, if it can be lowered. -/
def lower? : GMIR → Option (Pattern OpCode)
  | .g_sext => lowerSext
  | _ => none

/-- Widens type group `typeIdx` of `opcode` to `width` bits. -/
def widenScalar? : GMIR → (typeIdx : TypeGroup) → (width : Nat) → Option (Pattern OpCode)
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
  -- `g_sext_inreg` only reads the low `sz` bits, so any extension is fine.
  | .g_sext_inreg, .type 0, width => widenTypeGroup .g_sext_inreg (.type 0) .g_anyext width
  | _, _, _ => none

end

end Veir
