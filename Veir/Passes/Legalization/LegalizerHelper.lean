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

public section

/--
Widens type group `typeIdx` of `opcode` from `narrowWidth` to `width` bits.
`isSExtCheaperThanZExt` is the target hook that decides how to extend the operands when either
extension is correct, as in LLVM's `TargetLowering::isSExtCheaperThanZExt`.
-/
def widenScalar? (isSExtCheaperThanZExt : (fromWidth toWidth : Nat) → Bool) :
    GMIR → (typeIdx : TypeGroup) → (narrowWidth width : Nat) → Option (Pattern OpCode)
  -- The high bits of the operands never reach the low bits of the result, so any extension is
  -- fine.
  | .g_add, .type 0, _, width => widenTypeGroup .g_add (.type 0) .g_anyext width clearNswNuwProperties
  | .g_sub, .type 0, _, width => widenTypeGroup .g_sub (.type 0) .g_anyext width clearNswNuwProperties
  -- The result has no operands in its group, so `g_anyext` is not used.
  | .g_icmp, .type 0, _, width => widenTypeGroup .g_icmp (.type 0) .g_anyext width
  -- The high bits matter for the comparison, and sign extension preserves both the signed and
  -- the unsigned order.
  | .g_icmp, .type 1, _, width => widenTypeGroup .g_icmp (.type 1) .g_sext width
  | .g_and, .type 0, _, width => widenTypeGroup .g_and (.type 0) .g_anyext width
  | .g_or, .type 0, _, width => widenTypeGroup .g_or (.type 0) .g_anyext width
  | .g_xor, .type 0, _, width => widenTypeGroup .g_xor (.type 0) .g_anyext width
  | .g_mul, .type 0, _, width => widenTypeGroup .g_mul (.type 0) .g_anyext width clearNswNuwProperties
  -- The high bits matter for division and remainder, so the operands are extended according to
  -- the signedness of the operation. Exactness is preserved by both extensions.
  | .g_sdiv, .type 0, _, width => widenTypeGroup .g_sdiv (.type 0) .g_sext width
  | .g_srem, .type 0, _, width => widenTypeGroup .g_srem (.type 0) .g_sext width
  | .g_udiv, .type 0, _, width => widenTypeGroup .g_udiv (.type 0) .g_zext width
  | .g_urem, .type 0, _, width => widenTypeGroup .g_urem (.type 0) .g_zext width
  -- Sign extension preserves the signed order. Both extensions preserve the unsigned order, so
  -- the unsigned operations use the cheaper one.
  | .g_smin, .type 0, _, width => widenTypeGroup .g_smin (.type 0) .g_sext width
  | .g_smax, .type 0, _, width => widenTypeGroup .g_smax (.type 0) .g_sext width
  | .g_umin, .type 0, narrowWidth, width =>
    let extOpcode := if isSExtCheaperThanZExt narrowWidth width then .g_sext else .g_zext
    widenTypeGroup .g_umin (.type 0) extOpcode width
  | .g_umax, .type 0, narrowWidth, width =>
    let extOpcode := if isSExtCheaperThanZExt narrowWidth width then .g_sext else .g_zext
    widenTypeGroup .g_umax (.type 0) extOpcode width
  | .g_abs, .type 0, _, width => widenTypeGroup .g_abs (.type 0) .g_sext width
  | _, _, _, _ => none

end

end Veir
