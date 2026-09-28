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

public section

open Puddle

/--
Widens the binary operation `opcode` to `width` bits with `g_anyext` and `g_trunc`. The flags are
dropped, since the high bits are arbitrary and the wide operation may overflow.
-/
private def widenBinop (opcode : GMIR) (noFlags : propertiesOf (OpCode.gmir opcode)) (width : Nat) :
    Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth < width)
      let lhs ← MatchProg.value type
      let rhs ← MatchProg.value type
      let _ ← MatchProg.root (.gmir opcode) #[lhs, rhs] #[type]
      return (type, lhs, rhs))
    (fun (type, lhs, rhs) => do
      let wideType ← CreateProg.type (IntegerType.signless width)
      let anyextProps ← CreateProg.property (.gmir .g_anyext) ()
      let wideLhs ← CreateProg.operation (.gmir .g_anyext) #[lhs] #[wideType] anyextProps
      let wideRhs ← CreateProg.operation (.gmir .g_anyext) #[rhs] #[wideType] anyextProps
      let props ← CreateProg.property (.gmir opcode) noFlags
      let wide ← CreateProg.operation (.gmir opcode) #[wideLhs.res[0]!, wideRhs.res[0]!]
        #[wideType] props
      let truncProps ← CreateProg.property (.gmir .g_trunc) ⟨false, false⟩
      CreateProg.operation (.gmir .g_trunc) #[wide.res[0]!] #[type] truncProps)
    (fun trunc => trunc)

/--
Widens the operands of `g_icmp` to `width` bits with `g_sext`. As on RV64 in LLVM, this is done
for every predicate, since sign extension preserves both the signed and the unsigned order.
-/
private def widenICmpOperands (width : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let operandType ← MatchProg.type (Attr := IntegerType) (·.bitwidth < width)
      let resultType ← MatchProg.type (Attr := TypeAttr)
      let lhs ← MatchProg.value operandType
      let rhs ← MatchProg.value operandType
      let root ← MatchProg.root (.gmir .g_icmp) #[lhs, rhs] #[resultType]
      return (resultType, lhs, rhs, root))
    (fun (resultType, lhs, rhs, root) => do
      let wideType ← CreateProg.type (IntegerType.signless width)
      let sextProps ← CreateProg.property (.gmir .g_sext) ()
      let wideLhs ← CreateProg.operation (.gmir .g_sext) #[lhs] #[wideType] sextProps
      let wideRhs ← CreateProg.operation (.gmir .g_sext) #[rhs] #[wideType] sextProps
      CreateProg.operation (.gmir .g_icmp) #[wideLhs.res[0]!, wideRhs.res[0]!] #[resultType]
        root.properties)
    (fun cmp => cmp)

/-- Widens the result of `g_icmp` to `width` bits with `g_trunc`. -/
private def widenICmpResult (width : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let operandType ← MatchProg.type (Attr := TypeAttr)
      let resultType ← MatchProg.type (Attr := IntegerType) (·.bitwidth < width)
      let lhs ← MatchProg.value operandType
      let rhs ← MatchProg.value operandType
      let root ← MatchProg.root (.gmir .g_icmp) #[lhs, rhs] #[resultType]
      return (resultType, lhs, rhs, root))
    (fun (resultType, lhs, rhs, root) => do
      let wideType ← CreateProg.type (IntegerType.signless width)
      let cmp ← CreateProg.operation (.gmir .g_icmp) #[lhs, rhs] #[wideType] root.properties
      let truncProps ← CreateProg.property (.gmir .g_trunc) ⟨false, false⟩
      CreateProg.operation (.gmir .g_trunc) #[cmp.res[0]!] #[resultType] truncProps)
    (fun trunc => trunc)

/--
The pattern that widens type group `typeIdx` of `opcode` to `width` bits. Returns `none` if this
widening is not implemented.
-/
def widenScalar? : GMIR → (typeIdx width : Nat) → Option (Pattern OpCode)
  | .g_add, 0, width => widenBinop .g_add ⟨false, false⟩ width
  | .g_sub, 0, width => widenBinop .g_sub ⟨false, false⟩ width
  | .g_icmp, 0, width => widenICmpResult width
  | .g_icmp, 1, width => widenICmpOperands width
  | _, _, _ => none

end

end Veir
