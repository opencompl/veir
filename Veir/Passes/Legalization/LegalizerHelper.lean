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
Extends the binary operands to `width` bits and then truncates the result back to the original
type. The extension is performed with `g_anyext` because the high bits are assumed to not matter
for the operation. (This is not true for comparisons.)
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
      -- The new high bits are unconstrained, so the no-wrap flags no longer hold.
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
Extends the operands of `g_icmp` to `width` bits and then compares the wide operands. The extension
is performed with `g_sext` because the high bits matter for the comparison, and sign extension
preserves both the signed and the unsigned order.
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

/-- Widens the result of `g_icmp` to `width` bits and then truncates it back. -/
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

/-- Widens type group `typeIdx` of `opcode` to `width` bits. -/
def widenScalar? : GMIR → (typeIdx width : Nat) → Option (Pattern OpCode)
  | .g_add, 0, width => widenBinop .g_add ⟨false, false⟩ width
  | .g_sub, 0, width => widenBinop .g_sub ⟨false, false⟩ width
  | .g_icmp, 0, width => widenICmpResult width
  | .g_icmp, 1, width => widenICmpOperands width
  | _, _, _ => none

end

end Veir
