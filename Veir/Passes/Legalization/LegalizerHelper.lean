module

public import Veir.PatternRewriter.Puddle.Definitions
public import Veir.PatternRewriter.Puddle.Builders

/-!
# Legalization Actions

This file implements the legalization actions as Puddle patterns.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/include/llvm/CodeGen/GlobalISel/LegalizerHelper.h
-/

namespace Veir

open Puddle

public section

/--
Matches a binary `opcode` operation whose operands and result have the same integer type, which
satisfies `typeMatcher`.
-/
def matchBinop (opcode : GMIR) (typeMatcher : IntegerType → Bool) :
    MatchProg.Builder (Handle OpCode .type × Handle OpCode .value × Handle OpCode .value) := do
  let type ← MatchProg.type (Attr := IntegerType) typeMatcher
  let lhs ← MatchProg.value type
  let rhs ← MatchProg.value type
  let _ ← MatchProg.root (.gmir opcode) #[lhs, rhs] #[type]
  return (type, lhs, rhs)

/-- Extends `operand` to `wideType` with `extOpcode`, and returns the extended value. -/
def buildExt (operand : Handle OpCode .value) (wideType : Handle OpCode .type)
    (extOpcode : GMIR) (props : propertiesOf (OpCode.gmir extOpcode)) :
    CreateProg.Builder (Handle OpCode .value) := do
  let props ← CreateProg.property (.gmir extOpcode) props
  let ext ← CreateProg.operation (.gmir extOpcode) #[operand] #[wideType] props
  return ext.res[0]!

/--
Computes `opcode` on `lhs` and `rhs` extended to `wideType` with `g_anyext`, and returns the wide
result. The new high bits are unconstrained, so the no-wrap flags no longer hold.
-/
def buildWideBinop (opcode : GMIR) (noFlags : propertiesOf (OpCode.gmir opcode))
    (wideType : Handle OpCode .type) (lhs rhs : Handle OpCode .value) :
    CreateProg.Builder (Handle OpCode .value) := do
  let wideLhs ← buildExt lhs wideType .g_anyext ()
  let wideRhs ← buildExt rhs wideType .g_anyext ()
  let props ← CreateProg.property (.gmir opcode) noFlags
  let wide ← CreateProg.operation (.gmir opcode) #[wideLhs, wideRhs] #[wideType] props
  return wide.res[0]!

/-- Truncates the wide result `wide` back to `type`. -/
def buildTrunc (wide : Handle OpCode .value) (type : Handle OpCode .type) :
    CreateProg.Builder CreatedOpHandle := do
  let props ← CreateProg.property (.gmir .g_trunc) ⟨false, false⟩
  CreateProg.operation (.gmir .g_trunc) #[wide] #[type] props

end

/--
Extends the binary operands to `width` bits and then truncates the result back to the original
type. The extension is performed with `g_anyext` because the high bits are assumed to not matter
for the operation. (This is not true for comparisons.)
-/
def widenBinop (opcode : GMIR) (noFlags : propertiesOf (OpCode.gmir opcode)) (width : Nat) :
    Pattern OpCode :=
  Pattern.Builder
    (matchBinop opcode (·.bitwidth < width))
    (fun (type, lhs, rhs) => do
      let wideType ← CreateProg.type (IntegerType.signless width)
      let wide ← buildWideBinop opcode noFlags wideType lhs rhs
      buildTrunc wide type)
    (fun trunc => trunc)

/--
Extends the operands of `g_icmp` to `width` bits and then compares the wide operands. The extension
is performed with `g_sext` because the high bits matter for the comparison, and sign extension
preserves both the signed and the unsigned order.
-/
def widenICmpOperands (width : Nat) : Pattern OpCode :=
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
      let wideLhs ← buildExt lhs wideType .g_sext ()
      let wideRhs ← buildExt rhs wideType .g_sext ()
      CreateProg.operation (.gmir .g_icmp) #[wideLhs, wideRhs] #[resultType] root.properties)
    (fun cmp => cmp)

/-- Widens the result of `g_icmp` to `width` bits and then truncates it back. -/
def widenICmpResult (width : Nat) : Pattern OpCode :=
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
      buildTrunc cmp.res[0]! resultType)
    (fun trunc => trunc)

public section

/-- Widens type group `typeIdx` of `opcode` to `width` bits. -/
def widenScalar? : GMIR → (typeIdx : TypeGroup) → (width : Nat) → Option (Pattern OpCode)
  | .g_add, .type 0, width => widenBinop .g_add ⟨false, false⟩ width
  | .g_sub, .type 0, width => widenBinop .g_sub ⟨false, false⟩ width
  | .g_icmp, .type 0, width => widenICmpResult width
  | .g_icmp, .type 1, width => widenICmpOperands width
  | _, _, _ => none

end

end Veir
