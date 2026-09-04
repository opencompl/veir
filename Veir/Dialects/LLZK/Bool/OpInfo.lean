module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.Bool.Properties
public import Veir.Dialects.LLZK.Function.OpInfo
meta import Veir.Meta.OpCode

namespace Veir

public section

namespace LLZK

@[opcodes]
inductive Bool where
| and
| or
| xor
| not
| assert
| cmp
deriving Inhabited, Repr, Hashable, DecidableEq

end LLZK

@[expose, properties_of]
def LLZK.Bool.propertiesOf (op : LLZK.Bool) : Type :=
match op with
| .assert => BoolAssertProperties
| .cmp => BoolCmpProperties
| _ => Unit

/-- Reject properties on an operation whose schema has none. -/
private def noProperties (opName : String) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String Unit :=
  if attrDict.size > 0 then
    let plural := if attrDict.size = 1 then "property" else "properties"
    .error s!"{opName}: expected no properties, but got {attrDict.size} {plural}"
  else
    .ok ()

def LLZK.Bool.fromAttrDict
    (op : LLZK.Bool) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (LLZK.Bool.propertiesOf op) :=
  match op with
  | .and => noProperties "bool.and" attrDict
  | .or => noProperties "bool.or" attrDict
  | .xor => noProperties "bool.xor" attrDict
  | .not => noProperties "bool.not" attrDict
  | .assert => BoolAssertProperties.fromAttrDict attrDict
  | .cmp => BoolCmpProperties.fromAttrDict attrDict

def LLZK.Bool.toAttrDict
    (op : LLZK.Bool) (props : LLZK.Bool.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .assert =>
    match props.msg with
    | some msg =>
      (Std.HashMap.emptyWithCapacity 1).insert
        "msg".toUTF8 (Attribute.stringAttr msg)
    | none => Std.HashMap.emptyWithCapacity 0
  | .cmp =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "predicate".toUTF8 props.predicateAttr
  | _ => Std.HashMap.emptyWithCapacity 0

@[get_effects]
def LLZK.Bool.getEffects
    (op : LLZK.Bool) (_props : LLZK.Bool.propertiesOf op) : MemoryEffects :=
  match op with
  | .assert => .write
  | .and | .or | .xor | .not | .cmp => .none

def LLZK.Bool.isConstantLike (_op : LLZK.Bool) := false

def LLZK.Bool.hasSSADominance (_op : LLZK.Bool) (_index : Nat) := true

#generate_dialect LLZK.Bool

instance : IsOpCode LLZK.Bool where
  fromName := LLZK.Bool.fromName
  name := LLZK.Bool.name
  propertiesOf := LLZK.Bool.propertiesOf
  fromAttrDict := LLZK.Bool.fromAttrDict
  toAttrDict := LLZK.Bool.toAttrDict

private def OperationPtr.verifyBoolTypes {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo) (operandCount resultCount : Nat) :
    Except String PUnit := do
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType! ctx.raw))
  for i in [0:operandCount] do
    (op.getOperandTypes! ctx.raw)[i]!.verifyI1
      s!"{instrName}: Expected operand {i} to have i1 type"
  for i in [0:resultCount] do
    (op.getResultTypes! ctx.raw)[i]!.verifyI1
      s!"{instrName}: Expected result {i} to have i1 type"

def LLZK.Bool.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo LLZK.Bool] (opType : LLZK.Bool) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .and | .or | .xor => do
    op.verifyPlainOpCounts ctx opIn 2 1
    op.verifyBoolTypes ctx 2 1
    op.verifyLLZKNotFieldNative ctx
  | .not => do
    op.verifyPlainOpCounts ctx opIn 1 1
    op.verifyBoolTypes ctx 1 1
    op.verifyLLZKNotFieldNative ctx
  | .assert => do
    op.verifyPlainOpCounts ctx opIn 1 0
    op.verifyBoolTypes ctx 1 0
  | .cmp => do
    op.verifyPlainOpCounts ctx opIn 2 1
    let operandType ← op.verifyOperandTypesMatch ctx 0 1
      "bool.cmp: Expected operands to have the same type"
    if !(operandType.val matches Attribute.feltType _) then
      throw "bool.cmp: Expected operands to have FeltType"
    (op.getResultTypes! ctx.raw)[0]!.verifyI1
      "bool.cmp: Expected result 0 to have i1 type"

instance : HasOpInfo LLZK.Bool where
  verifyLocalInvariants := LLZK.Bool.verifyLocalInvariants
  getEffects := LLZK.Bool.getEffects
  isConstantLike := LLZK.Bool.isConstantLike
  hasSSADominance := LLZK.Bool.hasSSADominance

end

end Veir
