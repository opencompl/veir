module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.Bool.Properties
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

def LLZK.Bool.fromAttrDict
    (op : LLZK.Bool) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (LLZK.Bool.propertiesOf op) :=
  match op with
  | .and => .ok ()
  | .or => .ok ()
  | .xor => .ok ()
  | .not => .ok ()
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

def LLZK.Bool.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo LLZK.Bool] (opType : LLZK.Bool) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .and | .or | .xor => op.verifyPlainOpCounts ctx opIn 2 1
  | .not => op.verifyPlainOpCounts ctx opIn 1 1
  | .assert => op.verifyPlainOpCounts ctx opIn 1 0
  | .cmp => op.verifyPlainOpCounts ctx opIn 2 1

instance : HasOpInfo LLZK.Bool where
  verifyLocalInvariants := LLZK.Bool.verifyLocalInvariants
  getEffects := LLZK.Bool.getEffects
  isConstantLike := LLZK.Bool.isConstantLike
  hasSSADominance := LLZK.Bool.hasSSADominance

end

end Veir
