module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.Global.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Global where
| «def»
| read
| write
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Global.propertiesOf (op : Global) : Type :=
match op with
| .«def» => GlobalDefProperties
| .read => GlobalRefProperties
| .write => GlobalRefProperties

def Global.fromAttrDict
    (op : Global) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Global.propertiesOf op) := by
  cases op
  case «def» => exact GlobalDefProperties.fromAttrDict attrDict
  case read => exact GlobalRefProperties.fromAttrDict "global.read" attrDict
  case write => exact GlobalRefProperties.fromAttrDict "global.write" attrDict

def Global.toAttrDict
    (op : Global) (props : Global.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .«def» => Id.run do
    let mut dict := (Std.HashMap.emptyWithCapacity 4).insert
      "sym_name".toUTF8 (Attribute.stringAttr props.sym_name)
    if props.constant then
      dict := dict.insert "constant".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict := dict.insert "type".toUTF8 props.type
    if let some initialValue := props.initial_value then
      dict := dict.insert "initial_value".toUTF8 initialValue
    return dict
  | .read | .write =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "name_ref".toUTF8 (Attribute.flatSymbolRefAttr props.name_ref)

@[get_effects]
def Global.getEffects
    (op : Global) (_props : Global.propertiesOf op) : MemoryEffects :=
  match op with
  | .«def» => .unknown
  | .read => .read
  | .write => .write

def Global.isConstantLike (_op : Global) : Bool := false

def Global.hasSSADominance (_op : Global) (_index : Nat) : Bool := true

#generate_dialect Global

instance : IsOpCode Global where
  fromName := Global.fromName
  name := Global.name
  propertiesOf := Global.propertiesOf
  fromAttrDict := Global.fromAttrDict
  toAttrDict := Global.toAttrDict

def Global.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Global] (opType : Global) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .«def» => op.verifyPlainOpCounts ctx opIn 0 0
  | .read => op.verifyPlainOpCounts ctx opIn 0 1
  | .write => op.verifyPlainOpCounts ctx opIn 1 0

instance : HasOpInfo Global where
  verifyLocalInvariants := Global.verifyLocalInvariants
  getEffects := Global.getEffects
  isConstantLike := Global.isConstantLike
  hasSSADominance := Global.hasSSADominance

end

end Veir
