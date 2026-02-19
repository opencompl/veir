module

public import Veir.OpCode
public import Veir.IR.Attribute

namespace Veir

public section

/--
  Properties of the `arith.constant` operation.
-/
structure ArithConstantProperties where
  value : IntegerAttr
deriving Inhabited, Repr, Hashable

def ArithConstantProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String ArithConstantProperties := do
  if attrDict.size > 1 then
    throw s!"arith.constant: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "arith.constant: missing 'value' property"
  let .integerAttr intAttr := attr
    | throw s!"arith.constant: expected 'value' to be an integer attribute, but got {attr}"
  return { value := intAttr }

/--
  Properties of the `mod_arith.constant` operation.
-/
structure ModArithConstantProperties where
  value : IntegerAttr
deriving Inhabited, Repr, Hashable

def ModArithConstantProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String ModArithConstantProperties := do
  if attrDict.size > 1 then
    throw s!"mod_arith.constant: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "mod_arith.constant: missing 'value' property"
  let .integerAttr intAttr := attr
    | throw s!"mod_arith.constant: expected 'value' to be an integer attribute, but got {attr}"
  return { value := intAttr }

/--
  Properties of the `mod_arith.barrett_reduce` operation.
-/
structure ModArithBarrettReduceProperties where
  modulus : IntegerAttr
deriving Inhabited, Repr, Hashable

def ModArithBarrettReduceProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String ModArithBarrettReduceProperties := do
  if attrDict.size > 1 then
    throw s!"mod_arith.barrett_reduce: expected only 'modulus' property, but got {attrDict.size} properties"
  let some attr := attrDict["modulus".toUTF8]?
    | throw "mod_arith.barrett_reduce: missing 'modulus' property"
  let .integerAttr intAttr := attr
    | throw s!"mod_arith.barrett_reduce: expected 'modulus' to be an integer attribute, but got {attr}"
  return { modulus := intAttr }

/--
  A type family that maps an operation code to the type of its properties.
  For operations that do not have any properties, the type is `Unit`.
-/
@[expose]
def propertiesOf (opCode : OpCode) : Type :=
match opCode with
| .arith_constant => ArithConstantProperties
| .mod_arith_constant => ModArithConstantProperties
| .mod_arith_barrett_reduce => ModArithBarrettReduceProperties
| _ => Unit

instance (opCode : OpCode) : Inhabited (propertiesOf opCode) := by
  unfold propertiesOf
  cases opCode <;> infer_instance

instance (opCode : OpCode) : Repr (propertiesOf opCode) := by
  unfold propertiesOf
  cases opCode <;> infer_instance

instance (opCode : OpCode) : Hashable (propertiesOf opCode) := by
  unfold propertiesOf
  cases opCode <;> infer_instance

def Properties.fromAttrDict (opCode : OpCode) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (propertiesOf opCode) := by
  cases opCode
  case arith_constant => exact (ArithConstantProperties.fromAttrDict attrDict)
  case mod_arith_constant => exact (ModArithConstantProperties.fromAttrDict attrDict)
  case mod_arith_barrett_reduce => exact (ModArithBarrettReduceProperties.fromAttrDict attrDict)
  all_goals exact (Except.ok ())

/--
  Converts the properties of an operation into a dictionary of attributes.
-/
def Properties.toAttrDict (opCode : OpCode) (props : propertiesOf opCode) :
    Std.HashMap ByteArray Attribute :=
  match opCode with
  | .arith_constant =>
    (Std.HashMap.emptyWithCapacity 2).insert "value".toUTF8 (Attribute.integerAttr props.value)
  | .mod_arith_constant =>
    (Std.HashMap.emptyWithCapacity 2).insert "value".toUTF8 (Attribute.integerAttr props.value)
  | .mod_arith_barrett_reduce =>
    (Std.HashMap.emptyWithCapacity 2).insert "modulus".toUTF8 (Attribute.integerAttr props.modulus)
  | _ =>
    Std.HashMap.emptyWithCapacity 0

end
end Veir
