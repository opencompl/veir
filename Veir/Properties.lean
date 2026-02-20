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

inductive ArithCmpIPredicate where
| eq
| ne
| slt
| sle
| sgt
| sge
| ult
| ule
| ugt
| uge
deriving Inhabited, Repr, DecidableEq, Hashable

def ArithCmpIPredicate.ofString? (s : String) : Option ArithCmpIPredicate :=
  match s with
  | "eq" => some .eq
  | "ne" => some .ne
  | "slt" => some .slt
  | "sle" => some .sle
  | "sgt" => some .sgt
  | "sge" => some .sge
  | "ult" => some .ult
  | "ule" => some .ule
  | "ugt" => some .ugt
  | "uge" => some .uge
  | _ => none

def ArithCmpIPredicate.toString : ArithCmpIPredicate → String
  | .eq => "eq"
  | .ne => "ne"
  | .slt => "slt"
  | .sle => "sle"
  | .sgt => "sgt"
  | .sge => "sge"
  | .ult => "ult"
  | .ule => "ule"
  | .ugt => "ugt"
  | .uge => "uge"

instance : ToString ArithCmpIPredicate where
  toString := ArithCmpIPredicate.toString

structure ArithCmpiProperties where
  predicate : ArithCmpIPredicate
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

def ArithCmpiProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String ArithCmpiProperties := do
  if attrDict.size > 1 then
    throw s!"arith.cmpi: expected only 'predicate' property, but got {attrDict.size} properties"
  let some attr := attrDict["predicate".toUTF8]?
    | throw "arith.cmpi: missing 'predicate' property"
  let .stringAttr predicate := attr
    | throw s!"arith.cmpi: expected 'predicate' to be a string attribute, but got {attr}"
  let some predicate := ArithCmpIPredicate.ofString? (String.fromUTF8! predicate.value)
    | throw s!"arith.cmpi: unsupported predicate '{String.fromUTF8! predicate.value}'"
  return { predicate }

/--
  A type family that maps an operation code to the type of its properties.
  For operations that do not have any properties, the type is `Unit`.
-/
@[expose]
def propertiesOf (opCode : OpCode) : Type :=
match opCode with
| .arith_constant => ArithConstantProperties
| .arith_cmpi => ArithCmpiProperties
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
  case arith_cmpi => exact (ArithCmpiProperties.fromAttrDict attrDict)
  all_goals exact (Except.ok ())

/--
  Converts the properties of an operation into a dictionary of attributes.
-/
def Properties.toAttrDict (opCode : OpCode) (props : propertiesOf opCode) :
    Std.HashMap ByteArray Attribute :=
  match opCode with
  | .arith_constant =>
    (Std.HashMap.emptyWithCapacity 2).insert "value".toUTF8 (Attribute.integerAttr props.value)
  | .arith_cmpi =>
    (Std.HashMap.emptyWithCapacity 2).insert "predicate".toUTF8
      (Attribute.stringAttr { value := props.predicate.toString.toUTF8 })
  | _ =>
    Std.HashMap.emptyWithCapacity 0

end
end Veir
