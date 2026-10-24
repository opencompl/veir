module

public import Veir.IR.Attribute
public import Std.Data.HashMap

import Veir.Dialects.Builtin.Properties

namespace Veir

public section

/--
Properties of `gmir.g_constant`.
-/
structure GMIRConstantProperties where
  value : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def GMIRConstantProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String GMIRConstantProperties := do
  if attrDict.size > 1 then
    throw s!"gmir.g_constant: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "gmir.g_constant: missing 'value' property"
  let .integerAttr intAttr := attr
    | throw s!"gmir.g_constant: expected 'value' to be an integer attribute, but got {attr}"
  return { value := intAttr }

/-- The negation of the constant, wrapped to its type. -/
def GMIRConstantProperties.neg (props : GMIRConstantProperties) : GMIRConstantProperties :=
  { value := IntegerAttr.ofInt (-props.value.value) props.value.type }

/-- Whether the constant is the minimum signed value of its type. -/
def GMIRConstantProperties.isMinSigned (props : GMIRConstantProperties) : Bool :=
  let bitwidth := props.value.type.bitwidth
  BitVec.ofInt bitwidth props.value.value = BitVec.intMin bitwidth

/--
Properties of `gmir.g_sext_inreg`. `sz` is the number of low bits that are kept.
-/
structure SextInRegProperties where
  sz : BitVec 64
deriving Inhabited, Repr, Hashable, DecidableEq

def SextInRegProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String SextInRegProperties := do
  let sz ← getI64Attr "gmir.g_sext_inreg" "sz" attrDict
  return { sz }

end

end Veir
