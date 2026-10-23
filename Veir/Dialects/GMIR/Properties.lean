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

/--
Properties of `gmir.g_frame_index`: the size and alignment, in bytes, of the stack object.
Upstream keeps these in `MachineFrameInfo` and only references the object by index.
-/
structure GMIRFrameIndexProperties where
  size : BitVec 64
  alignment : BitVec 64
deriving Inhabited, Repr, Hashable, DecidableEq

def GMIRFrameIndexProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String GMIRFrameIndexProperties := do
  let size ← getI64Attr "gmir.g_frame_index" "size" attrDict
  let alignment ← getI64Attr "gmir.g_frame_index" "alignment" attrDict
  return { size, alignment }

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
