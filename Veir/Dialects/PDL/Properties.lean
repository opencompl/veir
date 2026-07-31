module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of the `pdl.attribute` operation.

  `value` is the optional constant value the attribute is constrained to. It is
  absent when the attribute is unconstrained or only constrained by the
  `valueType` operand, so it is modelled as an `Option` and omitted again when
  printing.
-/
structure PDLAttributeProperties where
  value : Option Attribute
deriving Inhabited, Repr, Hashable, DecidableEq

def PDLAttributeProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String PDLAttributeProperties := do
  let value := attrDict["value".toUTF8]?
  if attrDict.size > (if value.isSome then 1 else 0) then
    throw s!"pdl.attribute: expected only the 'value' property, but got {attrDict.size} properties"
  return { value := value }

end

end Veir
