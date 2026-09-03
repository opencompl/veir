module

public import Veir.IR.Attribute

namespace Veir

public section

/--
  Properties of the `felt.const` operation.

  The `value` field is a structured, typed `FeltConstAttr`.
-/
structure FeltConstProperties where
  value : FeltConstAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def FeltConstProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String FeltConstProperties := do
  if attrDict.size > 1 then
    throw s!"felt.const: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "felt.const: missing 'value' property"
  let .feltConstAttr fcAttr := attr
    | throw s!"felt.const: expected 'value' to be a `#felt<const N> : !felt.type` attribute, but got {attr}"
  return { value := fcAttr }

end

end Veir
