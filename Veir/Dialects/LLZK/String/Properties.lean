module

public import Veir.IR.Attribute

namespace Veir

public section

/--
  Properties of the `string.new` operation. Carries a `StringAttr`-typed
  `value` field containing the literal string.
-/
structure StringNewProperties where
  value : StringAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def StringNewProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String StringNewProperties := do
  if attrDict.size > 1 then
    throw s!"string.new: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "string.new: missing 'value' property"
  let .stringAttr strAttr := attr
    | throw s!"string.new: expected 'value' to be a string attribute, but got {attr}"
  return { value := strAttr }

end

end Veir
