module

public import Veir.IR.Attribute

namespace Veir

public section

/-- Properties of `include.from`.

Symbol uniqueness is not verified.
-/
structure IncludeFromProperties where
  sym_name : StringAttr
  path : StringAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def IncludeFromProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String IncludeFromProperties := do
  if attrDict.size > 2 then
    throw s!"include.from: expected 'sym_name' and 'path' properties, got {attrDict.size}"
  let some symAttr := attrDict["sym_name".toUTF8]?
    | throw "include.from: missing 'sym_name' property"
  let .stringAttr sym := symAttr
    | throw s!"include.from: expected 'sym_name' to be a string attribute, got {symAttr}"
  let some pathAttr := attrDict["path".toUTF8]?
    | throw "include.from: missing 'path' property"
  let .stringAttr path := pathAttr
    | throw s!"include.from: expected 'path' to be a string attribute, got {pathAttr}"
  return { sym_name := sym, path := path }

end

end Veir
