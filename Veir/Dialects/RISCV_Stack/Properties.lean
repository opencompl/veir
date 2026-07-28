module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

structure RISCVStackAllocaProperties where
  alignment : IntegerAttr
  value_type : TypeAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def RISCVStackAllocaProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String RISCVStackAllocaProperties := do
  let alignAttr ← match attrDict["alignment".toUTF8]? with
    | some (.integerAttr alignAttr) => .ok alignAttr
    | some attr => .error s!"expected 'alignment' to be an optional integer attribute, but got {attr}"
    | none => .ok { value := 0, type := { bitwidth := 64 } }
  let some typeAttr := attrDict["value_type".toUTF8]?
    | throw "alloca: missing 'value_type' property"
  if _ : typeAttr.isType = false then throw "alloca: expected 'value_type' to be a type attribute" else
  return { alignment := alignAttr, value_type := typeAttr.asType }

end

end Veir
