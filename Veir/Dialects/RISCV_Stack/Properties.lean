module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of a fixed-size function-local stack object. `size` and
  `alignment` are expressed in bytes; assignment of the object's final frame
  offset is left to the backend.
-/
structure RISCVStackAllocaProperties where
  size : IntegerAttr
  alignment : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def RISCVStackAllocaProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String RISCVStackAllocaProperties := do
  let sizeAttr ← match attrDict["size".toUTF8]? with
    | some (.integerAttr sizeAttr) => .ok sizeAttr
    | some attr => .error s!"expected 'size' to be an integer attribute, but got {attr}"
    | none => .error "alloca: missing 'size' property"
  let alignAttr ← match attrDict["alignment".toUTF8]? with
    | some (.integerAttr alignAttr) => .ok alignAttr
    | some attr => .error s!"expected 'alignment' to be an integer attribute, but got {attr}"
    | none => .error "alloca: missing 'alignment' property"
  return { size := sizeAttr, alignment := alignAttr }

end

end Veir
