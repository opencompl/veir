module

public import Veir.IR.Attribute
public import Std.Data.HashMap

import Veir.Dialects.Builtin.Properties

namespace Veir

public section

/--
  Properties of a fixed-size function-local stack object. `size` and
  `alignment` are expressed in bytes; assignment of the object's final frame
  offset is left to the backend.
-/
structure RISCVStackAllocaProperties where
  size : BitVec 64
  alignment : BitVec 64
deriving Inhabited, Repr, Hashable, DecidableEq

def RISCVStackAllocaProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String RISCVStackAllocaProperties := do
  let size ← getI64Attr "alloca" "size" attrDict
  let alignment ← getI64Attr "alloca" "alignment" attrDict
  return { size, alignment }

end

end Veir
