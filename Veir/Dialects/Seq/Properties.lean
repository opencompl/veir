module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of the `seq.firreg` operation.
-/
structure SeqFirRegProperties where
  name : StringAttr
  isAsync : Bool
  preset : Option IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def SeqFirRegProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String SeqFirRegProperties := do
  let some name := attrDict["name".toUTF8]? | throw "seq.firreg: requires attribute 'name'"
  let .stringAttr name := name
    | throw s!"seq.firreg: expected 'name' to be a string attribute, but got {name}"

  let isAsync := attrDict.contains "isAsync".toUTF8

  let preset ← match attrDict["preset".toUTF8]? with
    | none => pure none
    | some (.integerAttr i) => pure (some i)
    | some other => throw s!"seq.firreg: expected 'preset' to be an integer attribute, but got {other}"

  return { name, isAsync, preset }

end

end Veir
