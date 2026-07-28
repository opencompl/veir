module

public import Veir.IR.Attribute
public import Std.Data.HashMap

/- This is needed as some properties have ByteArray and require Repr instances -/
deriving instance Repr for ByteArray

namespace Veir

public section

/--
  Properties of a `builtin.unregistered` operation. Holds the original (parsed) operation name
  and the original `<{...}>` properties dictionary so that the operation can be printed back
  with its source representation preserved.
-/
structure UnregisteredProperties where
  opName : ByteArray
  properties : DictionaryAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def UnregisteredProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String UnregisteredProperties :=
  .ok { opName := .empty, properties := DictionaryAttr.fromArray attrDict.toArray }

def getUnitAttr (key : String) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String Bool := do
  match attrDict[key.toUTF8]? with
  | some (.unitAttr _) => .ok true
  | some attr => .error s!"expected '{key}' to be an optional unit attribute, but got {attr}"
  | none => .ok false

end

end Veir
