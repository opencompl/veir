module

namespace Veir

public section

/--
The `HasOpInfo` type class provides information about opcodes and their properties
and how to hash, represent, and compare them for equality. It also
provides a type family `propertyOf` that maps an operation code to the type of
its properties
-/
class HasOpInfo (opCode: Type)
    extends Hashable opCode, Repr opCode, Inhabited opCode where
  propertiesOf : opCode → Type
  propertiesHash {op : opCode} : Hashable (propertiesOf op)
  propertiesDefault {op : opCode} : Inhabited (propertiesOf op)
  propertiesRepr {op : opCode} : Repr (propertiesOf op)
  propertiesDecideEq {op : opCode} : DecidableEq (propertiesOf op)
  decideEq : DecidableEq (opCode)

instance [HasOpInfo opCode] {op : opCode} : Hashable (HasOpInfo.propertiesOf op) where
  hash := HasOpInfo.propertiesHash.hash

instance [HasOpInfo opCode] {op : opCode} : Inhabited (HasOpInfo.propertiesOf op) where
  default := HasOpInfo.propertiesDefault.default

instance [HasOpInfo opCode] {op : opCode} : Repr (HasOpInfo.propertiesOf op) where
  reprPrec := HasOpInfo.propertiesRepr.reprPrec

instance [HasOpInfo opCode] : DecidableEq (opCode) :=
  HasOpInfo.decideEq

end -- public section

end Veir
