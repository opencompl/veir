module

namespace Veir

public section

/--
The `OpInfo` type class provides information about the properties of an
operation and how to hash, represent, and compare them for equality. It also
provides a type family `propertyOf` that maps an operation code to the type of
its properties
-/
class OpInfo (opCode: Type)
    extends Hashable opCode, Repr opCode, Inhabited opCode where
  propertiesOf : opCode → Type
  propertiesHash {op : opCode} : Hashable (propertiesOf op)
  propertiesDefault {op : opCode} : Inhabited (propertiesOf op)
  propertiesRepr {op : opCode} : Repr (propertiesOf op)
  propertiesDecideEq {op : opCode} : DecidableEq (propertiesOf op)
  decideEq : DecidableEq (opCode)

instance [OpInfo opCode] {op : opCode} : Hashable (OpInfo.propertiesOf op) where
  hash := OpInfo.propertiesHash.hash

instance [OpInfo opCode] {op : opCode} : Inhabited (OpInfo.propertiesOf op) where
  default := OpInfo.propertiesDefault.default

instance [OpInfo opCode] {op : opCode} : Repr (OpInfo.propertiesOf op) where
  reprPrec := OpInfo.propertiesRepr.reprPrec

instance [OpInfo opCode] : DecidableEq (opCode) :=
  OpInfo.decideEq

end -- public section

end Veir
