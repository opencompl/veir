module

namespace Veir

public section

/--
The `OpInfo` type class provides information about the properties of an
operation and how to hash, represent, and compare them for equality. It also
provides a type family `propertyOf` that maps an operation code to the type of
its properties
-/
class OpInfo (ops: Type)
    extends Hashable ops, Repr ops, Inhabited ops where
  propertiesOf : ops → Type
  propertiesHash {op : ops} : Hashable (propertiesOf op)
  propertiesDefault {op : ops} : Inhabited (propertiesOf op)
  propertiesRepr {op : ops} : Repr (propertiesOf op)
  propertiesDecideEq {op : ops} : DecidableEq (propertiesOf op)
  decideEq : DecidableEq (ops)

instance [OpInfo ops] {op : ops} : Hashable (OpInfo.propertiesOf op) where
  hash := OpInfo.propertiesHash.hash

instance [OpInfo ops] {op : ops} : Inhabited (OpInfo.propertiesOf op) where
  default := OpInfo.propertiesDefault.default

instance [OpInfo ops] {op : ops} : Repr (OpInfo.propertiesOf op) where
  reprPrec := OpInfo.propertiesRepr.reprPrec

instance [OpInfo ops] : DecidableEq (ops) :=
  OpInfo.decideEq

end -- public section

end Veir
