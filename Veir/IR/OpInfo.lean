module

namespace Veir

/--
The `OpInfo` type class provides information about the properties of an
operation and how to hash, represent, and compare them for equality. It also
provides a type family `propertyOf` that maps an operation code to the type of
its properties
-/
public class OpInfo (ops: Type)
    extends Hashable ops, Repr ops, Inhabited ops where
  propertyOf : ops → Type
  propertyHash {op : ops} : Hashable (propertyOf op)
  propertyDefault {op : ops} : Inhabited (propertyOf op)
  propertyRepr {op : ops} : Repr (propertyOf op)
  propertyDecideEq {op : ops} : DecidableEq (propertyOf op)
  decideEq : DecidableEq (ops)

instance [OpInfo ops] {op : ops} :
    Hashable (OpInfo.propertyOf op) where
  hash props := OpInfo.propertyHash.hash props

instance [OpInfo ops] {op : ops} :
    Inhabited (OpInfo.propertyOf op) where
  default := OpInfo.propertyDefault.default

instance [OpInfo ops] {op : ops} :
    Repr (OpInfo.propertyOf op) where
  reprPrec props prec := OpInfo.propertyRepr.reprPrec props prec

instance [OpInfo ops] : DecidableEq (ops) :=
  OpInfo.decideEq

end Veir
