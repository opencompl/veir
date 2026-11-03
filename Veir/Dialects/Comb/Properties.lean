module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of the `comb.extract` operation.
-/
structure CombExtractProperties where
  lowBit : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def CombExtractProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String CombExtractProperties := do
  if attrDict.size > 1 then
    throw s!"comb.extract: expected only one property, but got {attrDict.size} properties"
  let some attr := attrDict["lowBit".toUTF8]?
    | throw "comb.extract: missing 'lowBit' property"
  let .integerAttr intAttr := attr
    | throw s!"comb.extract: expected 'lowBit' to be an integer attribute, but got {attr}"
  return { lowBit := intAttr }

/--
  Properties of `comb.icmp` operation, describing predicates for integer comparison.
-/
structure CombIcmpProperties where
  predicate : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def CombIcmpProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String CombIcmpProperties := do
  if attrDict.size > 1 then
    throw s!"comb.icmp: expected only one property, but got {attrDict.size} properties"
  let some attr := attrDict["predicate".toUTF8]?
    | throw "comb.icmp: missing 'predicate' property"
  let .integerAttr intAttr := attr
    | throw s!"comb.icmp: expected 'predicate' to be an integer attribute, but got {attr}"
  return { predicate := intAttr }

end

end Veir
