module

public import Veir.IR.Attribute

namespace Veir

public section

/-- Properties of the `bool.assert` operation. -/
structure BoolAssertProperties where
  msg : Option StringAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def BoolAssertProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String BoolAssertProperties := do
  if attrDict.size > 1 then
    throw s!"bool.assert: expected at most 'msg' property, got {attrDict.size}"
  let msg ← match attrDict["msg".toUTF8]? with
    | some (.stringAttr m) => .ok (some m)
    | some attr => .error s!"bool.assert: expected 'msg' to be a string attribute, got {attr}"
    | none => .ok none
  if attrDict.size = 1 ∧ msg.isNone then
    throw "bool.assert: only 'msg' is a recognized property"
  return { msg := msg }

/-- Properties of the `bool.cmp` operation. -/
structure BoolCmpProperties where
  predicate : BoolCmpPredicateAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def BoolCmpProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String BoolCmpProperties := do
  if attrDict.size > 1 then
    throw s!"bool.cmp: expected only 'predicate' property, got {attrDict.size}"
  let some attr := attrDict["predicate".toUTF8]?
    | throw "bool.cmp: missing 'predicate' property"
  let .boolCmpPredicateAttr predicate := attr
    | throw s!"bool.cmp: expected 'predicate' to be a #bool<cmp ...> attribute, got {attr}"
  return { predicate }

def BoolCmpProperties.predicateAttr (props : BoolCmpProperties) : Attribute :=
  Attribute.boolCmpPredicateAttr props.predicate

end

end Veir
