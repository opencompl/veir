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
  predicate : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def BoolCmpProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String BoolCmpProperties := do
  if attrDict.size > 1 then
    throw s!"bool.cmp: expected only 'predicate' property, got {attrDict.size}"
  let some attr := attrDict["predicate".toUTF8]?
    | throw "bool.cmp: missing 'predicate' property"
  let value ← match attr with
    | .integerAttr intAttr => pure intAttr
    | .boolCmpPredicateAttr pred =>
      pure ({ value := pred.value, type := { bitwidth := 32 } } : IntegerAttr)
    | _ =>
      throw s!"bool.cmp: expected 'predicate' to be an integer attribute or #bool<...>, got {attr}"
  if value.type.bitwidth ≠ 32 then
    throw s!"bool.cmp: 'predicate' must have type i32, got i{value.type.bitwidth}"
  if value.value < 0 ∨ value.value > 5 then
    throw s!"bool.cmp: 'predicate' must be in 0..5 (eq/ne/lt/le/gt/ge), got {value.value}"
  return { predicate := value }

def BoolCmpProperties.predicateAttr (props : BoolCmpProperties) : Attribute :=
  Attribute.boolCmpPredicateAttr { value := props.predicate.value }

end

end Veir
