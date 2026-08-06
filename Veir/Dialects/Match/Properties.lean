module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of the `match.constant_attribute` operation.

  `value` is the constant attribute the handle stands for. Unlike
  `pdl.attribute`, it is mandatory: the operation exists precisely to give a
  literal a value of its own.
-/
structure MatchConstantAttributeProperties where
  value : Attribute
deriving Inhabited, Repr, Hashable, DecidableEq

def MatchConstantAttributeProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String MatchConstantAttributeProperties := do
  let some value := attrDict["value".toUTF8]?
    | throw "match.constant_attribute: missing 'value' property"
  if attrDict.size > 1 then
    throw s!"match.constant_attribute: expected only the 'value' property, \
             but got {attrDict.size} properties"
  return { value }

/--
  Properties of the `match.constant_type` operation.
-/
structure MatchConstantTypeProperties where
  value : TypeAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def MatchConstantTypeProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String MatchConstantTypeProperties := do
  let some attr := attrDict["value".toUTF8]?
    | throw "match.constant_type: missing 'value' property"
  if _ : attr.isType = false then
    throw s!"match.constant_type: expected 'value' to be a type attribute, but got {attr}"
  else
    if attrDict.size > 1 then
      throw s!"match.constant_type: expected only the 'value' property, \
               but got {attrDict.size} properties"
    return { value := attr.asType }

/--
  Properties of the `match.constant_types` operation.

  `value` is the array of constant types the range stands for.
-/
structure MatchConstantTypesProperties where
  value : ArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def MatchConstantTypesProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String MatchConstantTypesProperties := do
  let some attr := attrDict["value".toUTF8]?
    | throw "match.constant_types: missing 'value' property"
  let .arrayAttr value := attr
    | throw s!"match.constant_types: expected 'value' to be an array attribute, but got {attr}"
  for element in value.value do
    if element.isType = false then
      throw s!"match.constant_types: expected 'value' to hold types, but got {element}"
  if attrDict.size > 1 then
    throw s!"match.constant_types: expected only the 'value' property, \
             but got {attrDict.size} properties"
  return { value }

/--
  Properties of the operations that index a single operand or result:
  `match.get_operand` and `match.get_result`.

  `index` is mandatory, which is what separates these from the `*s` forms below.
-/
structure MatchIndexProperties where
  index : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def MatchIndexProperties.fromAttrDict (opName : String)
    (attrDict : Std.HashMap ByteArray Attribute) :
    Except String MatchIndexProperties := do
  let some attr := attrDict["index".toUTF8]?
    | throw s!"{opName}: missing 'index' property"
  let .integerAttr index := attr
    | throw s!"{opName}: expected 'index' to be an integer attribute, but got {attr}"
  if index.value < 0 then
    throw s!"{opName}: expected 'index' to be non-negative, but got {index.value}"
  if attrDict.size > 1 then
    throw s!"{opName}: expected only the 'index' property, but got {attrDict.size} properties"
  return { index }

/--
  Properties of the operations that index a *group* of operands or results:
  `match.get_operands` and `match.get_results`.

  `index` is optional; when absent the operation stands for the whole list.
-/
structure MatchOptionalIndexProperties where
  index : Option IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def MatchOptionalIndexProperties.fromAttrDict (opName : String)
    (attrDict : Std.HashMap ByteArray Attribute) :
    Except String MatchOptionalIndexProperties := do
  let index ← match attrDict["index".toUTF8]? with
    | some (.integerAttr index) =>
      if index.value < 0 then
        throw s!"{opName}: expected 'index' to be non-negative, but got {index.value}"
      pure (some index)
    | some attr =>
      throw s!"{opName}: expected 'index' to be an integer attribute, but got {attr}"
    | none => pure none
  if attrDict.size > (if index.isSome then 1 else 0) then
    throw s!"{opName}: expected only the 'index' property, but got {attrDict.size} properties"
  return { index }

/--
  Properties of the `match.get_attribute` operation.

  `name` is the name of the attribute to look up on the operation.
-/
structure MatchGetAttributeProperties where
  name : StringAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def MatchGetAttributeProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String MatchGetAttributeProperties := do
  let some attr := attrDict["name".toUTF8]?
    | throw "match.get_attribute: missing 'name' property"
  let .stringAttr name := attr
    | throw s!"match.get_attribute: expected 'name' to be a string attribute, but got {attr}"
  if attrDict.size > 1 then
    throw s!"match.get_attribute: expected only the 'name' property, \
             but got {attrDict.size} properties"
  return { name }

end

end Veir
