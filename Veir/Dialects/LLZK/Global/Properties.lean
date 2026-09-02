module

public import Veir.IR.Attribute
public import Veir.Dialects.Builtin.Properties

namespace Veir

public section

/-- Properties of `global.def`.

The parent, symbol uniqueness, and symbol-use constraints are not verified.
-/
structure GlobalDefProperties where
  sym_name : StringAttr
  constant : Bool
  type : Attribute
  initial_value : Option Attribute
deriving Inhabited, Repr, Hashable, DecidableEq

def GlobalDefProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String GlobalDefProperties := do
  let some symAttr := attrDict["sym_name".toUTF8]?
    | throw "global.def: missing 'sym_name' property"
  let .stringAttr sym := symAttr
    | throw s!"global.def: expected 'sym_name' to be a string attribute, got {symAttr}"
  let constant ← getUnitAttr "constant" attrDict
  let some typeAttr := attrDict["type".toUTF8]?
    | throw "global.def: missing 'type' property"
  let initial_value := attrDict["initial_value".toUTF8]?
  -- Reject unrecognized keys.
  let expected := 2 + (if constant then 1 else 0) + (if initial_value.isSome then 1 else 0)
  if attrDict.size ≠ expected then
    throw s!"global.def: unexpected property keys (expected {expected}, got {attrDict.size})"
  return { sym_name := sym, constant := constant, type := typeAttr, initial_value := initial_value }

/-- Properties of `global.read` and `global.write`.

Only flat symbol references are supported.
-/
structure GlobalRefProperties where
  name_ref : FlatSymbolRefAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def GlobalRefProperties.fromAttrDict (opName : String) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String GlobalRefProperties := do
  if attrDict.size > 1 then
    throw s!"{opName}: expected only 'name_ref' property, got {attrDict.size} properties"
  let some refAttr := attrDict["name_ref".toUTF8]?
    | throw s!"{opName}: missing 'name_ref' property"
  let .flatSymbolRefAttr ref := refAttr
    | throw s!"{opName}: expected 'name_ref' to be a flat symbol ref, got {refAttr}"
  return { name_ref := ref }

end

end Veir
