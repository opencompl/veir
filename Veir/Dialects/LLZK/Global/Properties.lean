module

public import Veir.IR.Attribute
public import Veir.Dialects.Builtin.Properties

namespace Veir

public section

/-- Properties of `global.def`. -/
structure GlobalDefProperties where
  sym_name : StringAttr
  constant : Bool
  type : TypeAttr
  initial_value : Option Attribute
deriving Inhabited, Repr, Hashable, DecidableEq

/-- The global types currently represented by VeIR.
https://github.com/project-llzk/llzk-lib/blob/265d68f678ab15018e3f6253b85557fbaeac9c0d/lib/Util/TypeHelper.cpp#L516-L522 -/
def TypeAttr.isSupportedLLZKGlobalType (type : TypeAttr) : Bool :=
  match type.val with
  | .integerType intType => intType.bitwidth = 1
  | .indexType _ | .feltType _ | .stringType _ => true
  | _ => false

/-- Whether an attribute can initialize a supported LLZK global type.
https://github.com/project-llzk/llzk-lib/blob/265d68f678ab15018e3f6253b85557fbaeac9c0d/lib/Dialect/Global/IR/Ops.cpp#L99-L167 -/
def TypeAttr.acceptsLLZKGlobalInitializer (type : TypeAttr) (value : Attribute) : Bool :=
  match type.val, value with
  | .integerType intType, .integerAttr value =>
    intType.bitwidth = 1 && (value.value = 0 || value.value = 1)
  | .indexType _, .integerAttr _ => true
  | .feltType _, .feltConstAttr _ | .feltType _, .integerAttr _ => true
  | .stringType _, .stringAttr _ => true
  | _, _ => false

def GlobalDefProperties.verify (props : GlobalDefProperties) : Except String PUnit := do
  if !props.type.isSupportedLLZKGlobalType then
    throw s!"global.def: expected a supported LLZK global type, got {props.type}"
  match props.initial_value with
  | none =>
    if props.constant then
      throw "global.def: marked as 'constant' must be assigned an initial value"
  | some initialValue =>
    if !props.type.acceptsLLZKGlobalInitializer initialValue then
      throw s!"global.def: initial value {initialValue} is incompatible with type {props.type}"

def GlobalDefProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String GlobalDefProperties := do
  let some symAttr := attrDict["sym_name".toUTF8]?
    | throw "global.def: missing 'sym_name' property"
  let .stringAttr sym := symAttr
    | throw s!"global.def: expected 'sym_name' to be a string attribute, got {symAttr}"
  let constant ← getUnitAttr "constant" attrDict
  let some typeAttr := attrDict["type".toUTF8]?
    | throw "global.def: missing 'type' property"
  let typeAttr ← if h : typeAttr.isType = true then
    pure (typeAttr.asType h)
  else
    throw s!"global.def: expected 'type' to be a type attribute, got {typeAttr}"
  let initial_value := attrDict["initial_value".toUTF8]?
  -- Reject unrecognized keys.
  let expected := 2 + (if constant then 1 else 0) + (if initial_value.isSome then 1 else 0)
  if attrDict.size ≠ expected then
    throw s!"global.def: unexpected property keys (expected {expected}, got {attrDict.size})"
  let props := { sym_name := sym, constant, type := typeAttr, initial_value }
  props.verify
  return props

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
