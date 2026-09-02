module

public import Veir.IR.Attribute
public import Veir.IR.OpInfo
public import Veir.Dialects.Builtin.Properties

namespace Veir

public section

/-- Properties of the `struct.def` operation. -/
structure StructDefProperties where
  sym_name : StringAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def StructDefProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String StructDefProperties := do
  let some symAttr := attrDict["sym_name".toUTF8]?
    | throw "struct.def: missing 'sym_name' property"
  let .stringAttr sym := symAttr
    | throw s!"struct.def: expected 'sym_name' to be a string attribute, got {symAttr}"
  if attrDict.size ≠ 1 then
    throw s!"struct.def: expected only 'sym_name' property, got {attrDict.size} properties"
  return { sym_name := sym }

/-- Properties of the `struct.member` operation. -/
structure StructMemberProperties where
  sym_name : StringAttr
  type : Attribute
  column : Bool
  signal : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def StructMemberProperties.fromAttrDict (opName : String)
    (attrDict : Std.HashMap ByteArray Attribute) :
    Except String StructMemberProperties := do
  let some symAttr := attrDict["sym_name".toUTF8]?
    | throw s!"{opName}: missing 'sym_name' property"
  let .stringAttr sym := symAttr
    | throw s!"{opName}: expected 'sym_name' to be a string attribute, got {symAttr}"
  let some typeAttr := attrDict["type".toUTF8]?
    | throw s!"{opName}: missing 'type' property"
  let column ← getUnitAttr "column" attrDict
  let signal ← getUnitAttr "signal" attrDict
  let expected := 2 + (if column then 1 else 0) + (if signal then 1 else 0)
  if attrDict.size ≠ expected then
    throw s!"{opName}: unexpected property keys (expected {expected}, got {attrDict.size})"
  return { sym_name := sym, type := typeAttr, column, signal }

def StructMemberProperties.toAttrDict (props : StructMemberProperties) :
    Std.HashMap ByteArray Attribute := Id.run do
  let mut dict := Std.HashMap.emptyWithCapacity 4
  dict := dict.insert "sym_name".toUTF8 (Attribute.stringAttr props.sym_name)
  dict := dict.insert "type".toUTF8 props.type
  if props.column then
    dict := dict.insert "column".toUTF8 (Attribute.unitAttr UnitAttr.mk)
  if props.signal then
    dict := dict.insert "signal".toUTF8 (Attribute.unitAttr UnitAttr.mk)
  dict

/-- Properties of the `struct.readm` operation. -/
structure StructReadProperties where
  name_ref : FlatSymbolRefAttr
  tableOffset : Option Attribute
  numDimsPerMap : Option DenseArrayAttr
  mapOpGroupSizes : Option DenseArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def StructReadProperties.fromAttrDict (opName nameKey : String)
    (attrDict : Std.HashMap ByteArray Attribute) :
    Except String StructReadProperties := do
  let some refAttr := attrDict[nameKey.toUTF8]?
    | throw s!"{opName}: missing '{nameKey}' property"
  let .flatSymbolRefAttr ref := refAttr
    | throw s!"{opName}: expected '{nameKey}' to be a flat symbol ref, got {refAttr}"
  let tableOffset := attrDict["tableOffset".toUTF8]?
  let numDimsPerMap ← match attrDict["numDimsPerMap".toUTF8]? with
    | none => pure none
    | some (.denseArrayAttr arr) => pure (some arr)
    | some attr =>
      throw s!"{opName}: expected 'numDimsPerMap' to be a dense array attribute, got {attr}"
  let mapOpGroupSizes ← match attrDict["mapOpGroupSizes".toUTF8]? with
    | none => pure none
    | some (.denseArrayAttr arr) => pure (some arr)
    | some attr =>
      throw s!"{opName}: expected 'mapOpGroupSizes' to be a dense array attribute, got {attr}"
  let expected := 1 + (if tableOffset.isSome then 1 else 0)
    + (if numDimsPerMap.isSome then 1 else 0) + (if mapOpGroupSizes.isSome then 1 else 0)
  if attrDict.size ≠ expected then
    throw s!"{opName}: unexpected property keys (expected {expected}, got {attrDict.size})"
  return { name_ref := ref, tableOffset, numDimsPerMap, mapOpGroupSizes }

def StructReadProperties.toAttrDict (nameKey : String) (props : StructReadProperties) :
    Std.HashMap ByteArray Attribute := Id.run do
  let mut dict := Std.HashMap.emptyWithCapacity 4
  dict := dict.insert nameKey.toUTF8 (Attribute.flatSymbolRefAttr props.name_ref)
  if let some off := props.tableOffset then
    dict := dict.insert "tableOffset".toUTF8 off
  if let some arr := props.numDimsPerMap then
    dict := dict.insert "numDimsPerMap".toUTF8 (Attribute.denseArrayAttr arr)
  if let some arr := props.mapOpGroupSizes then
    dict := dict.insert "mapOpGroupSizes".toUTF8 (Attribute.denseArrayAttr arr)
  dict

/-- Properties of the `struct.writem` operation. -/
structure StructWriteProperties where
  name_ref : FlatSymbolRefAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def StructWriteProperties.fromAttrDict (opName nameKey : String)
    (attrDict : Std.HashMap ByteArray Attribute) :
    Except String StructWriteProperties := do
  if attrDict.size > 1 then
    throw s!"{opName}: expected only '{nameKey}' property, got {attrDict.size} properties"
  let some refAttr := attrDict[nameKey.toUTF8]?
    | throw s!"{opName}: missing '{nameKey}' property"
  let .flatSymbolRefAttr ref := refAttr
    | throw s!"{opName}: expected '{nameKey}' to be a flat symbol ref, got {refAttr}"
  return { name_ref := ref }

end

end Veir
