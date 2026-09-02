module

public import Veir.IR.Attribute

namespace Veir

public section

/-- Properties of `function.def`.

`arg_attrs` and `res_attrs` are not supported.
-/
structure FunctionDefProperties where
  sym_name : StringAttr
  function_type : FunctionType
deriving Inhabited, Repr, Hashable, DecidableEq

def FunctionDefProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String FunctionDefProperties := do
  let some symAttr := attrDict["sym_name".toUTF8]?
    | throw "function.def: missing 'sym_name' property"
  let .stringAttr sym := symAttr
    | throw s!"function.def: expected 'sym_name' to be a string attribute, got {symAttr}"
  let some ftAttr := attrDict["function_type".toUTF8]?
    | throw "function.def: missing 'function_type' property"
  let .functionType ft := ftAttr
    | throw s!"function.def: expected 'function_type' to be a function type, got {ftAttr}"
  return { sym_name := sym, function_type := ft }

/-- Properties of the `function.call` operation. -/
structure FunctionCallProperties where
  callee : SymbolRefAttr
  operandSegmentSizes : Option DenseArrayAttr
  numDimsPerMap : Option DenseArrayAttr
  mapOpGroupSizes : Option DenseArrayAttr
  templateParams : Option ArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def FunctionCallProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String FunctionCallProperties := do
  let callee ← match attrDict["callee".toUTF8]? with
    | some (.symbolRefAttr ref) => pure ref
    | some (.flatSymbolRefAttr flat) => pure { rootRef := flat.value, nestedRefs := #[] }
    | some attr =>
      throw s!"function.call: expected 'callee' to be a symbol reference, got {attr}"
    | none => throw "function.call: missing 'callee' property"
  let getDense (key : String) : Except String (Option DenseArrayAttr) := do
    match attrDict[key.toUTF8]? with
    | none => return none
    | some (.denseArrayAttr arr) => return (some arr)
    | some attr =>
      throw s!"function.call: expected '{key}' to be a dense array attribute, got {attr}"
  let operandSegmentSizes ← getDense "operandSegmentSizes"
  let numDimsPerMap ← getDense "numDimsPerMap"
  let mapOpGroupSizes ← getDense "mapOpGroupSizes"
  let templateParams ← match attrDict["templateParams".toUTF8]? with
    | none => pure none
    | some (.arrayAttr arr) => pure (some arr)
    | some attr =>
      throw s!"function.call: expected 'templateParams' to be an array attribute, got {attr}"
  let expected := 1 + (if operandSegmentSizes.isSome then 1 else 0)
    + (if numDimsPerMap.isSome then 1 else 0) + (if mapOpGroupSizes.isSome then 1 else 0)
    + (if templateParams.isSome then 1 else 0)
  if attrDict.size ≠ expected then
    throw s!"function.call: unexpected property keys (expected {expected}, got {attrDict.size})"
  return { callee, operandSegmentSizes, numDimsPerMap, mapOpGroupSizes, templateParams }

def FunctionCallProperties.toAttrDict (props : FunctionCallProperties) :
    Std.HashMap ByteArray Attribute := Id.run do
  let mut dict := Std.HashMap.emptyWithCapacity 5
  dict := dict.insert "callee".toUTF8 (Attribute.symbolRefAttr props.callee)
  if let some arr := props.operandSegmentSizes then
    dict := dict.insert "operandSegmentSizes".toUTF8 (Attribute.denseArrayAttr arr)
  if let some arr := props.numDimsPerMap then
    dict := dict.insert "numDimsPerMap".toUTF8 (Attribute.denseArrayAttr arr)
  if let some arr := props.mapOpGroupSizes then
    dict := dict.insert "mapOpGroupSizes".toUTF8 (Attribute.denseArrayAttr arr)
  if let some arr := props.templateParams then
    dict := dict.insert "templateParams".toUTF8 (Attribute.arrayAttr arr)
  dict

end

end Veir
