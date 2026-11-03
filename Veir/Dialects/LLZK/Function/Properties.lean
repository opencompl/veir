module

public import Veir.IR.Attribute

namespace Veir

public section

/-- Properties of `function.def`.

The required symbol name and function type are modelled explicitly; argument,
result, and dialect attributes are preserved in `extra`.
-/
structure FunctionDefProperties where
  sym_name : StringAttr
  function_type : FunctionType
  extra : DictionaryAttr
deriving Inhabited, Repr, Hashable, DecidableEq

/-- Port of LLZK's `verifyArgOrResNameAttrs`:
https://github.com/project-llzk/llzk-lib/blob/265d68f678ab15018e3f6253b85557fbaeac9c0d/lib/Dialect/Function/IR/Ops.cpp#L73-L121 -/
private def validateFunctionMetadataArray (key ownName crossName ownLabel crossLabel : String)
    (expectedSize : Nat) (attrDict : Std.HashMap ByteArray Attribute) : Except String Unit := do
  let some attr := attrDict[key.toUTF8]? | return
  let .arrayAttr attrs := attr
    | throw s!"function.def: expected '{key}' to be an array attribute, got {attr}"
  if attrs.value.size != expectedSize then
    throw s!"function.def: '{key}' expected {expectedSize} entries, got {attrs.value.size}"
  let mut seenNames : Std.HashMap ByteArray Unit := Std.HashMap.emptyWithCapacity
  for i in [0:attrs.value.size] do
    let .dictionaryAttr dict := attrs.value[i]!
      | throw s!"function.def: '{key}' entry {i} must be a dictionary attribute"
    for (name, value) in dict.entries do
      if name = crossName.toUTF8 then
        throw s!"function.def: '{crossName}' is only valid on function {crossLabel}s but found on {ownLabel} {i}"
      if name = ownName.toUTF8 then
        let .stringAttr str := value
          | throw s!"function.def: '{ownName}' on {ownLabel} {i} must be a string attribute"
        if str.value.isEmpty then
          throw s!"function.def: '{ownName}' on {ownLabel} {i} must not be empty"
        if seenNames.contains str.value then
          throw s!"function.def: duplicate '{ownName}' value on {ownLabel} {i}"
        seenNames := seenNames.insert str.value ()

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
  validateFunctionMetadataArray "arg_attrs" "function.arg_name" "function.res_name"
    "argument" "result" ft.inputs.size attrDict
  validateFunctionMetadataArray "res_attrs" "function.res_name" "function.arg_name"
    "result" "argument" ft.outputs.size attrDict
  let extra := DictionaryAttr.fromArray
    (attrDict.toArray.filter fun (key, _) =>
      key ≠ "sym_name".toUTF8 && key ≠ "function_type".toUTF8)
  return { sym_name := sym, function_type := ft, extra }

/-- Properties of the `function.call` operation. -/
structure FunctionCallProperties where
  callee : FlatSymbolRefAttr
  operandSegmentSizes : DenseArrayAttr
  numDimsPerMap : Option DenseArrayAttr
  mapOpGroupSizes : DenseArrayAttr
  templateParams : Option ArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def FunctionCallProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String FunctionCallProperties := do
  let callee ← match attrDict["callee".toUTF8]? with
    | some (.flatSymbolRefAttr ref) => pure ref
    | some attr =>
      throw s!"function.call: expected 'callee' to be a flat symbol reference, got {attr}"
    | none => throw "function.call: missing 'callee' property"
  let getDense (key : String) : Except String DenseArrayAttr := do
    match attrDict[key.toUTF8]? with
    | none => throw s!"function.call: missing '{key}' property"
    | some (.denseArrayAttr arr) =>
      -- These properties are `DenseI32ArrayAttr` in LLZK's `CallOp` definition:
      -- https://github.com/project-llzk/llzk-lib/blob/265d68f678ab15018e3f6253b85557fbaeac9c0d/include/llzk/Dialect/Function/IR/Ops.td#L355-L372
      if arr.elementType.bitwidth != 32 then
        throw s!"function.call: expected '{key}' to be an array<i32> attribute, got array<i{arr.elementType.bitwidth}>"
      return arr
    | some attr =>
      throw s!"function.call: expected '{key}' to be a dense array attribute, got {attr}"
  let operandSegmentSizes ← getDense "operandSegmentSizes"
  let mapOpGroupSizes ← getDense "mapOpGroupSizes"
  let numDimsPerMap ← match attrDict["numDimsPerMap".toUTF8]? with
    | none => pure none
    | some (.denseArrayAttr arr) =>
      if arr.elementType.bitwidth != 32 then
        throw s!"function.call: expected 'numDimsPerMap' to be an array<i32> attribute, got array<i{arr.elementType.bitwidth}>"
      pure (some arr)
    | some attr =>
      throw s!"function.call: expected 'numDimsPerMap' to be a dense array attribute, got {attr}"
  let templateParams ← match attrDict["templateParams".toUTF8]? with
    | none => pure none
    | some (.arrayAttr arr) => pure (some arr)
    | some attr =>
      throw s!"function.call: expected 'templateParams' to be an array attribute, got {attr}"
  let expected := 3 + (if numDimsPerMap.isSome then 1 else 0)
    + (if templateParams.isSome then 1 else 0)
  if attrDict.size ≠ expected then
    throw s!"function.call: unexpected property keys (expected {expected}, got {attrDict.size})"
  return { callee, operandSegmentSizes, numDimsPerMap, mapOpGroupSizes, templateParams }

def FunctionCallProperties.toAttrDict (props : FunctionCallProperties) :
    Std.HashMap ByteArray Attribute := Id.run do
  let mut dict := Std.HashMap.emptyWithCapacity 5
  dict := dict.insert "callee".toUTF8 (Attribute.flatSymbolRefAttr props.callee)
  dict := dict.insert "operandSegmentSizes".toUTF8
    (Attribute.denseArrayAttr props.operandSegmentSizes)
  dict := dict.insert "mapOpGroupSizes".toUTF8
    (Attribute.denseArrayAttr props.mapOpGroupSizes)
  if let some arr := props.numDimsPerMap then
    dict := dict.insert "numDimsPerMap".toUTF8 (Attribute.denseArrayAttr arr)
  if let some arr := props.templateParams then
    dict := dict.insert "templateParams".toUTF8 (Attribute.arrayAttr arr)
  dict

end

end Veir
