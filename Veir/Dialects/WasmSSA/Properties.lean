module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/-! ## Properties -/

structure WasmSSACallProperties where
  callee : StringAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def WasmSSACallProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String WasmSSACallProperties := do
  let value ← match attrDict["callee".toUTF8]? with
    | some (.stringAttr a) => pure a
    | some attr => throw s!"wasmssa.call: expected 'callee' to be a symbol name, but got {attr}"
    | none => throw "wasmssa.call: missing callee property"
  return { callee := value }

def WasmSSACallProperties.toAttrDict (props : WasmSSACallProperties) : Std.HashMap ByteArray Attribute :=
  Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    dict := dict.insert "callee".toUTF8 (.stringAttr props.callee)
    dict

structure WasmSSAConstProperties where
  value : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def WasmSSAConstProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String WasmSSAConstProperties := do
  let value ← match attrDict["value".toUTF8]? with
    | some (.integerAttr a) => pure a
    | some attr => throw s!"wasmssa.const: expected 'value' to be a typed attribute, but got {attr}"
    | none => throw "wasmssa.const: missing 'value' property"
  return { value := value }

def WasmSSAConstProperties.toAttrDict (props : WasmSSAConstProperties) : Std.HashMap ByteArray Attribute :=
  Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    dict := dict.insert "value".toUTF8 (.integerAttr props.value)
    dict

/--
  Properties of `wasmssa.func`. Its `sym_name` and `function_type` are modelled explicitly;
  every other attribute (arg_attrs, res_atrs, exported, ...) is preserved
  verbatim in `extra`.
-/
structure WasmSSAFuncProperties where
  sym_name : StringAttr
  function_type : FunctionType
  extra : DictionaryAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def WasmSSAFuncProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String WasmSSAFuncProperties := do
  let symName ← match attrDict["sym_name".toUTF8]? with
    | some (.stringAttr s) => pure s
    | some attr => throw s!"wasmssa.func: expected 'sym_name' to be a string attribute, but got {attr}"
    | none => throw "wasmssa.func: missing 'sym_name' property"
  let funcType ← match attrDict["functionType".toUTF8]? with
    | some (.functionType ft) => pure ft
    | some attr =>
      throw s!"cir.func: expected 'functionType' to be a MLIR functionType, but got {attr}"
    | none => throw "wasmssa.func: missing functionType property"
  let extra := DictionaryAttr.fromArray
    (attrDict.toArray.filter fun (k, _) => k ≠ "sym_name".toUTF8 && k ≠ "function_type".toUTF8)
  return { sym_name := symName, function_type := funcType, extra }

/-! ## Attribute dictionaries -/

def WasmSSAFuncProperties.toAttrDict (props : WasmSSAFuncProperties) : Std.HashMap ByteArray Attribute :=
  Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    dict := dict.insert "sym_name".toUTF8 (.stringAttr props.sym_name)
    dict := dict.insert "functionType".toUTF8 (.functionType props.function_type)
    dict

end

end Veir
