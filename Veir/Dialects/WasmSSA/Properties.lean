module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/-! ## Properties -/

structure WasmSSABranchIfProperties where
  exitLevel : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def WasmSSABranchIfProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String WasmSSABranchIfProperties := do
  let exitLevel ← match attrDict["exitLevel".toUTF8]? with
    | some (.integerAttr n) => pure n
    | some attr => throw s!"wasmssa.branch_if: expected 'exitLevel' to be an integer, but got {attr}"
    | none => throw "wasmssa.branch_if: missing 'exitLevel' property"
  return { exitLevel }

def WasmSSABranchIfProperties.toAttrDict (props : WasmSSABranchIfProperties) : Std.HashMap ByteArray Attribute :=
  Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    dict := dict.insert "exitLevel".toUTF8 (.integerAttr props.exitLevel)
    dict

structure WasmSSACallProperties where
  callee : FlatSymbolRefAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def WasmSSACallProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String WasmSSACallProperties := do
  let callee ← match attrDict["callee".toUTF8]? with
    | some (.flatSymbolRefAttr a) => pure a
    | some attr => throw s!"wasmssa.call: expected 'callee' to be a symbol name, but got {attr}"
    | none => throw "wasmssa.call: missing 'callee' property"
  return { callee }

def WasmSSACallProperties.toAttrDict (props : WasmSSACallProperties) : Std.HashMap ByteArray Attribute :=
  Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    dict := dict.insert "callee".toUTF8 (.flatSymbolRefAttr props.callee)
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
  return { value }

def WasmSSAConstProperties.toAttrDict (props : WasmSSAConstProperties) : Std.HashMap ByteArray Attribute :=
  Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    dict := dict.insert "value".toUTF8 (.integerAttr props.value)
    dict

structure WasmSSAExtendProperties where
  bitsToTake : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def WasmSSAExtendProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String WasmSSAExtendProperties := do
  let bitsToTake ← match attrDict["bitsToTake".toUTF8]? with
    | some (.integerAttr n) => pure n
    | some attr => throw s!"wasmssa.extend: Expected 'bitsToTake' to be an integer, but got {attr}"
    | none => throw "wasmssa.extend: missing 'bitstoTake' property"
  if bitsToTake.value < 0 then
    throw "wasmssa.extend: Expected positive value for 'bitsToTake'"
  return { bitsToTake }

def WasmSSAExtendProperties.toAttrDict (props : WasmSSAExtendProperties) : Std.HashMap ByteArray Attribute :=
  Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    dict := dict.insert "bitsToTake".toUTF8 (.integerAttr props.bitsToTake)
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
      throw s!"wasmssa.func: expected 'functionType' to be a MLIR functionType, but got {attr}"
    | none => throw "wasmssa.func: missing functionType property"
  let extra := DictionaryAttr.fromArray
    (attrDict.toArray.filter fun (k, _) => k ≠ "sym_name".toUTF8 && k ≠ "functionType".toUTF8)
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
