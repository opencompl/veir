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
  let invalid := "wasmssa.branch_if: attribute 'exitLevel' failed to satisfy constraint: \
    32-bit unsigned integer attribute"
  let exitLevel ← match attrDict["exitLevel".toUTF8]? with
    | some (.integerAttr n) => pure n
    | some _ => throw invalid
    | none => throw "wasmssa.branch_if: requires attribute 'exitLevel'"
  if exitLevel.type ≠ .unsigned 32 || exitLevel.value < 0 then
    throw invalid
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
    | some _ => throw "wasmssa.call: attribute 'callee' failed to satisfy constraint: \
        flat symbol reference attribute"
    | none => throw "wasmssa.call: requires attribute 'callee'"
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
    | some _ => throw "wasmssa.const: attribute 'value' failed to satisfy constraint: TypedAttr instance"
    | none => throw "wasmssa.const: requires attribute 'value'"
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
    | some _ => throw "wasmssa.extend: attribute 'bitsToTake' failed to satisfy constraint: \
        An Attribute containing a integer value"
    | none => throw "wasmssa.extend: requires attribute 'bitsToTake'"

  unless #[8, 16, 32].contains bitsToTake.value do
    throw s!"wasmssa.extend: extend op can only take 8, 16 or 32 bits. Got {bitsToTake.value}"
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
    | some _ => throw "wasmssa.func: attribute 'sym_name' failed to satisfy constraint: string attribute"
    | none => throw "wasmssa.func: requires attribute 'sym_name'"
  let funcType ← match attrDict["functionType".toUTF8]? with
    | some (.functionType ft) => pure ft
    | some _ => throw "wasmssa.func: attribute 'functionType' failed to satisfy constraint: \
        type attribute of function type"
    | none => throw "wasmssa.func: requires attribute 'functionType'"
  let extra := DictionaryAttr.fromArray
    (attrDict.toArray.filter fun (k, _) => k ≠ "sym_name".toUTF8 && k ≠ "functionType".toUTF8)
  return { sym_name := symName, function_type := funcType, extra }

def WasmSSAFuncProperties.toAttrDict (props : WasmSSAFuncProperties) : Std.HashMap ByteArray Attribute :=
  Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    dict := dict.insert "sym_name".toUTF8 (.stringAttr props.sym_name)
    dict := dict.insert "functionType".toUTF8 (.functionType props.function_type)
    dict

structure WasmSSALocalProperties where
  type : TypeAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def WasmSSALocalProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String WasmSSALocalProperties := do
  let type ← match attrDict["type".toUTF8]? with
    | some (.integerType t) => pure t
    | some _ => throw "wasmssa.local: attribute 'type' failed to satisfy constraint: type attribute of 32-bit signless integer or 64-bit signless integer" -- or 32-bit float or 64-bit float or 128-bit signless integer or Opaque type for function reference or Opaque type for external reference"
    | none => throw "requires attribute 'type'"
  return { type }

def WasmSSALocalProperties.toAttrDict (props : WasmSSALocalProperties) : Std.HashMap ByteArray Attribute :=
  Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    dict := dict.insert "type".toUTF8 props.type.val
    dict

end

end Veir
