module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of `func.func`. Its required `sym_name` and `function_type`
  attributes are modelled explicitly; all other attributes are preserved
  verbatim in `extra`.
-/
structure FuncFuncProperties where
  sym_name : StringAttr
  function_type : FunctionType
  extra : DictionaryAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def FuncFuncProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String FuncFuncProperties := do
  let symName ← match attrDict["sym_name".toUTF8]? with
    | some (.stringAttr s) => pure s
    | some attr => throw s!"func.func: expected 'sym_name' to be a string attribute, but got {attr}"
    | none => throw "func.func: missing 'sym_name' property"
  let funcType ← match attrDict["function_type".toUTF8]? with
    | some (.functionType ft) => pure ft
    | some attr =>
      throw s!"func.func: expected 'function_type' to be a function type, but got {attr}"
    | none => throw "func.func: missing 'function_type' property"
  let extra := DictionaryAttr.fromArray
    (attrDict.toArray.filter fun (k, _) => k ≠ "sym_name".toUTF8 && k ≠ "function_type".toUTF8)
  return { sym_name := symName, function_type := funcType, extra }

/--
  Properties of the `func.call` operation. The `callee` is first-class; all
  other attributes are kept verbatim in `extra`. `func.call` is never indirect,
  so `callee` is required.
-/
structure FuncCallProperties where
  callee : FlatSymbolRefAttr
  extra : DictionaryAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def FuncCallProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String FuncCallProperties := do
  let callee ← match attrDict["callee".toUTF8]? with
    | some (.flatSymbolRefAttr s) => pure s
    | some attr => throw s!"func.call: expected 'callee' to be a flat symbol reference, but got {attr}"
    | none => throw "func.call: expected a 'callee' symbol reference"
  let extra := DictionaryAttr.fromArray
    (attrDict.toArray.filter fun (k, _) => k ≠ "callee".toUTF8)
  return { callee, extra }

end

end Veir
