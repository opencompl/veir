module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of the `memref.global` operation.
-/
structure MemRefGlobalProperties where
  sym_name : StringAttr
  type : TypeAttr
  extra : DictionaryAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def MemRefGlobalProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String MemRefGlobalProperties := do
  let symName ← match attrDict["sym_name".toUTF8]? with
    | some (.stringAttr attr) => pure attr
    | some attr =>
      throw s!"memref.global: expected 'sym_name' to be a string attribute, but got {attr}"
    | none => throw "memref.global: missing 'sym_name' property"
  let type ← match attrDict["type".toUTF8]? with
    | some attr =>
      if _ : attr.isType = false then
        throw "memref.global: expected 'type' to be a type attribute"
      else
        pure attr.asType
    | none => throw "memref.global: missing 'type' property"
  let extra := DictionaryAttr.fromArray
    (attrDict.toArray.filter fun (k, _) => k ≠ "sym_name".toUTF8 ∧ k ≠ "type".toUTF8)
  return { sym_name := symName, type, extra }

/--
  Properties of the `memref.get_global` operation: `name` is the symbol of the
  `memref.global` whose memref is produced.
-/
structure MemRefGetGlobalProperties where
  name : FlatSymbolRefAttr
  extra : DictionaryAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def MemRefGetGlobalProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String MemRefGetGlobalProperties := do
  let name ← match attrDict["name".toUTF8]? with
    | some (.flatSymbolRefAttr attr) => pure attr
    | some attr =>
      throw s!"memref.get_global: expected 'name' to be a flat symbol reference, but got {attr}"
    | none => throw "memref.get_global: missing 'name' property"
  let extra := DictionaryAttr.fromArray
    (attrDict.toArray.filter fun (k, _) => k ≠ "name".toUTF8)
  return { name, extra }

end

end Veir
