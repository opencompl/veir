module

public import Veir.IR.Attribute
public import Veir.Properties

namespace Veir

public section

/--
  Properties of the `function.def` operation (Phase F.5).

  Carries the two required attributes:

  - `sym_name : StringAttr` per LLZK's `SymbolNameAttr` constraint
    (Gotcha 5 in `harness/porting-notes.md`). Generic form prints
    `<{sym_name = "name", ...}>`.
  - `function_type : FunctionType` — the signature. LLZK's TableGen
    declares this as `TypeAttrOf<FunctionType>` and the C++ verifier
    rejects a `function.def` without it, so the differential
    round-trip requires us to emit it. Stored as the underlying
    `FunctionType` (VEIR's type/attribute hierarchy lets us treat the
    wrapping `Attribute.functionType` case as a type attribute).

  Deferred for this prototype:
  - `arg_attrs`/`res_attrs` (ArrayAttrs of DictAttrs) — optional in
    LLZK, used by argument-attribute decorators (`{llzk.pub}`, …).
    Round-trip works without them when no decorators are present.
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

end

end Veir
