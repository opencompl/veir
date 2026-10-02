module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  A RISC-V function uses a builtin function type whose inputs and outputs are
  registers. An empty body region denotes an external declaration. Linkage,
  visibility, and other function metadata are preserved verbatim in `extra`.
-/
structure RISCVFuncProperties where
  sym_name : StringAttr
  function_type : FunctionType
  extra : DictionaryAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def RISCVFuncProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String RISCVFuncProperties := do
  let symName ← match attrDict["sym_name".toUTF8]? with
    | some (.stringAttr s) => pure s
    | some attr => throw s!"riscv_cf.func: expected 'sym_name' to be a string attribute, but got {attr}"
    | none => throw "riscv_cf.func: missing 'sym_name' property"
  let funcType ← match attrDict["function_type".toUTF8]? with
    | some (.functionType ft) => pure ft
    | some attr => throw s!"riscv_cf.func: expected 'function_type' to be a builtin function type, but got {attr}"
    | none => throw "riscv_cf.func: missing 'function_type' property"
  let extra := DictionaryAttr.fromArray
    (attrDict.toArray.filter fun (k, _) => k ≠ "sym_name".toUTF8 && k ≠ "function_type".toUTF8)
  return { sym_name := symName, function_type := funcType, extra }

/--
  A direct `riscv_cf.call` names its target with `callee`. When absent, the
  first operand is the register holding the indirect target; the remaining
  operands are arguments. Argument and result values are already ABI-lowered
  registers. Register assignment and ABI extension handling are separate steps.
-/
structure RISCVCallProperties where
  callee : Option FlatSymbolRefAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def RISCVCallProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String RISCVCallProperties := do
  if attrDict.toArray.any (fun (key, _) => key ≠ "callee".toUTF8) then
    throw "riscv_cf.call: expected only 'callee' property"
  let callee ← match attrDict["callee".toUTF8]? with
    | some (.flatSymbolRefAttr callee) => pure (some callee)
    | some attr =>
      throw s!"riscv_cf.call: expected 'callee' to be a flat symbol reference, but got {attr}"
    | none => pure none
  return { callee }

/--
  Properties of the RISC-V conditional branching operations.
-/
structure RISCVBrProperties where
  operandSegmentSizes : DenseArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def RISCVBrProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String RISCVBrProperties := do
  if attrDict.size > 1 then
    throw s!"riscv_cf: expected only 'operandSegmentSizes' property, but got {attrDict.size} properties"
  let some sizesAttr := attrDict["operandSegmentSizes".toUTF8]?
    | throw "riscv_cf: missing 'operandSegmentSizes' property"
  let .denseArrayAttr sizesAttr := sizesAttr
    | throw s!"riscv_cf: expected 'operandSegmentSizes' to be a dense array attribute, but got {sizesAttr}"
  return { operandSegmentSizes := sizesAttr }

end

end Veir
