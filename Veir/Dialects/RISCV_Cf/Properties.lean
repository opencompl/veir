module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

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

/--
  Properties of `riscv_cf.call`: the symbol of the function called. Calls are
  always direct.
-/
structure RISCVCallProperties where
  callee : FlatSymbolRefAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def RISCVCallProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String RISCVCallProperties := do
  if attrDict.size > 1 then
    throw s!"riscv_cf.call: expected only 'callee' property, but got {attrDict.size} properties"
  match attrDict["callee".toUTF8]? with
  | some (.flatSymbolRefAttr callee) => return { callee }
  | some attr => throw s!"riscv_cf.call: expected 'callee' to be a flat symbol reference, but got {attr}"
  | none => throw "riscv_cf.call: missing 'callee' property"

end

end Veir
