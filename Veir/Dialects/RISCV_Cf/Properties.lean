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

end

end Veir
