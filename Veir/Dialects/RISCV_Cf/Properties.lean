module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

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
