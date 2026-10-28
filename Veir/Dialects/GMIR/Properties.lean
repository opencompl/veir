module

public import Veir.IR.Attribute
public import Std.Data.HashMap

import Veir.Dialects.Builtin.Properties

namespace Veir

public section

/--
Properties of `gmir.g_constant`.
-/
structure GMIRConstantProperties where
  value : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def GMIRConstantProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String GMIRConstantProperties := do
  if attrDict.size > 1 then
    throw s!"gmir.g_constant: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "gmir.g_constant: missing 'value' property"
  let .integerAttr intAttr := attr
    | throw s!"gmir.g_constant: expected 'value' to be an integer attribute, but got {attr}"
  return { value := intAttr }

/-- The negation of the constant, wrapped to its type. -/
def GMIRConstantProperties.neg (props : GMIRConstantProperties) : GMIRConstantProperties :=
  { value := IntegerAttr.ofInt (-props.value.value) props.value.type }

/-- Whether the constant is the minimum signed value of its type. -/
def GMIRConstantProperties.isMinSigned (props : GMIRConstantProperties) : Bool :=
  let bitwidth := props.value.type.bitwidth
  BitVec.ofInt bitwidth props.value.value = BitVec.intMin bitwidth

/--
Properties of `gmir.g_sext_inreg`. `sz` is the number of low bits that are kept.
-/
structure SextInRegProperties where
  sz : BitVec 64
deriving Inhabited, Repr, Hashable, DecidableEq

def SextInRegProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String SextInRegProperties := do
  let sz ← getI64Attr "gmir.g_sext_inreg" "sz" attrDict
  return { sz }

/--
Properties of `gmir.g_brcond`. Unlike LLVM's `G_BRCOND`, which falls through to the next block when
its condition is false, `g_brcond` names both successors and forwards operands to each of them, as
`llvm.cond_br` does. `operandSegmentSizes` splits the operands into the condition and the operands
forwarded to each successor.
-/
structure GMIRBrCondProperties where
  operandSegmentSizes : DenseArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def GMIRBrCondProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String GMIRBrCondProperties := do
  if attrDict.size > 1 then
    throw s!"gmir.g_brcond: expected only 'operandSegmentSizes' property, but got \
      {attrDict.size} properties"
  let some sizesAttr := attrDict["operandSegmentSizes".toUTF8]?
    | throw "gmir.g_brcond: missing 'operandSegmentSizes' property"
  let .denseArrayAttr sizesAttr := sizesAttr
    | throw s!"gmir.g_brcond: expected 'operandSegmentSizes' to be a dense array attribute, but \
        got {sizesAttr}"
  return { operandSegmentSizes := sizesAttr }

/--
A description of a memory reference used in the backend, same as LLVM's `MachineMemOperand`.

Representing this fully, as done in LLVM's GISel backend, allows us to legalize an access
independently of its value type (an `i8` load becomes an `i64` load of 8 bits).
Once the RISC-V operations also carry MachineMemOperand, this will allow us to tell `llc` which
accesses it may reorder or move.

Unlike in the LLVM dialect, the alignment is explicit. The IR-level attributes (access groups,
alias scopes, TBAA, `invariantGroup`) are not kept.

TODO: Add missing `MachineMemOperand` fields.
-/
structure MachineMemOperand where
  size : BitVec 64
  alignment : BitVec 64
  volatile_ : Bool
  nontemporal : Bool
  invariant : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def MachineMemOperand.fromAttrDict (instrName : String)
    (attrDict : Std.HashMap ByteArray Attribute) : Except String MachineMemOperand := do
  for key in attrDict.keys do
    let key := String.fromUTF8! key
    unless ["size", "alignment", "volatile_", "nontemporal", "invariant"].contains key do
      throw s!"{instrName}: unexpected property '{key}'"
  return {
    size := ← getI64Attr instrName "size" attrDict
    alignment := ← getI64Attr instrName "alignment" attrDict
    volatile_ := ← getUnitAttr "volatile_" attrDict
    nontemporal := ← getUnitAttr "nontemporal" attrDict
    invariant := ← getUnitAttr "invariant" attrDict }

def MachineMemOperand.toAttrDict (mmo : MachineMemOperand) :
    Std.HashMap ByteArray Attribute := Id.run do
  let mut dict := Std.HashMap.emptyWithCapacity 5
  dict := dict.insert "size".toUTF8 (i64Attr mmo.size)
  dict := dict.insert "alignment".toUTF8 (i64Attr mmo.alignment)
  if mmo.volatile_ then
    dict := dict.insert "volatile_".toUTF8 (.unitAttr UnitAttr.mk)
  if mmo.nontemporal then
    dict := dict.insert "nontemporal".toUTF8 (.unitAttr UnitAttr.mk)
  if mmo.invariant then
    dict := dict.insert "invariant".toUTF8 (.unitAttr UnitAttr.mk)
  dict

end

end Veir
