module

public import Veir.IR.Attribute

namespace Veir

public section

/-- Properties shared by the LLZK cast operations. -/
structure CastProperties where
  overflow : CastOverflowSemanticsAttr := { value := .assert }
deriving Inhabited, Repr, Hashable, DecidableEq

def CastProperties.fromAttrDict (opName : String)
    (attrDict : Std.HashMap ByteArray Attribute) : Except String CastProperties := do
  if attrDict.size > 1 then
    throw s!"{opName}: expected only 'overflow' property, got {attrDict.size}"
  let overflowAttr := attrDict["overflow".toUTF8]?
  let overflow ← match overflowAttr with
    | some (.castOverflowSemanticsAttr overflow) => pure overflow
    | some attr =>
      throw s!"{opName}: expected 'overflow' to be a #cast<overflow ...> attribute, got {attr}"
    | none => pure { value := .assert }
  if attrDict.size = 1 ∧ overflowAttr.isNone then
    throw s!"{opName}: only 'overflow' is a recognized property"
  return { overflow }

def CastProperties.toAttrDict (props : CastProperties) : Std.HashMap ByteArray Attribute :=
  (Std.HashMap.emptyWithCapacity 1).insert
    "overflow".toUTF8 (Attribute.castOverflowSemanticsAttr props.overflow)

end

end Veir
