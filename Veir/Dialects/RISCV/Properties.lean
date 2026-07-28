module

public import Veir.IR.Attribute
public import Std.Data.HashMap

import Veir.Dialects.Builtin.Properties

namespace Veir

public section

/--
  Properties of the RISC-V immediate operations.
-/
structure RISCVImmediateProperties where
  value : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def RISCVImmediateProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String RISCVImmediateProperties := do
  if attrDict.size > 1 then
    throw s!"RISC-V immediate operation: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "RISC-V immediate operation: missing 'value' property"
  let .integerAttr intAttr := attr
    | throw s!"RISC-V immediate operation: expected 'value' to be an integer attribute, but got {attr}"
  return { value := intAttr }

/--
  Properties of the RISC-V memory operations (`ld`/`lw`/.../`sd`/`sb`): the
  offset immediate added to the base register, plus whether the access is
  volatile.

  RISC-V itself has no volatile bit -- a volatile `lw` and an ordinary one
  encode identically -- so this mirrors `LoadProperties`/`StoreProperties`
  in the LLVM dialect, where volatility is likewise a promise to the
  optimizer rather than something the target encodes.
-/
structure RISCVMemProperties where
  value : IntegerAttr
  volatile_ : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def RISCVMemProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String RISCVMemProperties := do
  let volatile_ ← getUnitAttr "volatile_" attrDict
  /- 'value' is required and 'volatile_' optional, so anything beyond those
     two keys (or a second key when there is no 'volatile_') is bogus. -/
  if attrDict.size > (if volatile_ then 2 else 1) then
    throw s!"RISC-V memory operation: expected only 'value' and 'volatile_' properties, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "RISC-V memory operation: missing 'value' property"
  let .integerAttr intAttr := attr
    | throw s!"RISC-V memory operation: expected 'value' to be an integer attribute, but got {attr}"
  return { value := intAttr, volatile_ }

end

end Veir
