module

public import Veir.IR.Attribute
public import Std.Data.HashMap

import Veir.Dialects.Builtin.Properties

namespace Veir

public section

/--
  Decode a RISC-V immediate attribute. The attribute must be a 64-bit signless
  integer; unlike `llvm.mlir.constant`, the RISC-V dialects are ours alone, so
  there is no upstream compatibility reason to let the attribute's width differ
  from the width a register holds. Storing the decoded `BitVec 64` rather than
  the attribute keeps that invariant by construction: there is no width left to
  disagree with anything.
-/
def decodeRISCVImmediate (what : String) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (BitVec 64) := do
  let some attr := attrDict["value".toUTF8]?
    | throw s!"{what}: missing 'value' property"
  let .integerAttr intAttr := attr
    | throw s!"{what}: expected 'value' to be an integer attribute, but got {attr}"
  if intAttr.type.bitwidth ≠ 64 then
    throw s!"{what}: expected 'value' to be a 64-bit signless integer attribute, but got i{intAttr.type.bitwidth}"
  return BitVec.ofInt 64 intAttr.value

/-- Re-encode a RISC-V immediate as the `i64` attribute it is printed as. -/
def encodeRISCVImmediate (value : BitVec 64) : Attribute :=
  .integerAttr (IntegerAttr.mk value.toInt (IntegerType.mk 64))

/--
  Properties of the RISC-V immediate operations.

  The immediate is held as a `BitVec 64` -- the width a register holds -- not as
  an `IntegerAttr`, so an immediate whose declared width disagrees with that is
  not representable. See `decodeRISCVImmediate`.
-/
structure RISCVImmediateProperties where
  value : BitVec 64
deriving Inhabited, Repr, Hashable, DecidableEq

def RISCVImmediateProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String RISCVImmediateProperties := do
  if attrDict.size > 1 then
    throw s!"RISC-V immediate operation: expected only 'value' property, but got {attrDict.size} properties"
  let value ← decodeRISCVImmediate "RISC-V immediate operation" attrDict
  return { value }

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
  value : BitVec 64
  volatile_ : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def RISCVMemProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String RISCVMemProperties := do
  let volatile_ ← getUnitAttr "volatile_" attrDict
  /- 'value' is required and 'volatile_' optional, so anything beyond those
     two keys (or a second key when there is no 'volatile_') is bogus. -/
  if attrDict.size > (if volatile_ then 2 else 1) then
    throw s!"RISC-V memory operation: expected only 'value' and 'volatile_' properties, but got {attrDict.size} properties"
  let value ← decodeRISCVImmediate "RISC-V memory operation" attrDict
  return { value, volatile_ }

end

end Veir
