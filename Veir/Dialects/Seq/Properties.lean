module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of the `seq.firreg` operation.
-/
structure SeqFirRegProperties where
  name : StringAttr
  isAsync : Bool
  preset : Option IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def SeqFirRegProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String SeqFirRegProperties := do
  let some name := attrDict["name".toUTF8]? | throw "seq.firreg: requires attribute 'name'"
  let .stringAttr name := name
    | throw s!"seq.firreg: expected 'name' to be a string attribute, but got {name}"

  let isAsync := attrDict.contains "isAsync".toUTF8

  let preset ← match attrDict["preset".toUTF8]? with
    | none => pure none
    | some (.integerAttr i) => pure (some i)
    | some other => throw s!"seq.firreg: expected 'preset' to be an integer attribute, but got {other}"

  return { name, isAsync, preset }

/--
  Properties of the `seq.firmem` operation.

  CIRCT spells `ruw` and `wuw` as the enum attributes `#seq.ruw<old>` and
  `#seq.wuw<port_order>`. VeIR carries dialect enums as plain integers -- as `comb.icmp`'s
  `predicate` already does -- so they are held here as `i32` integer attributes:
  `ruw` is 0 undefined, 1 old, 2 new; `wuw` is 0 undefined, 1 port_order.
-/
structure SeqFirMemProperties where
  name : Option StringAttr
  readLatency : IntegerAttr
  writeLatency : IntegerAttr
  ruw : IntegerAttr
  wuw : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

/-- Read one required `i32` property of `seq.firmem`. -/
private def seqFirMemInt (attrDict : Std.HashMap ByteArray Attribute) (field : String) :
    Except String IntegerAttr := do
  let some attr := attrDict[field.toUTF8]?
    | throw s!"seq.firmem: requires attribute '{field}'"
  let .integerAttr attr := attr
    | throw s!"seq.firmem: expected '{field}' to be an integer attribute, but got {attr}"
  return attr

def SeqFirMemProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String SeqFirMemProperties := do
  let name ← match attrDict["name".toUTF8]? with
    | none => pure none
    | some (.stringAttr name) => pure (some name)
    | some other => throw s!"seq.firmem: expected 'name' to be a string attribute, but got {other}"

  let readLatency ← seqFirMemInt attrDict "readLatency"
  let writeLatency ← seqFirMemInt attrDict "writeLatency"
  let ruw ← seqFirMemInt attrDict "ruw"
  let wuw ← seqFirMemInt attrDict "wuw"

  return { name, readLatency, writeLatency, ruw, wuw }

/--
  Properties shared by the `seq.firmem` port operations.

  Each port has optional operands -- `enable` on every port, and `mask` on the two that write --
  so, as in MLIR, the operand list is split by an `operandSegmentSizes` dense array holding one
  entry per declared operand, `1` when it is present and `0` when it is not.
-/
structure SeqFirMemPortProperties where
  operandSegmentSizes : DenseArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def SeqFirMemPortProperties.fromAttrDict (opName : String)
    (attrDict : Std.HashMap ByteArray Attribute) : Except String SeqFirMemPortProperties := do
  if attrDict.size > 1 then
    throw s!"{opName}: expected only 'operandSegmentSizes', but got {attrDict.size} properties"
  let some sizesAttr := attrDict["operandSegmentSizes".toUTF8]?
    | throw s!"{opName}: missing 'operandSegmentSizes' property"
  let .denseArrayAttr sizesAttr := sizesAttr
    | throw s!"{opName}: expected 'operandSegmentSizes' to be a dense array attribute, but got {sizesAttr}"
  return { operandSegmentSizes := sizesAttr }

end

end Veir
