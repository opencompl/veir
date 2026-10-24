module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of the `arith.constant` operation: an integer or an index value.
-/
inductive ArithConstantProperties where
  | mk (value : IntegerAttr)
  | index (value : IndexAttr)
deriving Inhabited, Repr, Hashable, DecidableEq

def ArithConstantProperties.intAttr? : ArithConstantProperties → Option IntegerAttr
  | .mk value => some value
  | .index _ => none

def ArithConstantProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String ArithConstantProperties := do
  if attrDict.size > 1 then
    throw s!"arith.constant: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "arith.constant: missing 'value' property"
  match attr with
  | .integerAttr intAttr => return .mk intAttr
  | .indexAttr indexAttr => return .index indexAttr
  | _ => throw s!"arith.constant: expected 'value' to be an integer attribute, but got {attr}"

/-- Properties of arith operations that can have `nsw` and `nuw` flags, such as `arith.addi` or `arith.muli`. -/
structure ArithIntegerOverflowFlagsProperties where
  attr : ArithIntegerOverflowFlagsAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def ArithIntegerOverflowFlagsProperties.fromAttrDict
    (attrDict : Std.HashMap ByteArray Attribute) :
    Except String ArithIntegerOverflowFlagsProperties := do

  let value ← match attrDict["overflowFlags".toUTF8]? with
    | none => .ok { nsw := false, nuw := false }
    | some (.arithIntegerOverflowFlagsAttr flags) => .ok flags
    | some (.unregisteredAttr attr) =>
        .error s!"expected 'overflowFlags' to be an arith integer overflow flags attribute, but got unregistered {attr}"
    | some attr =>
        .error s!"expected 'overflowFlags' to be an arith integer overflow flags attribute, but got {attr}"

  return ⟨value⟩

end

end Veir
