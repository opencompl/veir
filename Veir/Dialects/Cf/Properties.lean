module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of the `cond_br` operation.
-/
structure CondBrProperties where
  branch_weights : DenseArrayAttr
  operandSegmentSizes : DenseArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def CondBrProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String CondBrProperties := do
  if attrDict.size > 2 then
    throw s!"cf.cond_br: expected only 'branch_weights' and 'operandSegmentSizes' properties, but got {attrDict.size} properties"
  let weightsAttr ← match attrDict["branch_weights".toUTF8]? with
    | some (.denseArrayAttr weightsAttr) => .ok weightsAttr
    | some attr => .error s!"expected 'branch_weights' to be an optional dense array attribute, but got {attr}"
    | none => .ok { elementType := { bitwidth := 32 }, values := #[] }
  let some sizesAttr := attrDict["operandSegmentSizes".toUTF8]?
    | throw "cf.cond_br: missing 'operandSegmentSizes' property"
  let .denseArrayAttr sizesAttr := sizesAttr
    | throw s!"cf.cond_br: expected 'operandSegmentSizes' to be a dense array attribute, but got {sizesAttr}"
  return { branch_weights := weightsAttr, operandSegmentSizes := sizesAttr }

end

end Veir
