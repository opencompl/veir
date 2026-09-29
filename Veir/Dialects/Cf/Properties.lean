module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of the `cond_br` operation. `branch_weights` is empty when absent,
  and `loop_annotation` is `none` when absent.
-/
structure CondBrProperties where
  branch_weights : DenseArrayAttr
  loop_annotation : Option LoopAnnotationAttr := none
  operandSegmentSizes : DenseArrayAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def CondBrProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String CondBrProperties := do
  if let some (key, _) := attrDict.toArray.find? (fun (k, _) =>
      k ≠ "branch_weights".toUTF8 && k ≠ "loop_annotation".toUTF8
        && k ≠ "operandSegmentSizes".toUTF8) then
    throw s!"cf.cond_br: unexpected property '{String.fromUTF8! key}'"
  let weightsAttr ← match attrDict["branch_weights".toUTF8]? with
    | some (.denseArrayAttr weightsAttr) => .ok weightsAttr
    | some attr => .error s!"expected 'branch_weights' to be an optional dense array attribute, but got {attr}"
    | none => .ok { elementType := { bitwidth := 32 }, values := #[] }
  let annotation ← match attrDict["loop_annotation".toUTF8]? with
    | some (.loopAnnotationAttr annotation) => .ok (some annotation)
    | some attr =>
      throw s!"cf.cond_br: expected 'loop_annotation' to be a loop annotation attribute, but got {attr}"
    | none => .ok none
  let some sizesAttr := attrDict["operandSegmentSizes".toUTF8]?
    | throw "cf.cond_br: missing 'operandSegmentSizes' property"
  let .denseArrayAttr sizesAttr := sizesAttr
    | throw s!"cf.cond_br: expected 'operandSegmentSizes' to be a dense array attribute, but got {sizesAttr}"
  return { branch_weights := weightsAttr, loop_annotation := annotation,
           operandSegmentSizes := sizesAttr }

end

end Veir
