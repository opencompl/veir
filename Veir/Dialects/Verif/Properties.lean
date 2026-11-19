module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
  Properties of the `verif.assume`and `verif.assert` operations.
-/
structure VerifAssumeAssertProperties where
  label : Option StringAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def VerifAssumeAssertProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
  Except String VerifAssumeAssertProperties := do
  let label : Option StringAttr ←
  match attrDict["label".toUTF8]? with
    | none => pure none
    | some (.stringAttr l) => pure (some l)
    | some other => throw s!"verif: expected 'label' to be a string attribute, but got {other}"

  return { label }

/--
  Properties of the `verif.clocked_assert` and `verif.clocked_assume` operations.
-/
structure VerifClockedAssumeAssertProperties where
  edge : IntegerAttr
  label : Option StringAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def VerifClockedAssumeAssertProperties.fromAttrDict
    (attrDict : Std.HashMap ByteArray Attribute) :
    Except String VerifClockedAssumeAssertProperties := do
  let some edge := attrDict["edge".toUTF8]?
    | throw "verif: requires attribute 'edge'"
  let .integerAttr edge := edge
    | throw s!"verif: expected 'edge' to be an integer attribute, but got {edge}"

  let label : Option StringAttr ←
  match attrDict["label".toUTF8]? with
    | none => pure none
    | some (.stringAttr l) => pure (some l)
    | some other => throw s!"verif: expected 'label' to be a string attribute, but got {other}"

  return { edge, label }

end

end Veir
