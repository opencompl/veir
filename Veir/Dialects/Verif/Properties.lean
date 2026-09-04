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

end

end Veir
