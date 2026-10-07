module

public import Veir.IR.Attribute
public import Std.Data.HashMap

import Veir.Dialects.Builtin.Properties

namespace Veir

public section

/--
Properties of `gmir.g_sext_inreg`. `sz` is the number of low bits that are sign-extended, which
LLVM's `G_SEXT_INREG` takes as an immediate operand.
-/
structure SextInRegProperties where
  sz : BitVec 64
deriving Inhabited, Repr, Hashable, DecidableEq

def SextInRegProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String SextInRegProperties := do
  let sz ← getI64Attr "gmir.g_sext_inreg" "sz" attrDict
  return { sz }

end

end Veir
