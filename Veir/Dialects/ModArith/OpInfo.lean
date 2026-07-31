module

public import Veir.Dialects.ModArith.OpInfo.Basic
public import Veir.Dialects.ModArith.Fold.Basic

namespace Veir

public section

instance : HasDialectOpInfo Mod_Arith where
  fromName := Mod_Arith.fromName
  name := Mod_Arith.name
  propertiesOf := Mod_Arith.propertiesOf
  fromAttrDict := Mod_Arith.fromAttrDict
  toAttrDict := Mod_Arith.toAttrDict
  hasSideEffects := Mod_Arith.hasSideEffects
  readsMemory := Mod_Arith.readsMemory
  isConstantLike := Mod_Arith.isConstantLike
  foldsTo := Mod_Arith.foldsTo
  hasSSADominance := Mod_Arith.hasSSADominance

end

end Veir
