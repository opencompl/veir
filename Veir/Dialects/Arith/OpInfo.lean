module

public import Veir.Dialects.Arith.OpInfo.Basic
public import Veir.Dialects.Arith.Fold.Basic

namespace Veir

public section

instance : HasDialectOpInfo Arith where
  fromName := Arith.fromName
  name := Arith.name
  propertiesOf := Arith.propertiesOf
  fromAttrDict := Arith.fromAttrDict
  toAttrDict := Arith.toAttrDict
  hasSideEffects := Arith.hasSideEffects
  readsMemory := Arith.readsMemory
  isConstantLike := Arith.isConstantLike
  foldsTo := Arith.foldsTo
  hasSSADominance := Arith.hasSSADominance

end

end Veir
