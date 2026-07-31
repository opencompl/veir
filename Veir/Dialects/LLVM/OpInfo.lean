module

public import Veir.Dialects.LLVM.OpInfo.Basic
public import Veir.Dialects.LLVM.Fold.Basic

namespace Veir

public section

instance : HasDialectOpInfo Llvm where
  fromName := Llvm.fromName
  name := Llvm.name
  propertiesOf := Llvm.propertiesOf
  fromAttrDict := Llvm.fromAttrDict
  toAttrDict := Llvm.toAttrDict
  hasSideEffects := Llvm.hasSideEffects
  readsMemory := Llvm.readsMemory
  isConstantLike := Llvm.isConstantLike
  foldsTo := Llvm.foldsTo
  hasSSADominance := Llvm.hasSSADominance

end

end Veir
