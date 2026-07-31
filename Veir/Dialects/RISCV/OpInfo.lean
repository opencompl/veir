module

public import Veir.Dialects.RISCV.OpInfo.Basic
public import Veir.Dialects.RISCV.Fold.Basic

namespace Veir

public section

instance : HasDialectOpInfo Riscv where
  fromName := Riscv.fromName
  name := Riscv.name
  propertiesOf := Riscv.propertiesOf
  fromAttrDict := Riscv.fromAttrDict
  toAttrDict := Riscv.toAttrDict
  hasSideEffects := Riscv.hasSideEffects
  readsMemory := Riscv.readsMemory
  isConstantLike := Riscv.isConstantLike
  foldsTo := Riscv.foldsTo
  hasSSADominance := Riscv.hasSSADominance

end

end Veir
