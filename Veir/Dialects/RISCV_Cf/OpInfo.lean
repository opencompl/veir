module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.RISCV_Cf.Properties
meta import Veir.Meta.Attrs

namespace Veir

public section

@[opcodes]
inductive Riscv_Cf where
| branch
| beqz
| bnez
| beq
| bne
| blt
| bge
| bltu
| bgeu
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Riscv_Cf.propertiesOf (op : Riscv_Cf) : Type :=
match op with
| .beq => RISCVBrProperties
| .bne => RISCVBrProperties
| .blt => RISCVBrProperties
| .bge => RISCVBrProperties
| .bltu => RISCVBrProperties
| .bgeu => RISCVBrProperties
| .beqz => RISCVBrProperties
| .bnez => RISCVBrProperties
| _ => Unit

def Riscv_Cf.hasSideEffects
    (_op : Riscv_Cf) (_props : Riscv_Cf.propertiesOf _op) : Bool :=
  true

def Riscv_Cf.readsMemory (_op : Riscv_Cf) : Bool :=
  false

def Riscv_Cf.isConstantLike (_op : Riscv_Cf) : Bool :=
  false

def Riscv_Cf.hasSSADominance (_op : Riscv_Cf) (_index : Nat) : Bool :=
  true

instance : HasDialectOpInfo Riscv_Cf where
  propertiesOf := Riscv_Cf.propertiesOf
  hasSideEffects := Riscv_Cf.hasSideEffects
  readsMemory := Riscv_Cf.readsMemory
  isConstantLike := Riscv_Cf.isConstantLike
  hasSSADominance := Riscv_Cf.hasSSADominance

end

end Veir
