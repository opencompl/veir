module

public import Veir.Data.RISCV.Reg.Basic
public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Properties

namespace Veir

open Veir.Data

public section

@[expose, properties_of]
def Riscv.propertiesOf (op : Riscv) : Type :=
match op with
| .li => RISCVImmediateProperties
| .lui => RISCVImmediateProperties
| .auipc => RISCVImmediateProperties
| .andi => RISCVImmediateProperties
| .ori => RISCVImmediateProperties
| .xori => RISCVImmediateProperties
| .addi => RISCVImmediateProperties
| .slti => RISCVImmediateProperties
| .sltiu => RISCVImmediateProperties
| .addiw => RISCVImmediateProperties
| .slli => RISCVImmediateProperties
| .srli => RISCVImmediateProperties
| .srai => RISCVImmediateProperties
| .slliw => RISCVImmediateProperties
| .srliw => RISCVImmediateProperties
| .sraiw => RISCVImmediateProperties
| .slliuw => RISCVImmediateProperties
| .rori => RISCVImmediateProperties
| .roriw => RISCVImmediateProperties
| .bclri => RISCVImmediateProperties
| .bexti => RISCVImmediateProperties
| .binvi => RISCVImmediateProperties
| .bseti => RISCVImmediateProperties
| .ld => RISCVImmediateProperties
| .sd => RISCVImmediateProperties
| _ => Unit

@[expose, properties_of]
def Riscv.getNumOperands (op : Riscv) : Nat :=
match op with
| .li => 1
| .or => 2
| .and => 2
| _ => 0

@[expose, properties_of]
def Riscv.getOperandType (op : Riscv) (_idx : Fin (Riscv.getNumOperands op)) : Type :=
match op with
| .li => Nat
| .or => Nat
| .and => Nat
| _ => Unit

def Riscv.interpret (op : Riscv) (ops : Vector RISCV.Reg (Riscv.getNumOperands op)) : RISCV.Reg :=
match op with
| .li => ops[0]
| .or => RISCV.or ops[0] ops[1]
| .and => RISCV.and ops[0] ops[1]
| _ => sorry

instance : HasDialectOpInfo Riscv where
  propertiesOf := Riscv.propertiesOf
  getNumOperands := Riscv.getNumOperands
  getOperandType := Riscv.getOperandType

end

end Veir
