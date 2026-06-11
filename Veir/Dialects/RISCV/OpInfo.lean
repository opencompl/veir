module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Properties

namespace Veir

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
| .lw => RISCVImmediateProperties
| .lwu => RISCVImmediateProperties
| .lh => RISCVImmediateProperties
| .lhu => RISCVImmediateProperties
| .lb => RISCVImmediateProperties
| .lbu => RISCVImmediateProperties
| .sd => RISCVImmediateProperties
| .sw => RISCVImmediateProperties
| .sh => RISCVImmediateProperties
| .sb => RISCVImmediateProperties
| _ => Unit

instance : HasDialectOpInfo Riscv where
  propertiesOf := Riscv.propertiesOf

end

end Veir
