module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Properties

namespace Veir

public section

@[expose, properties_of]
def Riscv_Cf.propertiesOf (op : Riscv_Cf) : Type :=
match op with
| .beq => RISCVBrProperties
| .bne => RISCVBrProperties
| .blt => RISCVBrProperties
| .bge => RISCVBrProperties
| .bltu => RISCVBrProperties
| .bgeu => RISCVBrProperties
| .cbr => RISCVBrProperties
| _ => Unit

instance : HasDialectOpInfo Riscv_Cf where
  propertiesOf := Riscv_Cf.propertiesOf

end

end Veir
