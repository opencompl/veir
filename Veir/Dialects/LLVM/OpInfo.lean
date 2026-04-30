module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Properties

namespace Veir

public section

@[expose, properties_of]
def Llvm.propertiesOf (op : Llvm) : Type :=
match op with
| .constant => LLVMConstantProperties
| .add => NswNuwProperties
| .sub => NswNuwProperties
| .mul => NswNuwProperties
| .udiv => ExactProperties
| .sdiv => ExactProperties
| .shl => NswNuwProperties
| .lshr => ExactProperties
| .ashr => ExactProperties
| .or => DisjointProperties
| .trunc => NswNuwProperties
| .zext => NnegProperties
| .icmp => IcmpProperties
| .cond_br => CondBrProperties
| .alloca => AllocaProperties
| .load => LoadProperties
| .store => StoreProperties
| _ => Unit

instance : HasDialectOpInfo Llvm where
  propertiesOf := Llvm.propertiesOf

end

end Veir
