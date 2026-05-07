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
| .getelementptr => GetelementptrProperties
| _ => Unit

@[expose]
def Llvm.getNumOperands (op : Llvm) : Option Nat :=
match op with
| .constant => some 0
| .alloca
| .br
| .cond_br
| .load => some 1
| .add
| .and
| .xor
| .srem
| .urem
| .select
| .sext
| .sub
| .mul
| .udiv
| .sdiv
| .shl
| .lshr
| .ashr
| .or
| .trunc
| .zext
| .icmp
| .store => some 2
| .getelementptr
| .return => none

instance : HasDialectOpInfo Llvm where
  propertiesOf := Llvm.propertiesOf

end

end Veir
