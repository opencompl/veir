module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Properties

namespace Veir

public section

@[expose, properties_of]
def Llvm.propertiesOf (op : Llvm) : Type :=
match op with
| .mlir__constant => LLVMConstantProperties
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
| .load => LoadProperties -- attribute
| .store => StoreProperties -- attribute
| .getelementptr => GetelementptrProperties -- attribute
| .fadd | .fsub | .fmul | .fdiv | .frem => FastMathFlagsProperties
| .func => LLVMFuncProperties
| .module_flags => LLVMModuleFlagsProperties
| _ => Unit

def Llvm.propertySize (op : Llvm) : UInt64 :=
match op with
| .mlir__constant => 8
| .add => 1
| .sub => 1
| .mul => 1
| .udiv => 1
| .sdiv => 1
| .shl => 1
| .lshr => 1
| .ashr => 1
| .or => 1
| .trunc => 1
| .zext => 1
| .icmp => 1
| .cond_br => 8 -- attribute
| .alloca => 8 -- attribute
| .load => 8 -- attribute
| .store => 8 -- attribute
| .getelementptr => 8 -- attribute
| .fadd | .fsub | .fmul | .fdiv | .frem => 1
| .func => 8
| .module_flags => 8
| _ => 0


instance : HasDialectOpInfo Llvm where
  propertiesOf := Llvm.propertiesOf
  propertySize op := Llvm.propertySize op
  propertySize_small {op} := by cases op <;> simp [Llvm.propertySize]

end

end Veir
