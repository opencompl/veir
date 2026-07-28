module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.LLVM.Properties
public import Veir.Dialects.Cf.Properties
meta import Veir.Meta.Attrs

namespace Veir

public section

@[opcodes]
inductive Llvm where
| mlir__constant
| mlir__poison
| and
| or
| xor
| add
| sub
| shl
| lshr
| ashr
| intr__ctlz
| intr__cttz
| intr__ctpop
| intr__bswap
| intr__bitreverse
| intr__fshl
| intr__fshr
| mul
| sdiv
| udiv
| srem
| urem
| icmp
| select
| trunc
| sext
| zext
| br
| cond_br
| unreachable
| alloca
| load
| store
| getelementptr
| call
| return
| func
| module_flags
| fadd
| fsub
| fmul
| fdiv
| frem
| freeze
| bitcast
| intr__smax
| intr__smin
| intr__umax
| intr__umin
| intr__abs
| intr__sadd__sat
| intr__uadd__sat
| intr__ssub__sat
| intr__usub__sat
| intr__sshl__sat
| intr__ushl__sat
deriving Inhabited, Repr, Hashable, DecidableEq

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
| .intr__ctlz | .intr__cttz => ZeroPoisonProperties
| .intr__abs => IntMinPoisonProperties
| .or => DisjointProperties
| .trunc => NswNuwProperties
| .zext => NnegProperties
| .icmp => IcmpProperties
| .cond_br => CondBrProperties
| .alloca => AllocaProperties
| .load => LoadProperties
| .store => StoreProperties
| .getelementptr => GetelementptrProperties
| .fadd | .fsub | .fmul | .fdiv | .frem => FastMathFlagsProperties
| .call => LLVMCallProperties
| .func => LLVMFuncProperties
| .module_flags => LLVMModuleFlagsProperties
| _ => Unit

instance : HasDialectOpInfo Llvm where
  propertiesOf := Llvm.propertiesOf

end

end Veir
