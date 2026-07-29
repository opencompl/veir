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

def Llvm.hasSideEffects (op : Llvm) (props : Llvm.propertiesOf op) : Bool :=
  match op, props with
  -- Volatile loads are definitionally side-effecting.
  | .load, props => props.volatile_
  | .mlir__constant, _
  | .mlir__poison, _
  | .and, _ | .or, _ | .xor, _
  | .add, _ | .sub, _ | .mul, _
  | .sdiv, _ | .udiv, _ | .srem, _ | .urem, _
  | .shl, _ | .lshr, _ | .ashr, _
  | .intr__ctlz, _ | .intr__cttz, _ | .intr__ctpop, _
  | .intr__bswap, _ | .intr__bitreverse, _
  | .intr__fshl, _ | .intr__fshr, _
  | .icmp, _ | .select, _
  | .trunc, _ | .sext, _ | .zext, _
  | .getelementptr, _
  | .intr__smax, _ | .intr__smin, _ | .intr__umax, _ | .intr__umin, _
  | .intr__abs, _
  | .intr__sadd__sat, _ | .intr__uadd__sat, _
  | .intr__ssub__sat, _ | .intr__usub__sat, _
  | .intr__sshl__sat, _ | .intr__ushl__sat, _
  | .fadd, _ | .fsub, _ | .fmul, _ | .fdiv, _ | .frem, _ => false
  -- For everything else: be conservative!
  | _, _ => true

def Llvm.readsMemory (op : Llvm) : Bool :=
  match op with
  | .load => true
  | _ => false

def Llvm.isConstantLike (op : Llvm) : Bool :=
  match op with
  | .mlir__constant | .mlir__poison => true
  | _ => false

def Llvm.hasSSADominance (_op : Llvm) (_index : Nat) : Bool :=
  true

instance : HasDialectOpInfo Llvm where
  propertiesOf := Llvm.propertiesOf
  hasSideEffects := Llvm.hasSideEffects
  readsMemory := Llvm.readsMemory
  isConstantLike := Llvm.isConstantLike
  hasSSADominance := Llvm.hasSSADominance

end

end Veir
