module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.LLVM.Properties
public import Veir.Dialects.Cf.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Llvm where
| mlir__constant
| mlir__poison
| mlir__global
| mlir__addressof
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
| .mlir__global => LLVMGlobalProperties
| .mlir__addressof => LLVMAddressOfProperties
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

def Llvm.fromAttrDict
    (op : Llvm) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Llvm.propertiesOf op) := by
  cases op
  case mlir__constant => exact LLVMConstantProperties.fromAttrDict attrDict
  case mlir__global => exact LLVMGlobalProperties.fromAttrDict attrDict
  case mlir__addressof => exact LLVMAddressOfProperties.fromAttrDict attrDict
  case add | sub | mul | shl | trunc =>
    exact NswNuwProperties.fromAttrDict attrDict
  case udiv | sdiv | lshr | ashr =>
    exact ExactProperties.fromAttrDict attrDict
  case intr__ctlz =>
    exact ZeroPoisonProperties.fromAttrDictFor "llvm.intr.ctlz" attrDict
  case intr__cttz =>
    exact ZeroPoisonProperties.fromAttrDictFor "llvm.intr.cttz" attrDict
  case intr__abs => exact IntMinPoisonProperties.fromAttrDict attrDict
  case or => exact DisjointProperties.fromAttrDict attrDict
  case zext => exact NnegProperties.fromAttrDict attrDict
  case icmp => exact IcmpProperties.fromAttrDict attrDict
  case cond_br => exact CondBrProperties.fromAttrDict attrDict
  case alloca => exact AllocaProperties.fromAttrDict attrDict
  case load => exact LoadProperties.fromAttrDict attrDict
  case store => exact StoreProperties.fromAttrDict attrDict
  case getelementptr => exact GetelementptrProperties.fromAttrDict attrDict
  case fadd | fsub | fmul | fdiv | frem =>
    exact FastMathFlagsProperties.fromAttrDict attrDict
  case func => exact LLVMFuncProperties.fromAttrDict attrDict
  case module_flags => exact LLVMModuleFlagsProperties.fromAttrDict attrDict
  case call => exact LLVMCallProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Llvm.toAttrDict
    (op : Llvm) (props : Llvm.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .mlir__constant =>
    match props.value with
    | .integer intAttr =>
      (Std.HashMap.emptyWithCapacity 1).insert
        "value".toUTF8 (Attribute.integerAttr intAttr)
    | .float floatAttr =>
      (Std.HashMap.emptyWithCapacity 1).insert
        "value".toUTF8 (Attribute.floatAttr floatAttr)
    | .dense denseAttr =>
      (Std.HashMap.emptyWithCapacity 1).insert
        "value".toUTF8 (Attribute.denseElementsAttr denseAttr)
    | .string stringAttr =>
      (Std.HashMap.emptyWithCapacity 1).insert
        "value".toUTF8 (Attribute.stringAttr stringAttr)
  | .mlir__global => Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    dict := dict.insert "sym_name".toUTF8 (.stringAttr props.sym_name)
    dict := dict.insert "global_type".toUTF8 props.global_type
    if let some alignment := props.alignment then
      dict := dict.insert "alignment".toUTF8 (.integerAttr alignment)
    dict := dict.insert "addr_space".toUTF8 (.integerAttr props.addr_space)
    dict := dict.insert "linkage".toUTF8 (.linkageAttr props.linkage)
    if let some value := props.value then
      dict := dict.insert "value".toUTF8 value
    if props.constant then
      dict := dict.insert "constant".toUTF8 (.unitAttr UnitAttr.mk)
    dict
  | .mlir__addressof => Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    dict := dict.insert "global_name".toUTF8 (.flatSymbolRefAttr props.global_name)
    dict
  | .add | .sub | .mul | .shl | .trunc => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    let mut val := 0
    if props.nsw then
      val := val + 1
    if props.nuw then
      val := val + 2
    if val > 0 then
      let attr := IntegerAttr.mk (Int.ofNat val) (IntegerType.mk 32)
      dict := dict.insert "overflowFlags".toUTF8 (Attribute.integerAttr attr)
    dict
  | .fadd | .fsub | .fmul | .fdiv | .frem =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "fastmathFlags".toUTF8 (Attribute.fastMathFlagsAttr props.attr)
  | .icmp =>
    let value := IntegerAttr.mk (Int.ofNat props.predicate.toNat) (IntegerType.mk 64)
    (Std.HashMap.emptyWithCapacity 1).insert
      "predicate".toUTF8 (Attribute.integerAttr value)
  | .cond_br =>
    let dict := (Std.HashMap.emptyWithCapacity 2).insert
      "branch_weights".toUTF8 (Attribute.denseArrayAttr props.branch_weights)
    dict.insert "operandSegmentSizes".toUTF8
      (Attribute.denseArrayAttr props.operandSegmentSizes)
  | .udiv | .sdiv | .lshr | .ashr => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    if props.exact then
      dict := dict.insert "exact".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .or => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    if props.disjoint then
      dict := dict.insert "disjoint".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .zext => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    if props.nneg then
      dict := dict.insert "nneg".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .intr__ctlz | .intr__cttz =>
    let value := if props.is_zero_poison then 1 else 0
    let attr := IntegerAttr.mk value (IntegerType.mk 1)
    (Std.HashMap.emptyWithCapacity 1).insert
      "is_zero_poison".toUTF8 (Attribute.integerAttr attr)
  | .intr__abs =>
    let value := if props.is_int_min_poison then 1 else 0
    let attr := IntegerAttr.mk value (IntegerType.mk 1)
    (Std.HashMap.emptyWithCapacity 1).insert
      "is_int_min_poison".toUTF8 (Attribute.integerAttr attr)
  | .alloca => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 3
    dict := dict.insert "alignment".toUTF8 (Attribute.integerAttr props.alignment)
    dict := dict.insert "elem_type".toUTF8 props.elem_type
    if props.inalloca then
      dict := dict.insert "inalloca".toUTF8 (.unitAttr UnitAttr.mk)
    dict
  | .load => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 10
    dict := dict.insert "alignment".toUTF8 (.integerAttr props.alignment)
    if props.volatile_ then
      dict := dict.insert "volatile_".toUTF8 (.unitAttr UnitAttr.mk)
    if props.nontemporal then
      dict := dict.insert "nontemporal".toUTF8 (.unitAttr UnitAttr.mk)
    if props.invariant then
      dict := dict.insert "invariant".toUTF8 (.unitAttr UnitAttr.mk)
    if props.invariantGroup then
      dict := dict.insert "invariantGroup".toUTF8 (.unitAttr UnitAttr.mk)
    if let some syncscope := props.syncscope then
      dict := dict.insert "syncscope".toUTF8 (.stringAttr syncscope)
    dict := dict.insert "access_groups".toUTF8 (.arrayAttr props.access_groups)
    dict := dict.insert "alias_scopes".toUTF8 (.arrayAttr props.alias_scopes)
    dict := dict.insert "noalias_scopes".toUTF8 (.arrayAttr props.noalias_scopes)
    dict := dict.insert "tbaa".toUTF8 (.arrayAttr props.tbaa)
    dict
  | .store => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 9
    dict := dict.insert "alignment".toUTF8 (.integerAttr props.alignment)
    if props.volatile_ then
      dict := dict.insert "volatile_".toUTF8 (.unitAttr UnitAttr.mk)
    if props.nontemporal then
      dict := dict.insert "nontemporal".toUTF8 (.unitAttr UnitAttr.mk)
    if props.invariantGroup then
      dict := dict.insert "invariantGroup".toUTF8 (.unitAttr UnitAttr.mk)
    if let some syncscope := props.syncscope then
      dict := dict.insert "syncscope".toUTF8 (.stringAttr syncscope)
    dict := dict.insert "access_groups".toUTF8 (.arrayAttr props.access_groups)
    dict := dict.insert "alias_scopes".toUTF8 (.arrayAttr props.alias_scopes)
    dict := dict.insert "noalias_scopes".toUTF8 (.arrayAttr props.noalias_scopes)
    dict := dict.insert "tbaa".toUTF8 (.arrayAttr props.tbaa)
    dict
  | .getelementptr => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 3
    dict := dict.insert
      "rawConstantIndices".toUTF8
      (Attribute.denseArrayAttr props.rawConstantIndices)
    dict := dict.insert "elem_type".toUTF8 props.elem_type
    dict := dict.insert "noWrapFlags".toUTF8 (.integerAttr props.noWrapFlags)
    dict
  | .func => Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    if let some sym_name := props.sym_name then
      dict := dict.insert "sym_name".toUTF8 (.stringAttr sym_name)
    if let some function_type := props.function_type then
      dict := dict.insert "function_type".toUTF8 function_type
    dict
  | .module_flags =>
    (Std.HashMap.emptyWithCapacity 3).insert
      "flags".toUTF8 (Attribute.arrayAttr props.flags)
  | .call => Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    if let some callee := props.callee then
      dict := dict.insert "callee".toUTF8 (.flatSymbolRefAttr callee)
    dict
  | _ => Std.HashMap.emptyWithCapacity 0

def Llvm.hasSideEffects (op : Llvm) (props : Llvm.propertiesOf op) : Bool :=
  match op, props with
  -- Volatile loads are definitionally side-effecting.
  | .load, props => props.volatile_
  | .mlir__constant, _
  | .mlir__poison, _
  | .mlir__addressof, _
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

def Llvm.readsMemory (op : Llvm) (props : Llvm.propertiesOf op) : Bool :=
  match op, props with
  | .store, props => props.volatile_
  | .mlir__constant, _ | .mlir__poison, _ | .mlir__addressof, _
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
  | .br, _ | .cond_br, _ | .return, _
  | .freeze, _ | .bitcast, _
  | .intr__smax, _ | .intr__smin, _ | .intr__umax, _ | .intr__umin, _
  | .intr__abs, _
  | .intr__sadd__sat, _ | .intr__uadd__sat, _
  | .intr__ssub__sat, _ | .intr__usub__sat, _
  | .intr__sshl__sat, _ | .intr__ushl__sat, _
  | .fadd, _ | .fsub, _ | .fmul, _ | .fdiv, _ | .frem, _ => false
  | _, _ => true

def Llvm.writesMemory (op : Llvm) (props : Llvm.propertiesOf op) : Bool :=
  match op, props with
  | .load, props => props.volatile_
  | .mlir__constant, _ | .mlir__poison, _ | .mlir__addressof, _
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
  | .br, _ | .cond_br, _ | .return, _
  | .freeze, _ | .bitcast, _
  | .intr__smax, _ | .intr__smin, _ | .intr__umax, _ | .intr__umin, _
  | .intr__abs, _
  | .intr__sadd__sat, _ | .intr__uadd__sat, _
  | .intr__ssub__sat, _ | .intr__usub__sat, _
  | .intr__sshl__sat, _ | .intr__ushl__sat, _
  | .fadd, _ | .fsub, _ | .fmul, _ | .fdiv, _ | .frem, _ => false
  | _, _ => true

def Llvm.isConstantLike (op : Llvm) : Bool :=
  match op with
  | .mlir__constant | .mlir__poison | .mlir__addressof => true
  | _ => false

def Llvm.hasSSADominance (_op : Llvm) (_index : Nat) : Bool :=
  true

def Llvm.isTerminator (op : Llvm) : Bool :=
  match op with
  | .br | .cond_br | .return | .unreachable => true
  | _ => false

#generate_dialect Llvm

instance : HasOpInfo Llvm where
  fromName := Llvm.fromName
  name := Llvm.name
  propertiesOf := Llvm.propertiesOf
  fromAttrDict := Llvm.fromAttrDict
  toAttrDict := Llvm.toAttrDict
  hasSideEffects := Llvm.hasSideEffects
  readsMemory := Llvm.readsMemory
  writesMemory := Llvm.writesMemory
  isConstantLike := Llvm.isConstantLike
  hasSSADominance := Llvm.hasSSADominance
  isTerminator := Llvm.isTerminator

end

end Veir
