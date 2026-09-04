module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLVM.Properties
public import Veir.Dialects.Cf.Properties
public import Veir.ConstantMaterialization
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Llvm where
| mlir__constant
| mlir__poison
| mlir__zero
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
| intr__lifetime__start
| intr__lifetime__end
| intr__ctpop
| intr__bswap
| intr__bitreverse
| intr__fshl
| intr__fshr
| intr__assume
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
| switch
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
| .intr__assume => LLVMAssumeProperties
| .or => DisjointProperties
| .trunc => NswNuwProperties
| .zext => NnegProperties
| .icmp => IcmpProperties
| .br => LLVMBrProperties
| .cond_br => LLVMCondBrProperties
| .switch => LLVMSwitchProperties
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
  case intr__assume => exact LLVMAssumeProperties.fromAttrDict attrDict
  case or => exact DisjointProperties.fromAttrDict attrDict
  case zext => exact NnegProperties.fromAttrDict attrDict
  case icmp => exact IcmpProperties.fromAttrDict attrDict
  case br => exact LLVMBrProperties.fromAttrDict attrDict
  case cond_br => exact LLVMCondBrProperties.fromAttrDict attrDict
  case switch => exact LLVMSwitchProperties.fromAttrDict attrDict
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
  | .br => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    if let some annotation := props.loop_annotation then
      dict := dict.insert "loop_annotation".toUTF8 (.loopAnnotationAttr annotation)
    dict
  | .cond_br => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 3
    dict := dict.insert
      "branch_weights".toUTF8 (Attribute.denseArrayAttr props.branch_weights)
    if let some annotation := props.loop_annotation then
      dict := dict.insert "loop_annotation".toUTF8 (.loopAnnotationAttr annotation)
    dict := dict.insert "operandSegmentSizes".toUTF8
      (Attribute.denseArrayAttr props.operandSegmentSizes)
    dict
  | .switch => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 4
    if let some values := props.case_values then
      dict := dict.insert "case_values".toUTF8 (.denseElementsAttr values)
    dict := dict.insert "case_operand_segments".toUTF8
      (Attribute.denseArrayAttr props.case_operand_segments)
    if let some weights := props.branch_weights then
      dict := dict.insert "branch_weights".toUTF8 (Attribute.denseArrayAttr weights)
    dict := dict.insert "operandSegmentSizes".toUTF8
      (Attribute.denseArrayAttr props.operandSegmentSizes)
    dict
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
  | .intr__assume => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    dict := dict.insert "op_bundle_sizes".toUTF8 (Attribute.denseArrayAttr props.op_bundle_sizes)
    if let some tags := props.op_bundle_tags then
      dict := dict.insert "op_bundle_tags".toUTF8 (.arrayAttr tags)
    dict
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
    dict := dict.insert "sym_name".toUTF8 (.stringAttr props.sym_name)
    dict := dict.insert "function_type".toUTF8 (.llvmFunctionType props.function_type)
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

@[get_effects]
def Llvm.getEffects (op : Llvm) (props : Llvm.propertiesOf op) : MemoryEffects :=
  match op, props with
  | .alloca, _ => .allocate
  | .load, props => if props.volatile_ then .readWrite else .read
  | .store, props => if props.volatile_ then .readWrite else .write
  | .mlir__constant, _ | .mlir__poison, _ | .mlir__zero, _ | .mlir__addressof, _
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
  | .br, _ | .cond_br, _ | .switch, _ | .return, _
  | .freeze, _ | .bitcast, _
  | .intr__smax, _ | .intr__smin, _ | .intr__umax, _ | .intr__umin, _
  | .intr__abs, _
  | .intr__sadd__sat, _ | .intr__uadd__sat, _
  | .intr__ssub__sat, _ | .intr__usub__sat, _
  | .intr__sshl__sat, _ | .intr__ushl__sat, _
  | .fadd, _ | .fsub, _ | .fmul, _ | .fdiv, _ | .frem, _ => .none
  -- For everything else: be conservative!
  | _, _ => .unknown

def Llvm.isConstantLike (op : Llvm) : Bool :=
  match op with
  | .mlir__constant | .mlir__poison | .mlir__zero | .mlir__addressof => true
  | _ => false

def Llvm.isIsolatedFromAbove (op : Llvm) : Bool :=
  match op with
  | .mlir__global | .func => true
  | _ => false

def Llvm.hasSSADominance (_op : Llvm) (_index : Nat) : Bool :=
  true

@[is_terminator]
def Llvm.isTerminator (op : Llvm) : Bool :=
  match op with
  | .br | .cond_br | .switch | .return | .unreachable => true
  | _ => false

#generate_dialect Llvm

/-- Operations whose result is poison whenever any operand is poison. -/
def Llvm.propagatesPoison : Llvm → Bool
  | .and | .or | .xor | .add | .sub | .mul | .sdiv | .udiv | .srem | .urem
  | .shl | .lshr | .ashr | .icmp | .trunc | .sext | .zext | .bitcast
  | .intr__ctlz | .intr__cttz | .intr__ctpop | .intr__bswap
  | .intr__bitreverse | .intr__fshl | .intr__fshr
  | .intr__smax | .intr__smin | .intr__umax | .intr__umin | .intr__abs
  | .intr__sadd__sat | .intr__uadd__sat | .intr__ssub__sat | .intr__usub__sat
  | .intr__sshl__sat | .intr__ushl__sat => true
  -- The floating-point arithmetic operations propagate poison too, but no
  -- `RuntimeValue` represents a poisoned float yet, so listing them here would
  -- claim a fold that cannot be materialized.
  | .fadd | .fsub | .fmul | .fdiv | .frem
  | .mlir__constant | .mlir__poison | .mlir__zero | .mlir__global | .mlir__addressof
  | .select | .br | .cond_br | .switch | .unreachable | .alloca | .load | .store
  | .intr__lifetime__start | .intr__lifetime__end | .intr__assume
  | .getelementptr | .call | .return | .func | .module_flags | .freeze => false

instance : IsOpCode Llvm where
  fromName := Llvm.fromName
  name := Llvm.name
  propertiesOf := Llvm.propertiesOf
  fromAttrDict := Llvm.fromAttrDict
  toAttrDict := Llvm.toAttrDict

def Llvm.functionInterface? (op : Llvm) : Option (FunctionOpInterface (Llvm.propertiesOf op)) :=
  match op with
  | .func =>
    some
      { getSymName := fun props => props.sym_name
        getFunctionType := fun props => props.function_type
        setFunctionType := fun props functionType =>
          { props with function_type := functionType } }
  | _ => none

/-- Whether `n` is a valid LLVM alignment: a strictly positive power of two. -/
def isValidLLVMAlignment (n : Int) : Bool :=
  decide (0 < n) && (n.toNat &&& (n.toNat - 1)) == 0

/-- Check an `llvm.return` against its enclosing `llvm.func`'s declared results. -/
def OperationPtr.verifyLLVMFuncReturnTypes {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Llvm] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) (funcOp : OperationPtr) : Except String PUnit := do
  let props : Llvm.propertiesOf .func := funcOp.getProperties! ctx.raw Llvm.func
  let functionType := props.function_type
  -- A single `llvm.void` result corresponds to no return operands.
  let outputs := match functionType.outputs with
    | #[.llvmVoidType _] => #[]
    | outputs => outputs
  if op.getNumOperands ctx.raw opIn ≠ outputs.size then
    throw s!"Expected llvm.return to have {outputs.size} operand(s)"
  let opTypes := op.getOperandTypes! ctx.raw
  for i in [0:outputs.size] do
    if !Attribute.branchArgCompatible (opTypes[i]!).val outputs[i]! then
      throw s!"llvm.return operand {i} type does not match the function's declared result type"

/-- Check an `llvm.return` against its `llvm.mlir.global`'s `global_type`. -/
def OperationPtr.verifyLLVMGlobalReturnTypes {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Llvm] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) (globalOp : OperationPtr) : Except String PUnit := do
  let globalType :=
    (globalOp.getProperties! ctx.raw Llvm.mlir__global).global_type
  if op.getNumOperands ctx.raw opIn ≠ 1 then
    throw "Expected llvm.return in llvm.mlir.global to have 1 operand"
  let opTypes := op.getOperandTypes! ctx.raw
  if (opTypes[0]!).val ≠ globalType.val then
    throw "llvm.return operand type does not match the global's declared global_type"

/--
Check an `llvm.return`'s operands against its enclosing `llvm.func` or
`llvm.mlir.global`.
-/
def OperationPtr.verifyLLVMReturnTypes {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Llvm] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let enclosingOp ← op.getEnclosingFunctionOp ctx "llvm.return"
  let badEnclosure : Except String PUnit :=
    throw "Expected llvm.return to be enclosed by llvm.func or llvm.mlir.global"
  match toDialect? Llvm (enclosingOp.getOpType! ctx.raw) with
  | some .func => op.verifyLLVMFuncReturnTypes ctx opIn enclosingOp
  | some .mlir__global => op.verifyLLVMGlobalReturnTypes ctx opIn enclosingOp
  | _ => badEnclosure

def OperationPtr.verifyLLVMShift {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyIntegerOrByteType
    s!"{instrName}: Expected operand 0 to have integer or byte type"
  ((op.getOperand! ctx.raw 1).getType! ctx.raw).verifyIntegerType
    s!"{instrName}: Expected operand 1 to have integer type"
  op.verifyResultTypeMatches ctx ((op.getOperand! ctx.raw 0).getType! ctx.raw)
    s!"{instrName}: Expected result type to match first operand type"

def OperationPtr.verifyLLVMICmp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  -- `llvm.icmp` also compares pointers.
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyIntegerOrPointerType
    s!"{instrName}: Expected operand 0 to have integer or pointer type"
  ((op.getOperand! ctx.raw 1).getType! ctx.raw).verifyIntegerOrPointerType
    s!"{instrName}: Expected operand 1 to have integer or pointer type"
  let _ ← op.verifyOperandTypesMatch ctx 0 1
    s!"{instrName}: Expected operands to have the same type"
  ((op.getResult 0).get! ctx.raw).type.verifyI1 s!"{instrName}: Expected i1 result"

/--
Verify the local invariants of an `llvm` operation in any operation-info type
containing the `llvm` dialect.
-/
def Llvm.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Llvm] (opType : Llvm) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .mlir__constant => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 0 1
    -- Unlike `arith.constant`, `llvm.mlir.constant` does not require the value
    -- attribute's type to match the result type exactly.
    let resultType := ((op.getResult 0).get! ctx.raw).type.val
    match (op.getProperties! ctx.raw Llvm.mlir__constant).value with
    | .integer _ =>
      match resultType with
      | .integerType _ => pure ()
      | _ => throw "llvm.mlir.constant: Expected integer result type for an integer constant"
    | .float floatAttr =>
      match resultType with
      | .floatType floatType =>
        if floatType.bitwidth ≠ floatAttr.type.bitwidth then
          throw s!"llvm.mlir.constant: Expected float result type with bitwidth {floatAttr.type.bitwidth}"
      | .integerType intType =>
        if intType.bitwidth ≠ floatAttr.type.bitwidth then
          throw s!"llvm.mlir.constant: Expected integer result type with bitwidth {floatAttr.type.bitwidth}"
      | _ => throw "llvm.mlir.constant: Expected float or integer result type for a float constant"
    | .dense denseAttr =>
      match resultType with
      | .llvmArrayType { type := .llvmArrayType _, .. } => pure ()
      | .llvmArrayType arrType =>
        match denseElementsElementType? denseAttr.type with
        | some elemType =>
          let baseType := toString arrType.type
          if elemType ≠ baseType then
            throw s!"llvm.mlir.constant: dense elements type '{elemType}' does not match array element type '{baseType}'"
        | none => pure ()
      | .vectorType vecType =>
        match denseElementsElementType? denseAttr.type with
        | some elemType =>
          let baseType := toString vecType.elementType
          if elemType ≠ baseType then
            throw s!"llvm.mlir.constant: dense elements type '{elemType}' does not match vector element type '{baseType}'"
        | none => pure ()
      | _ =>
        throw "llvm.mlir.constant: Expected array or vector result type for a dense elements constant"
    | .string stringAttr =>
      match resultType with
      | .llvmArrayType arrType =>
        if arrType.type ≠ .integerType ⟨8⟩ then
          throw "llvm.mlir.constant: Expected array<N x i8> result type for a string constant"
        if stringAttr.value.size ≠ arrType.size then
          throw s!"llvm.mlir.constant: string length {stringAttr.value.size} does not match declared array size {arrType.size}"
      | _ => throw "llvm.mlir.constant: Expected array result type for a string constant"
      pure ()
  | .mlir__poison => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 0 1
    pure ()
  | .mlir__global => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "Expected 1 region"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    let properties := op.getProperties! ctx.raw Llvm.mlir__global
    if let some alignment := properties.alignment then
      if alignment.type.bitwidth ≠ 64 then
        throw "'alignment' must be a 64-bit signless integer attribute"
      if !isValidLLVMAlignment alignment.value then
        throw "alignment attribute is not a power of 2"
    if properties.addr_space.type.bitwidth ≠ 32 then
      throw "'addr_space' must be a 32-bit signless integer attribute"
    if let some value := properties.value then
      let body := (op.getRegion! ctx.raw 0).get! ctx.raw
      if body.firstBlock.isSome then
        throw "cannot have both initializer value and region"
      if properties.linkage.value == "common" && value.isKnownNonZero then
        throw "expected zero value for 'common' linkage"
    pure ()
  | .mlir__zero => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 0 1
    let resultType := ((op.getResult 0).get! ctx.raw).type
    match resultType.val with
    | .llvmVoidType _ | .llvmFunctionType _ =>
      throw "llvm.mlir.zero: Expected result to have a type with a zero value"
    | _ => pure ()
  | .intr__lifetime__start | .intr__lifetime__end => do
    op.verifyPlainOpCounts ctx opIn 1 0
    let operandType := (op.getOperand! ctx.raw 0).getType! ctx.raw
    let .llvmPointerType _ := operandType.val
      | throw "Expected operand 0 to have !llvm.ptr type"
    pure ()
  | .intr__assume => do
    op.checkIsNonNullIntegerType ctx opIn
    let props := op.getProperties! ctx.raw Llvm.intr__assume
    let sizes := props.op_bundle_sizes
    if sizes.elementType.bitwidth ≠ 32 then
      throw "llvm.intr.assume: Expected 'op_bundle_sizes' to be an i32 dense array attribute"
    if sizes.values.any (· < 0) then
      throw "llvm.intr.assume: op_bundle_sizes contains a negative size"
    let bundleOperands := (sizes.values.foldl (· + ·) 0).toNat
    let numOperands := op.getNumOperands ctx.raw opIn
    if numOperands ≠ 1 + bundleOperands then
      throw s!"llvm.intr.assume: Expected 1 condition and {bundleOperands} operand bundle \
        operand(s) per 'op_bundle_sizes', but got {numOperands} operand(s)"
    op.verifyPlainOpCounts ctx opIn numOperands 0
    ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyI1 "llvm.intr.assume: Expected i1 condition"
    let tags := (props.op_bundle_tags.map (·.value)).getD #[]
    if tags.size ≠ sizes.values.size then
      throw s!"llvm.intr.assume: Expected {sizes.values.size} operand bundle tag(s), \
        but got {tags.size}"
    for tag in tags do
      let .stringAttr _ := tag
        | throw "llvm.intr.assume: Expected operand bundle tags to be string attributes"
  | .mlir__addressof => do
    op.verifyPlainOpCounts ctx opIn 0 1
    let resultType := ((op.getResult 0).get! ctx.raw).type
    let .llvmPointerType _ := resultType.val
      | throw "Expected result to have !llvm.ptr type"
    pure ()
  | .and | .or | .xor | .intr__smax | .intr__smin
  | .intr__umax | .intr__umin | .add | .sub | .ashr | .mul | .sdiv | .udiv
  | .srem | .urem | .intr__sadd__sat | .intr__uadd__sat
  | .intr__ssub__sat | .intr__usub__sat | .intr__sshl__sat | .intr__ushl__sat => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyIntegerBinop ctx opIn
    pure ()
  | .lshr | .shl => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyLLVMShift ctx opIn
    pure ()
  | .intr__abs => do
    op.checkIsNonNullIntegerType ctx opIn
    let _ ← op.verifyIntegerUnop ctx opIn
    pure ()
  | .intr__fshl | .intr__fshr => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyIntegerTernop ctx opIn
    pure ()
  | .intr__ctlz | .intr__cttz | .intr__ctpop | .intr__bitreverse => do
    op.checkIsNonNullIntegerType ctx opIn
    let _ ← op.verifyIntegerUnop ctx opIn
    pure ()
  | .intr__bswap => do
    op.checkIsNonNullIntegerType ctx opIn
    let operandType ← op.verifyIntegerUnop ctx opIn
    let .integerType intType := operandType.val
      | throw "llvm.intr.bswap: Expected operand 0 to have integer type"
    if intType.bitwidth ∉ [16, 32, 64] then
      throw "llvm.intr.bswap: bitwidth must be 16, 32, or 64"
    pure ()
  | .icmp => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyLLVMICmp ctx opIn
    pure ()
  | .select => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifySelectTypes ctx opIn
    pure ()
  | .trunc => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyTruncTypes ctx opIn true
    pure ()
  | .sext | .zext => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyIntegerExtTypes ctx opIn
    pure ()
  | .return => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyTerminatorCounts ctx opIn 0
    op.verifyLLVMReturnTypes ctx opIn
  | .unreachable => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 0 0
    pure ()
  | .br => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyUnconditionalBranch ctx opIn
  | .switch => do
    op.checkIsNonNullIntegerType ctx opIn
    let props := op.getProperties! ctx.raw Llvm.switch
    let caseSegments := props.case_operand_segments.values
    op.verifyTerminatorCounts ctx opIn (caseSegments.size + 1)
    let sizes ← op.verifyOperandSegmentSizes ctx opIn props.operandSegmentSizes 3
    if sizes[0]! ≠ 1 then
      throw s!"llvm.switch: expected a single value operand, got {sizes[0]!}"
    /- The default destination takes the second operand segment. -/
    let defaultDest := op.getSuccessor! ctx.raw 0
    if sizes[1]! ≠ defaultDest.getNumArguments! ctx.raw then
      throw s!"llvm.switch: default operand segment expected operand count \
        {defaultDest.getNumArguments! ctx.raw}, got {sizes[1]!}"
    op.verifyBranchSuccessorArgTypes ctx (1 : Nat) defaultDest "llvm.switch: default successor"
    /- `case_operand_segments` splits the third segment one group per case. -/
    let mut base := 1 + sizes[1]!
    for i in [0:caseSegments.size] do
      let count := caseSegments[i]!
      if count < 0 then
        throw s!"llvm.switch: case_operand_segments contains negative size {count}"
      let dest := op.getSuccessor! ctx.raw (i + 1)
      if count.toNat ≠ dest.getNumArguments! ctx.raw then
        throw s!"llvm.switch: case {i} operand segment expected operand count \
          {dest.getNumArguments! ctx.raw}, got {count.toNat}"
      op.verifyBranchSuccessorArgTypes ctx base dest s!"llvm.switch: case {i} successor"
      base := base + count.toNat
    if base ≠ 1 + sizes[1]! + sizes[2]! then
      throw s!"llvm.switch: case_operand_segments describes {base - 1 - sizes[1]!} case \
        operands, but operandSegmentSizes reserves {sizes[2]!}"
  | .cond_br => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyTerminatorCounts ctx opIn 2
    let weights := (op.getProperties! ctx.raw Llvm.cond_br).branch_weights
    if weights.values.size ≠ 2 && weights.values.size ≠ 0 then
      throw "Expected 0 or 2 branch weights"
    let sizes := (op.getProperties! ctx.raw Llvm.cond_br).operandSegmentSizes
    op.verifyCondBranchOperandSegmentSizes ctx opIn sizes 1
  | .alloca => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 1 1
    let properties := op.getProperties! ctx.raw Llvm.alloca
    if properties.alignment.type.bitwidth ≠ 64 then
      throw "'llvm.alloca' op attribute 'alignment' failed to satisfy constraint: 64-bit signless integer attribute"
    pure ()
  | .load => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 1 1
    let properties := op.getProperties! ctx.raw Llvm.load
    if properties.alignment.type.bitwidth ≠ 64 then
      throw "'llvm.load' op attribute 'alignment' failed to satisfy constraint: 64-bit signless integer attribute"
    pure ()
  | .store => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 2 0
    let properties := op.getProperties! ctx.raw Llvm.store
    if properties.alignment.type.bitwidth ≠ 64 then
      throw "'llvm.store' op attribute 'alignment' failed to satisfy constraint: 64-bit signless integer attribute"
    pure ()
  | .getelementptr => do
    op.checkIsNonNullIntegerType ctx opIn
    let props := op.getProperties! ctx.raw Llvm.getelementptr
    let dynamicCount := props.rawConstantIndices.values.filter (· == -2147483648) |>.size
    if op.getNumOperands ctx.raw opIn ≠ 1 + dynamicCount then
      throw s!"Expected {1 + dynamicCount} operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .call => do
    op.checkIsNonNullIntegerType ctx opIn
    if op.getNumResults ctx.raw opIn > 1 then
      throw "Expected at most 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .func => do
    op.checkIsNonNullIntegerType ctx opIn
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "Expected 1 region"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
  | .fadd | .fsub | .fmul | .fdiv | .frem => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .module_flags => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 0 0
    pure ()
  | .freeze => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 1 1
    op.verifyResultTypeMatches ctx ((op.getOperand! ctx.raw 0).getType! ctx.raw)
      "llvm.freeze: Expected result type to match operand type"
    pure ()
  | .bitcast => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 1 1
    if Attribute.bitwidthOfType ((op.getOperand! ctx.raw 0).getType! ctx.raw) ≠
        Attribute.bitwidthOfType (op.getResultTypes! ctx.raw)[0]! then
      throw "llvm.bitcast: Expected types of the same bitwidth"
    pure ()

/-- Materialize constants produced by folding LLVM dialect operations. -/
def Llvm.materializeConstant {OpInfo : Type} [HasOpInfo OpInfo] [HasDialect OpInfo Llvm]
    (_op : Llvm) (value : RuntimeValue) (type : TypeAttr) : Option (Materialized OpInfo) :=
  match value, type.val with
  | .int bw (.val value), .integerType intType =>
    if bw = intType.bitwidth then
      some (.of Llvm.mlir__constant
        (LLVMConstantProperties.mk (.integer (IntegerAttr.mk value.toInt intType))))
    else none
  | .int bw .poison, .integerType intType =>
    if bw = intType.bitwidth then some (.of Llvm.mlir__poison ()) else none
  | .float type value, .floatType floatType =>
    -- Materialize the constant as long as the runtime float type matches the result type.
    if type = floatType then
      some (.of Llvm.mlir__constant
        (LLVMConstantProperties.mk (.float (FloatAttr.mk type value))))
    else none
  | _, _ => none

instance : HasOpInfo Llvm where
  verifyLocalInvariants := Llvm.verifyLocalInvariants
  propagatesPoison := Llvm.propagatesPoison
  getEffects := Llvm.getEffects
  isConstantLike := Llvm.isConstantLike
  functionInterface? := Llvm.functionInterface?
  hasSSADominance := Llvm.hasSSADominance
  isTerminator := Llvm.isTerminator
  isIsolatedFromAbove := Llvm.isIsolatedFromAbove

end

end Veir
