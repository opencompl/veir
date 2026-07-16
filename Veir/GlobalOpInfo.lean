module

public import Veir.Dialects.Arith.OpInfo
public import Veir.Dialects.LLVM.OpInfo
public import Veir.Dialects.RISCV.OpInfo
public import Veir.Dialects.RISCV_Cf.OpInfo
public import Veir.Dialects.RISCV_Stack.OpInfo
public import Veir.Dialects.RV64.OpInfo
public import Veir.Dialects.ModArith.OpInfo
public import Veir.Dialects.Cf.OpInfo
public import Veir.Dialects.Comb.OpInfo
public import Veir.Dialects.HW.OpInfo
public import Veir.IR.Basic

namespace Veir

public section

/--
  A type family that maps an operation code to the type of its properties.
  For operations that do not have any properties, the type is `Unit`.
-/
@[expose, properties_of]
def _propertiesOf (opCode : OpCode) : Type :=
match opCode with
| .arith op => Arith.propertiesOf op
| .llvm op => Llvm.propertiesOf op
| .riscv op => Riscv.propertiesOf op
| .riscv_cf op => Riscv_Cf.propertiesOf op
| .riscv_stack op => Riscv_Stack.propertiesOf op
| .rv64 op => Rv64.propertiesOf op
| .mod_arith op => Mod_Arith.propertiesOf op
| .cf op => Cf.propertiesOf op
| .comb op => Comb.propertiesOf op
| .hw op => HW.propertiesOf op
| .builtin .unregistered => UnregisteredProperties
| .func .func => FuncFuncProperties
| .func .call => FuncCallProperties
| _ => Unit

instance : HasDialectOpInfo OpCode where
  propertiesOf := _propertiesOf

inductive RegionKind where
| SSACFG
| Graph
deriving Inhabited, Repr, DecidableEq

/--
  Return the kind of the region with the given index inside this operation.
  This mirrors MLIR's RegionKindInterface default: regions are SSACFG unless
  the operation is known to define graph regions.
-/
def OpCode.getRegionKind (opCode : OpCode) (_index : Nat) : RegionKind :=
  match opCode with
  | .builtin .module
  | .builtin .unregistered
  | .test .test => .Graph
  | _ => .SSACFG

instance : HasOpInfo OpCode where
  moduleOpCode := .builtin .module
  hasSSADominance opCode index := opCode.getRegionKind index == .SSACFG

abbrev propertiesOf := HasOpInfo.propertiesOf (self := instHasOpInfoOpCode)

def Properties.fromAttrDict (opCode : OpCode) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (propertiesOf opCode) := by
  cases opCode
  case test =>
    all_goals exact (Except.ok ())
  case datapath =>
    all_goals exact (Except.ok ())
  case mod_arith op =>
    cases op
    case constant => exact (ModArithConstantProperties.fromAttrDict attrDict)
    all_goals exact (Except.ok ())
  case riscv op =>
    cases op
    case li => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case lui => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case auipc => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case andi => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case ori => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case xori => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case addi => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case slti => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case sltiu => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case addiw => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case slli => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case srli => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case srai => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case slliw => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case srliw => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case sraiw => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case slliuw => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case rori => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case roriw => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case bclri => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case bexti => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case binvi => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case bseti => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case ld => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case lw => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case lwu => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case lh => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case lhu => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case lb => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case lbu => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case sd => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case sw => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case sh => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    case sb => exact (RISCVImmediateProperties.fromAttrDict attrDict)
    all_goals exact (Except.ok ())
  case riscv_cf op =>
    cases op
    case beq => exact (RISCVBrProperties.fromAttrDict attrDict)
    case bne => exact (RISCVBrProperties.fromAttrDict attrDict)
    case blt => exact (RISCVBrProperties.fromAttrDict attrDict)
    case bge => exact (RISCVBrProperties.fromAttrDict attrDict)
    case bltu => exact (RISCVBrProperties.fromAttrDict attrDict)
    case bgeu => exact (RISCVBrProperties.fromAttrDict attrDict)
    case beqz => exact (RISCVBrProperties.fromAttrDict attrDict)
    case bnez => exact (RISCVBrProperties.fromAttrDict attrDict)
    all_goals exact (Except.ok ())
  case riscv_stack op =>
    cases op
    case alloca => exact (RISCVStackAllocaProperties.fromAttrDict attrDict)
    all_goals exact (Except.ok ())
  case rv64 =>
    exact Except.ok ()
  case llvm op =>
    cases op
    case mlir__constant => exact (LLVMConstantProperties.fromAttrDict attrDict)
    case add => exact (NswNuwProperties.fromAttrDict attrDict)
    case sub => exact (NswNuwProperties.fromAttrDict attrDict)
    case mul => exact (NswNuwProperties.fromAttrDict attrDict)
    case udiv => exact (ExactProperties.fromAttrDict attrDict)
    case sdiv => exact (ExactProperties.fromAttrDict attrDict)
    case shl => exact (NswNuwProperties.fromAttrDict attrDict)
    case lshr => exact (ExactProperties.fromAttrDict attrDict)
    case ashr => exact (ExactProperties.fromAttrDict attrDict)
    case intr__ctlz => exact (ZeroPoisonProperties.fromAttrDictFor "llvm.intr.ctlz" attrDict)
    case intr__cttz => exact (ZeroPoisonProperties.fromAttrDictFor "llvm.intr.cttz" attrDict)
    case intr__abs => exact (IntMinPoisonProperties.fromAttrDict attrDict)
    case or => exact (DisjointProperties.fromAttrDict attrDict)
    case trunc => exact (NswNuwProperties.fromAttrDict attrDict)
    case zext => exact (NnegProperties.fromAttrDict attrDict)
    case icmp => exact (IcmpProperties.fromAttrDict attrDict)
    case cond_br => exact (CondBrProperties.fromAttrDict attrDict)
    case alloca => exact (AllocaProperties.fromAttrDict attrDict)
    case load => exact (LoadProperties.fromAttrDict attrDict)
    case store => exact (StoreProperties.fromAttrDict attrDict)
    case getelementptr => exact (GetelementptrProperties.fromAttrDict attrDict)
    case fadd => exact (FastMathFlagsProperties.fromAttrDict attrDict)
    case fsub => exact (FastMathFlagsProperties.fromAttrDict attrDict)
    case fmul => exact (FastMathFlagsProperties.fromAttrDict attrDict)
    case fdiv => exact (FastMathFlagsProperties.fromAttrDict attrDict)
    case frem => exact (FastMathFlagsProperties.fromAttrDict attrDict)
    case func => exact (LLVMFuncProperties.fromAttrDict attrDict)
    case module_flags => exact (LLVMModuleFlagsProperties.fromAttrDict attrDict)
    case call => exact (LLVMCallProperties.fromAttrDict attrDict)
    all_goals exact (Except.ok ())
  case func op =>
    cases op
    case func => exact (FuncFuncProperties.fromAttrDict attrDict)
    case call => exact (FuncCallProperties.fromAttrDict attrDict)
    all_goals exact (Except.ok ())
  case cf op =>
    cases op
    case cond_br => exact (CondBrProperties.fromAttrDict attrDict)
    all_goals exact (Except.ok ())
  case builtin op =>
    cases op
    case unregistered => exact (UnregisteredProperties.fromAttrDict attrDict)
    all_goals exact (Except.ok ())
  case arith op =>
    cases op
    case constant => exact (ArithConstantProperties.fromAttrDict attrDict)
    case addi => exact (ArithIntegerOverflowFlagsProperties.fromAttrDict attrDict)
    case subi => exact (ArithIntegerOverflowFlagsProperties.fromAttrDict attrDict)
    case muli => exact (ArithIntegerOverflowFlagsProperties.fromAttrDict attrDict)
    case divsi => exact (ExactProperties.fromAttrDict attrDict)
    case divui => exact (ExactProperties.fromAttrDict attrDict)
    case cmpi => exact (IcmpProperties.fromAttrDictFor "arith.cmpi" attrDict)
    case shli => exact (ArithIntegerOverflowFlagsProperties.fromAttrDict attrDict)
    case shrsi => exact (ExactProperties.fromAttrDict attrDict)
    case shrui => exact (ExactProperties.fromAttrDict attrDict)
    case ori => exact (DisjointProperties.fromAttrDict attrDict)
    case trunci => exact (ArithIntegerOverflowFlagsProperties.fromAttrDict attrDict)
    case extui => exact (NnegProperties.fromAttrDict attrDict)
    all_goals exact (Except.ok ())
  case comb op =>
    cases op
    case extract => exact (CombExtractProperties.fromAttrDict attrDict)
    case icmp => exact (CombIcmpProperties.fromAttrDict attrDict)
    all_goals exact (Except.ok ())
  case hw op =>
    cases op
    case constant => exact (HWConstantProperties.fromAttrDict attrDict)
    case module => exact (HWModuleProperties.fromAttrDict attrDict)
    all_goals exact (Except.ok ())

/--
  Converts the properties of an operation into a dictionary of attributes.
-/
def Properties.toAttrDict (opCode : OpCode) (props : propertiesOf opCode) :
    Std.HashMap ByteArray Attribute :=
  match opCode with
  | .arith .constant =>
    (Std.HashMap.emptyWithCapacity 2).insert "value".toUTF8 (Attribute.integerAttr props.value)
  | .llvm .mlir__constant =>
    match props.value with
    | .integer intAttr =>
      (Std.HashMap.emptyWithCapacity 1).insert "value".toUTF8 (Attribute.integerAttr intAttr)
    | .float floatAttr =>
      (Std.HashMap.emptyWithCapacity 1).insert "value".toUTF8 (Attribute.floatAttr floatAttr)
    | .dense denseAttr =>
      (Std.HashMap.emptyWithCapacity 1).insert "value".toUTF8 (Attribute.denseElementsAttr denseAttr)
  | .arith .addi | .arith .subi | .arith .muli | .arith .shli | .arith .trunci => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    if props.attr.nsw || props.attr.nuw then
      dict := dict.insert "overflowFlags".toUTF8 (Attribute.arithIntegerOverflowFlagsAttr props.attr)
    dict
  | .llvm .add | .llvm .sub | .llvm .mul | .llvm .shl | .llvm .trunc => Id.run do
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
  | .llvm .fadd | .llvm .fsub | .llvm .fmul | .llvm .fdiv | .llvm .frem => Id.run do
    (Std.HashMap.emptyWithCapacity 1).insert "fastmathFlags".toUTF8 (Attribute.fastMathFlagsAttr props.attr)
  | .arith .cmpi | .llvm .icmp => Id.run do
    let value := IntegerAttr.mk (Int.ofNat props.predicate.toNat) (IntegerType.mk 64)
    (Std.HashMap.emptyWithCapacity 1).insert "predicate".toUTF8 (Attribute.integerAttr value)
  | .llvm .cond_br =>
    let dict := (Std.HashMap.emptyWithCapacity 2).insert "branch_weights".toUTF8 (Attribute.denseArrayAttr props.branch_weights)
    dict.insert "operandSegmentSizes".toUTF8 (Attribute.denseArrayAttr props.operandSegmentSizes)
  | .arith .divsi | .arith .divui | .arith .shrsi | .arith .shrui |
    .llvm .udiv | .llvm .sdiv | .llvm .lshr | .llvm .ashr => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    if props.exact then
      dict := dict.insert "exact".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .arith .ori | .llvm .or => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    if props.disjoint then
      dict := dict.insert "disjoint".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .arith .extui | .llvm .zext => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    if props.nneg then
      dict := dict.insert "nneg".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .llvm .intr__ctlz | .llvm .intr__cttz =>
    let value := if props.is_zero_poison then 1 else 0
    let attr := IntegerAttr.mk value (IntegerType.mk 1)
    (Std.HashMap.emptyWithCapacity 1).insert "is_zero_poison".toUTF8 (Attribute.integerAttr attr)
  | .llvm .intr__abs =>
    let value := if props.is_int_min_poison then 1 else 0
    let attr := IntegerAttr.mk value (IntegerType.mk 1)
    (Std.HashMap.emptyWithCapacity 1).insert "is_int_min_poison".toUTF8 (Attribute.integerAttr attr)
  | .riscv .li  | .riscv .lui | .riscv .auipc | .riscv .andi | .riscv .ori | .riscv .xori
  | .riscv .addi | .riscv .slti | .riscv .sltiu | .riscv .addiw | .riscv .slli | .riscv .srli | .riscv .srai
  | .riscv .slliw | .riscv .srliw | .riscv .sraiw | .riscv .rori | .riscv .roriw | .riscv .slliuw
  | .riscv .bclri | .riscv .bexti | .riscv .binvi | .riscv .bseti | .riscv .ld | .riscv .sd
  | .riscv .lw | .riscv .lwu | .riscv .lh | .riscv .lhu | .riscv .lb | .riscv .lbu
  | .riscv .sw | .riscv .sh | .riscv .sb | .mod_arith .constant =>
    (Std.HashMap.emptyWithCapacity 2).insert "value".toUTF8 (Attribute.integerAttr props.value)
  | .riscv_stack .alloca => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    dict := dict.insert "alignment".toUTF8 (Attribute.integerAttr props.alignment)
    dict.insert "value_type".toUTF8 props.value_type
  | .riscv_cf .beq | .riscv_cf .bne | .riscv_cf .blt | .riscv_cf .bge
  | .riscv_cf .bltu | .riscv_cf .bgeu | .riscv_cf .beqz | .riscv_cf .bnez =>
    (Std.HashMap.emptyWithCapacity 1).insert "operandSegmentSizes".toUTF8 (Attribute.denseArrayAttr props.operandSegmentSizes)
  | .cf .cond_br =>
    let dict := (Std.HashMap.emptyWithCapacity 2).insert "branch_weights".toUTF8 (.denseArrayAttr props.branch_weights)
    dict.insert "operandSegmentSizes".toUTF8 (Attribute.denseArrayAttr props.operandSegmentSizes)
  | .llvm .alloca => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 3
    dict := dict.insert "alignment".toUTF8 (Attribute.integerAttr props.alignment)
    dict := dict.insert "elem_type".toUTF8 props.elem_type
    if props.inalloca then
      dict := dict.insert "inalloca".toUTF8 (.unitAttr UnitAttr.mk)
    dict
  | .llvm .load => Id.run do
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
  | .llvm .store => Id.run do
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
  | .llvm .getelementptr => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 3
    dict := dict.insert "rawConstantIndices".toUTF8 (Attribute.denseArrayAttr props.rawConstantIndices)
    dict := dict.insert "elem_type".toUTF8 props.elem_type
    dict := dict.insert "noWrapFlags".toUTF8 (.integerAttr props.noWrapFlags)
    dict
  | .comb .extract =>
    (Std.HashMap.emptyWithCapacity 1).insert "lowBit".toUTF8 (Attribute.integerAttr props.lowBit)
  | .comb .icmp =>
    (Std.HashMap.emptyWithCapacity 1).insert "predicate".toUTF8 (Attribute.integerAttr props.predicate)
  | .hw .constant => Id.run do
    (Std.HashMap.emptyWithCapacity 1).insert "value".toUTF8 (Attribute.integerAttr props.value)
  | .llvm .func => Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    if let some sym_name := props.sym_name then
      dict := dict.insert "sym_name".toUTF8 (.stringAttr sym_name)
    if let some function_type := props.function_type then
      dict := dict.insert "function_type".toUTF8 function_type
    dict
  | .llvm .module_flags => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 3
    dict := dict.insert "flags".toUTF8 (Attribute.arrayAttr props.flags)
    dict
  | .func .call => Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    dict := dict.insert "callee".toUTF8 (.flatSymbolRefAttr props.callee)
    dict
  | .llvm .call => Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    if let some callee := props.callee then
      dict := dict.insert "callee".toUTF8 (.flatSymbolRefAttr callee)
    dict
  | .func .func => Id.run do
    let mut dict := Std.HashMap.ofList props.extra.entries.toList
    if let some sym_name := props.sym_name then
      dict := dict.insert "sym_name".toUTF8 (.stringAttr sym_name)
    dict
  | .builtin .unregistered =>
    Std.HashMap.ofList props.properties.entries.toList
  | .hw .module => Id.run do
    let dict := Std.HashMap.emptyWithCapacity 4
    let dict := dict.insert "module_type".toUTF8 (.hwModuleType props.module_type)
    let dict := dict.insert "sym_name".toUTF8 (.stringAttr props.sym_name)
    let dict := dict.insert "per_port_attrs".toUTF8 (.arrayAttr props.per_port_attrs)
    let dict := dict.insert "parameters".toUTF8 (.arrayAttr props.parameters)
    dict
  | _ =>
    Std.HashMap.emptyWithCapacity 0

/--
  Does this OpCode count as an MLIR basic block terminator?
-/
def OpCode.isTerminator (opCode : OpCode) : Bool :=
  match opCode with
  | .cf .br | .cf .cond_br
  | .func .return
  | .llvm .br | .llvm .cond_br | .llvm .return | .llvm .unreachable
  | .riscv_cf .branch | .riscv_cf .beq | .riscv_cf .bne
  | .riscv_cf .beqz | .riscv_cf .bnez
  | .riscv_cf .blt | .riscv_cf .bge | .riscv_cf .bltu | .riscv_cf .bgeu
  | .hw .output => true
  | _ => false

/--
  Does this operation have effects that make it ineligible for DCE and
  other transformations that add / remove / rearrange instructions?

  NOTE: ¬ hasSideEffects does not imply that an operation is safe to
        speculate. For that we also need it to never trigger immediate
        UB. We'll have to deal with this later on.

  Also see:
  https://mlir.llvm.org/docs/Rationale/SideEffectsAndSpeculation/
-/
def OperationPtr.hasSideEffects (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  let opCode := op.getOpType! ctx
  if opCode.isTerminator then true else
  match opCode with
  -- These dialects are pure
  | .arith _ | .comb _ | .mod_arith _ | .datapath _ => false
  | .builtin .unrealized_conversion_cast => false
  | .hw .constant => false
  -- RISC-V is pure register arithmetic except the memory ops
  | .riscv .ld | .riscv .sd | .riscv .sw | .riscv .sh | .riscv .sb => true
  | .riscv _ => false
  -- For LLVM we enumerate the pure ops
  | .llvm .mlir__constant
  | .llvm .mlir__poison
  | .llvm .and | .llvm .or | .llvm .xor
  | .llvm .add | .llvm .sub | .llvm .mul
  | .llvm .sdiv | .llvm .udiv | .llvm .srem | .llvm .urem
  | .llvm .shl | .llvm .lshr | .llvm .ashr
  | .llvm .intr__ctlz | .llvm .intr__cttz | .llvm .intr__ctpop
  | .llvm .intr__bswap | .llvm .intr__bitreverse
  | .llvm .intr__fshl | .llvm .intr__fshr
  | .llvm .icmp | .llvm .select
  | .llvm .trunc | .llvm .sext | .llvm .zext
  | .llvm .getelementptr
  | .llvm .intr__smax | .llvm .intr__smin | .llvm .intr__umax | .llvm .intr__umin
  | .llvm .intr__abs
  | .llvm .intr__sadd__sat | .llvm .intr__uadd__sat
  | .llvm .intr__ssub__sat | .llvm .intr__usub__sat
  | .llvm .intr__sshl__sat | .llvm .intr__ushl__sat
  | .llvm .fadd | .llvm .fsub | .llvm .fmul | .llvm .fdiv | .llvm .frem => false
  -- Volatile loads are definitionally side-effecting
  | .llvm .load => (op.getProperties! ctx (.llvm .load)).volatile_
  -- For everything else: be conservative!
  | _ => true

/--
  Does this `OpCode` materialize a literal constant value (i.e. an op
  whose result is a compile-time constant taken from its attributes,
  with no SSA operands)?
-/
def OpCode.isConstantLike (opCode : OpCode) : Bool :=
  match opCode with
  | .arith .constant
  | .llvm .mlir__constant
  | .riscv .li => true
  | _ => false

/--
  Is this `OpCode` commutative in its operands, i.e. `op x y` always
  computes the same value as `op y x`?
-/
def OpCode.isCommutative (opCode : OpCode) : Bool :=
  match opCode with
  | .arith .addi | .arith .muli
  | .arith .andi | .arith .ori | .arith .xori
  | .arith .maxsi | .arith .maxui | .arith .minsi | .arith .minui
  | .arith .addui_extended
  | .arith .mulsi_extended | .arith .mului_extended
  | .llvm .add | .llvm .mul
  | .llvm .and | .llvm .or | .llvm .xor
  | .llvm .intr__smax | .llvm .intr__smin | .llvm .intr__umax | .llvm .intr__umin
  | .llvm .intr__sadd__sat | .llvm .intr__uadd__sat
  | .llvm .fadd | .llvm .fmul
  | .riscv .add | .riscv .and | .riscv .or | .riscv .xor | .riscv .xnor
  | .riscv .mul | .riscv .mulh | .riscv .mulhu
  | .riscv .max | .riscv .maxu | .riscv .min | .riscv .minu
  | .riscv .addw | .riscv .mulw => true
  | _ => false
