module

public import Veir.Dialects.Arith.OpInfo
public import Veir.Dialects.LLVM.OpInfo
public import Veir.Dialects.RISCV.OpInfo
public import Veir.Dialects.ModArith.OpInfo
public import Veir.Dialects.Cf.OpInfo

namespace Veir

public section

/--
  A type family that maps an operation code to the type of its properties.
  For operations that do not have any properties, the type is `Unit`.
-/
@[expose, properties_of]
def propertiesOf (opCode : OpCode) : Type :=
match opCode with
| .arith op => Arith.propertiesOf op
| .llvm op => Llvm.propertiesOf op
| .riscv op => Riscv.propertiesOf op
| .mod_arith op => Mod_Arith.propertiesOf op
| .cf op => Cf.propertiesOf op
| _ => Unit

instance : HasDialectOpInfo OpCode where
  propertiesOf := propertiesOf

instance : HasOpInfo OpCode where
  moduleOpCode := .builtin .module

instance (opCode : OpCode) : Inhabited (propertiesOf opCode) := by
  simp only [properties_of]
  cases opCode <;> (try simp) <;> (rename_i op; cases op <;> infer_instance)

instance (opCode : OpCode) : Repr (propertiesOf opCode) := by
  simp only [properties_of]
  cases opCode <;> (try simp) <;> (rename_i op; cases op <;> infer_instance)

instance (opCode : OpCode) : Hashable (propertiesOf opCode) := by
  simp only [properties_of]
  cases opCode <;> (try simp) <;> (rename_i op; cases op <;> infer_instance)

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
    all_goals exact (Except.ok ())
  case llvm op =>
    cases op
    case constant => exact (LLVMConstantProperties.fromAttrDict attrDict)
    case add => exact (NswNuwProperties.fromAttrDict attrDict)
    case sub => exact (NswNuwProperties.fromAttrDict attrDict)
    case mul => exact (NswNuwProperties.fromAttrDict attrDict)
    case udiv => exact (ExactProperties.fromAttrDict attrDict)
    case sdiv => exact (ExactProperties.fromAttrDict attrDict)
    case shl => exact (NswNuwProperties.fromAttrDict attrDict)
    case lshr => exact (ExactProperties.fromAttrDict attrDict)
    case ashr => exact (ExactProperties.fromAttrDict attrDict)
    case or => exact (DisjointProperties.fromAttrDict attrDict)
    case trunc => exact (NswNuwProperties.fromAttrDict attrDict)
    case zext => exact (NnegProperties.fromAttrDict attrDict)
    case icmp => exact (IcmpProperties.fromAttrDict attrDict)
    all_goals exact (Except.ok ())
  case func =>
    all_goals exact (Except.ok ())
  case cf op =>
    cases op
    case cond_br => exact (CondBrConstantProperties.fromAttrDict attrDict)
    all_goals exact (Except.ok ())
  case builtin =>
    all_goals exact (Except.ok ())
  case arith op =>
    cases op
    case constant => exact (ArithConstantProperties.fromAttrDict attrDict)
    case addi => exact (NswNuwProperties.fromAttrDict attrDict)
    case subi => exact (NswNuwProperties.fromAttrDict attrDict)
    case muli => exact (NswNuwProperties.fromAttrDict attrDict)
    case divsi => exact (ExactProperties.fromAttrDict attrDict)
    case divui => exact (ExactProperties.fromAttrDict attrDict)
    case shli => exact (NswNuwProperties.fromAttrDict attrDict)
    case shrsi => exact (ExactProperties.fromAttrDict attrDict)
    case shrui => exact (ExactProperties.fromAttrDict attrDict)
    case ori => exact (DisjointProperties.fromAttrDict attrDict)
    case trunci => exact (NswNuwProperties.fromAttrDict attrDict)
    case extui => exact (NnegProperties.fromAttrDict attrDict)
    all_goals exact (Except.ok ())

/--
  Converts the properties of an operation into a dictionary of attributes.
-/
def Properties.toAttrDict (opCode : OpCode) (props : propertiesOf opCode) :
    Std.HashMap ByteArray Attribute :=
  match opCode with
  | .arith .constant =>
    (Std.HashMap.emptyWithCapacity 2).insert "value".toUTF8 (Attribute.integerAttr props.value)
  | .llvm .constant =>
    (Std.HashMap.emptyWithCapacity 2).insert "value".toUTF8 (Attribute.integerAttr props.value)
  | .arith .addi | .arith .subi | .arith .muli | .arith .shli | .arith .trunci
  | .llvm .add | .llvm .sub | .llvm .mul | .llvm .shl | .llvm .trunc => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    if props.nsw then
      dict := dict.insert "nsw".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    if props.nuw then
      dict := dict.insert "nuw".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .llvm .icmp => Id.run do
    (Std.HashMap.emptyWithCapacity 2).insert "predicate".toUTF8 (Attribute.integerAttr props.value)
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
  | .riscv .li  | .riscv .lui | .riscv .auipc | .riscv .andi | .riscv .ori | .riscv .xori
  | .riscv .addi | .riscv .slti | .riscv .sltiu | .riscv .addiw | .riscv .slli | .riscv .srli | .riscv .srai
  | .riscv .slliw | .riscv .srliw | .riscv .sraiw | .riscv .rori | .riscv .roriw | .riscv .slliuw
  | .riscv .bclri | .riscv .bexti | .riscv .binvi | .riscv .bseti | .mod_arith .constant =>
    (Std.HashMap.emptyWithCapacity 2).insert "value".toUTF8 (Attribute.integerAttr props.value)
  | .cf .cond_br =>
    let dict := (Std.HashMap.emptyWithCapacity 2).insert "branch_weights".toUTF8 (Attribute.denseArrayAttr props.branch_weights)
    dict.insert "operandSegmentSizes".toUTF8 (Attribute.denseArrayAttr props.operandSegmentSizes)
  | _ =>
    Std.HashMap.emptyWithCapacity 0
