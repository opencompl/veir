module

public import Veir.OpCode
public import Veir.IR.Attribute
public import Veir.IR.Simp
public import Veir.ForLean
public import Veir.IR.OpInfo

namespace Veir

public section

/--
  Properties of the `arith.constant` operation.
-/
structure ArithConstantProperties where
  value : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def ArithConstantProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String ArithConstantProperties := do
  if attrDict.size > 1 then
    throw s!"arith.constant: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "arith.constant: missing 'value' property"
  let .integerAttr intAttr := attr
    | throw s!"arith.constant: expected 'value' to be an integer attribute, but got {attr}"
  return { value := intAttr }

/--
  Properties of operations that can have `nsw` and `nuw` flags, such as `arith.addi`, `arith.muli`,
  `llvm.add`, or `llvm.mul`.
-/
structure NswNuwProperties where
  nsw : Bool
  nuw : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def NswNuwProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String NswNuwProperties := do
  let nsw ← match attrDict["nsw".toUTF8]? with
    | some (.unitAttr _) => .ok true
    | some attr => .error s!"expected 'nsw' to be an optional unit attribute, but got {attr}"
    | none => .ok false
  let nuw ← match attrDict["nuw".toUTF8]? with
    | some (.unitAttr _) => .ok true
    | some attr => .error s!"expected 'nuw' to be an optional unit attribute, but got {attr}"
    | none => .ok false
  return { nsw := nsw, nuw := nuw }

/--
  Properties of operations that can have the `exact` flags, such as
  `llvm.udiv`, or `llvm.sdiv`.
-/
structure ExactProperties where
  exact : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def ExactProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String ExactProperties := do
  let exact ← match attrDict["exact".toUTF8]? with
    | some (.unitAttr _) => .ok true
    | some attr => .error s!"expected 'exact' to be an optional unit attribute, but got {attr}"
    | none => .ok false
  return { exact := exact }

/--
  Properties of operations that can have the `disjoint` flags, such as
  `llvm.or`.
-/
structure DisjointProperties where
  disjoint : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def DisjointProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String DisjointProperties := do
  let disjoint ← match attrDict["disjoint".toUTF8]? with
    | some (.unitAttr _) => .ok true
    | some attr => .error s!"expected 'disjoint' to be an optional unit attribute, but got {attr}"
    | none => .ok false
  return { disjoint := disjoint }

/--
  Properties of operations that can have the `nneg` flag, such as `llvm.zext`.
-/
structure NnegProperties where
  nneg : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def NnegProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String NnegProperties := do
  let nneg ← match attrDict["nneg".toUTF8]? with
    | some (.unitAttr _) => .ok true
    | some attr => .error s!"expected 'nneg' to be an optional unit attribute, but got {attr}"
    | none => .ok false
  return { nneg := nneg }

/--
  Properties of the `llvm.constant` operation.
-/
structure LLVMConstantProperties where
  value : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def LLVMConstantProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String LLVMConstantProperties := do
  if attrDict.size > 1 then
    throw s!"llvm.constant: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "llvm.constant: missing 'value' property"
  let .integerAttr intAttr := attr
    | throw s!"llvm.constant: expected 'value' to be an integer attribute, but got {attr}"
  return { value := intAttr }

/--
  Properties of `llvm.icmp` operation, describing predicates for integer comparison.
-/
structure IcmpProperties where
  value : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def IcmpProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String IcmpProperties := do
  if attrDict.size > 1 then
    throw s!"llvm.icmp: expected only one property, but got {attrDict.size} properties"
  let some attr := attrDict["predicate".toUTF8]?
    | throw "llvm.icmp: missing predicate"
  let .integerAttr intAttr := attr
    | throw s!"llvm.icmp: expected predicate to be a string attribute, but got {attr}"
  return { value := intAttr }

/--
  Properties of the RISC-V immediate operations.
-/
structure RISCVImmediateProperties where
  value : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def RISCVImmediateProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String RISCVImmediateProperties := do
  if attrDict.size > 1 then
    throw s!"RISC-V immediate operation: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "RISC-V immediate operation: missing 'value' property"
  let .integerAttr intAttr := attr
    | throw s!"RISC-V immediate operation: expected 'value' to be an integer attribute, but got {attr}"
  return { value := intAttr }

/--
  Properties of the `mod_arith.constant` operation.
-/
structure ModArithConstantProperties where
  value : IntegerAttr
deriving Inhabited, Repr, Hashable, DecidableEq

def ModArithConstantProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String ModArithConstantProperties := do
  if attrDict.size > 1 then
    throw s!"mod_arith.constant: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "mod_arith.constant: missing 'value' property"
  let .integerAttr intAttr := attr
    | throw s!"mod_arith.constant: expected 'value' to be an integer attribute, but got {attr}"
  return { value := intAttr }

@[expose, properties_of]
def Arith.propertiesOf (op : Arith) : Type :=
match op with
| .constant => ArithConstantProperties
| .addi => NswNuwProperties
| .subi => NswNuwProperties
| .muli => NswNuwProperties
| .divsi => ExactProperties
| .divui => ExactProperties
| .shli => NswNuwProperties
| .shrsi => ExactProperties
| .shrui => ExactProperties
| .ori => DisjointProperties
| .trunci => NswNuwProperties
| .extui => NnegProperties
| _ => Unit

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
| _ => Unit

@[expose, properties_of]
def Riscv.propertiesOf (op : Riscv) : Type :=
match op with
| .li => RISCVImmediateProperties
| .lui => RISCVImmediateProperties
| .auipc => RISCVImmediateProperties
| .andi => RISCVImmediateProperties
| .ori => RISCVImmediateProperties
| .xori => RISCVImmediateProperties
| .addi => RISCVImmediateProperties
| .slti => RISCVImmediateProperties
| .sltiu => RISCVImmediateProperties
| .addiw => RISCVImmediateProperties
| .slli => RISCVImmediateProperties
| .srli => RISCVImmediateProperties
| .srai => RISCVImmediateProperties
| .slliw => RISCVImmediateProperties
| .srliw => RISCVImmediateProperties
| .sraiw => RISCVImmediateProperties
| .slliuw => RISCVImmediateProperties
| .rori => RISCVImmediateProperties
| .roriw => RISCVImmediateProperties
| .bclri => RISCVImmediateProperties
| .bexti => RISCVImmediateProperties
| .binvi => RISCVImmediateProperties
| .bseti => RISCVImmediateProperties
| _ => Unit

@[expose, properties_of]
def Mod_Arith.propertiesOf (op : Mod_Arith) : Type :=
match op with
| .constant => ModArithConstantProperties
| .add | .sub | .mul => Unit

instance : HasDialectOpInfo Arith where
  propertiesOf := Arith.propertiesOf

instance : HasDialectOpInfo Llvm where
  propertiesOf := Llvm.propertiesOf

instance : HasDialectOpInfo Riscv where
  propertiesOf := Riscv.propertiesOf

instance : HasDialectOpInfo Mod_Arith where
  propertiesOf := Mod_Arith.propertiesOf

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
  case cf =>
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
  | _ =>
    Std.HashMap.emptyWithCapacity 0

end
end Veir
