module

public import Veir.OpCode
public import Veir.IR.Attribute
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


/--
  A type family that maps an operation code to the type of its properties.
  For operations that do not have any properties, the type is `Unit`.
-/
@[expose]
def propertiesOf (opCode : OpCode) : Type :=
match opCode with
| .arith .constant => ArithConstantProperties
| .llvm .constant => LLVMConstantProperties
| .arith .addi => NswNuwProperties
| .arith .subi => NswNuwProperties
| .arith .muli => NswNuwProperties
| .arith .divsi => ExactProperties
| .arith .divui => ExactProperties
| .arith .shli => NswNuwProperties
| .arith .shrsi => ExactProperties
| .arith .shrui => ExactProperties
| .arith .ori => DisjointProperties
| .llvm .add => NswNuwProperties
| .llvm .sub => NswNuwProperties
| .llvm .mul => NswNuwProperties
| .llvm .udiv => ExactProperties
| .llvm .sdiv => ExactProperties
| .llvm .shl => NswNuwProperties
| .llvm .lshr => ExactProperties
| .llvm .ashr => ExactProperties
| .llvm .or => DisjointProperties
| .llvm .trunc => NswNuwProperties
| .llvm .zext => NnegProperties
| .llvm .icmp => IcmpProperties
| .arith .trunci => NswNuwProperties
| .arith .extui => NnegProperties
| .riscv .li => RISCVImmediateProperties
| .riscv .lui => RISCVImmediateProperties
| .riscv .auipc => RISCVImmediateProperties
| .riscv .andi => RISCVImmediateProperties
| .riscv .ori => RISCVImmediateProperties
| .riscv .xori => RISCVImmediateProperties
| .riscv .addi => RISCVImmediateProperties
| .riscv .slti => RISCVImmediateProperties
| .riscv .sltiu => RISCVImmediateProperties
| .riscv .addiw => RISCVImmediateProperties
| .riscv .slli => RISCVImmediateProperties
| .riscv .srli => RISCVImmediateProperties
| .riscv .srai => RISCVImmediateProperties
| .riscv .slliw => RISCVImmediateProperties
| .riscv .srliw => RISCVImmediateProperties
| .riscv .sraiw => RISCVImmediateProperties
| .riscv .slliuw => RISCVImmediateProperties
| .riscv .rori => RISCVImmediateProperties
| .riscv .roriw => RISCVImmediateProperties
| .riscv .bclri => RISCVImmediateProperties
| .riscv .bexti => RISCVImmediateProperties
| .riscv .binvi => RISCVImmediateProperties
| .riscv .bseti => RISCVImmediateProperties
| .mod_arith .constant => ModArithConstantProperties
| _ => Unit

instance : HasOpInfo OpCode where
  moduleOpCode := .builtin .module
  propertiesOf := propertiesOf
  propertiesHash := by
    unfold propertiesOf
    intros opCode
    cases opCode <;> (try simp) <;> (rename_i op; cases op <;> infer_instance)
  propertiesDefault := by
    unfold propertiesOf
    intros opCode
    cases opCode <;> (try simp) <;> (rename_i op; cases op <;> infer_instance)
  propertiesRepr := by
    unfold propertiesOf
    intros opCode
    cases opCode <;> (try simp) <;> (rename_i op; cases op <;> infer_instance)
  propertiesDecideEq := by
    unfold propertiesOf
    intros opCode
    cases opCode <;> (try simp) <;> (rename_i op; cases op <;> infer_instance)
  decideEq := by
    intros opCode1 opCode2
    cases opCode1 <;> cases opCode2 <;> infer_instance

instance (opCode : OpCode) : Inhabited (propertiesOf opCode) := by
  unfold propertiesOf
  cases opCode <;> (try simp) <;> (rename_i op; cases op <;> infer_instance)

instance (opCode : OpCode) : Repr (propertiesOf opCode) := by
  unfold propertiesOf
  cases opCode <;> (try simp) <;> (rename_i op; cases op <;> infer_instance)

instance (opCode : OpCode) : Hashable (propertiesOf opCode) := by
  unfold propertiesOf
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
