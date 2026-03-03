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
  A type family that maps an operation code to the type of its properties.
  For operations that do not have any properties, the type is `Unit`.
-/
@[expose]
def propertiesOf (opCode : OpCode) : Type :=
match opCode with
| .arith_constant => ArithConstantProperties
| .llvm_constant => LLVMConstantProperties
| .arith_addi => NswNuwProperties
| .arith_subi => NswNuwProperties
| .arith_muli => NswNuwProperties
| .arith_divsi => ExactProperties
| .arith_divui => ExactProperties
| .llvm_add => NswNuwProperties
| .llvm_sub => NswNuwProperties
| .llvm_mul => NswNuwProperties
| .llvm_udiv => ExactProperties
| .llvm_sdiv => ExactProperties
| .riscv_li => RISCVImmediateProperties
| .riscv_lui => RISCVImmediateProperties
| .riscv_auipc => RISCVImmediateProperties
| .riscv_andi => RISCVImmediateProperties
| .riscv_ori => RISCVImmediateProperties
| .riscv_xori => RISCVImmediateProperties
| .riscv_addi => RISCVImmediateProperties
| .riscv_slti => RISCVImmediateProperties
| .riscv_sltiu => RISCVImmediateProperties
| .riscv_addiw => RISCVImmediateProperties
| .riscv_slli => RISCVImmediateProperties
| .riscv_srli => RISCVImmediateProperties
| .riscv_srai => RISCVImmediateProperties
| _ => Unit

instance : HasOpInfo OpCode where
  propertiesOf := propertiesOf
  propertiesHash := by
    unfold propertiesOf
    intros opCode
    cases opCode <;> infer_instance
  propertiesDefault := by
    unfold propertiesOf
    intros opCode
    cases opCode <;> infer_instance
  propertiesRepr := by
    unfold propertiesOf
    intros opCode
    cases opCode <;> infer_instance
  propertiesDecideEq := by
    unfold propertiesOf
    intros opCode
    cases opCode <;> infer_instance
  decideEq := by
    intros opCode1 opCode2
    cases opCode1 <;> cases opCode2 <;> infer_instance

def Properties.fromAttrDict (opCode : OpCode) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (propertiesOf opCode) := by
  cases opCode
  case arith_constant => exact (ArithConstantProperties.fromAttrDict attrDict)
  case arith_addi => exact (NswNuwProperties.fromAttrDict attrDict)
  case arith_subi => exact (NswNuwProperties.fromAttrDict attrDict)
  case arith_muli => exact (NswNuwProperties.fromAttrDict attrDict)
  case arith_divsi => exact (ExactProperties.fromAttrDict attrDict)
  case arith_divui => exact (ExactProperties.fromAttrDict attrDict)
  case llvm_constant => exact (LLVMConstantProperties.fromAttrDict attrDict)
  case llvm_add => exact (NswNuwProperties.fromAttrDict attrDict)
  case llvm_sub => exact (NswNuwProperties.fromAttrDict attrDict)
  case llvm_mul => exact (NswNuwProperties.fromAttrDict attrDict)
  case llvm_udiv => exact (ExactProperties.fromAttrDict attrDict)
  case llvm_sdiv => exact (ExactProperties.fromAttrDict attrDict)
  case riscv_li => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_lui => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_auipc => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_andi => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_ori => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_xori => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_addi => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_slti => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_sltiu => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_addiw => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_slli => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_srli => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_srai => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  all_goals exact (Except.ok ())

/--
  Converts the properties of an operation into a dictionary of attributes.
-/
def Properties.toAttrDict (opCode : OpCode) (props : propertiesOf opCode) :
    Std.HashMap ByteArray Attribute :=
  match opCode with
  | .arith_constant =>
    (Std.HashMap.emptyWithCapacity 2).insert "value".toUTF8 (Attribute.integerAttr props.value)
  | .llvm_constant =>
    (Std.HashMap.emptyWithCapacity 2).insert "value".toUTF8 (Attribute.integerAttr props.value)
  | .arith_addi | .arith_subi | .arith_muli | .llvm_add | .llvm_sub | .llvm_mul => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    if props.nsw then
      dict := dict.insert "nsw".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    if props.nuw then
      dict := dict.insert "nuw".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .arith_divsi | .arith_divui | .llvm_udiv | .llvm_sdiv => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    if props.exact then
      dict := dict.insert "exact".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .riscv_li  | .riscv_lui | .riscv_auipc | .riscv_andi | .riscv_ori | .riscv_xori
  | .riscv_addi | .riscv_slti | .riscv_sltiu | .riscv_addiw | .riscv_slli | .riscv_srli | .riscv_srai =>
    (Std.HashMap.emptyWithCapacity 2).insert "value".toUTF8 (Attribute.integerAttr props.value)
  | _ =>
    Std.HashMap.emptyWithCapacity 0

end
end Veir
