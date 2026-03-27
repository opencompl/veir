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
| .arith_constant => ArithConstantProperties
| .llvm_constant => LLVMConstantProperties
| .arith_addi => NswNuwProperties
| .arith_subi => NswNuwProperties
| .arith_muli => NswNuwProperties
| .arith_divsi => ExactProperties
| .arith_divui => ExactProperties
| .arith_shli => NswNuwProperties
| .arith_shrsi => ExactProperties
| .arith_shrui => ExactProperties
| .arith_ori => DisjointProperties
| .llvm_add => NswNuwProperties
| .llvm_sub => NswNuwProperties
| .llvm_mul => NswNuwProperties
| .llvm_udiv => ExactProperties
| .llvm_sdiv => ExactProperties
| .llvm_shl => NswNuwProperties
| .llvm_lshr => ExactProperties
| .llvm_ashr => ExactProperties
| .llvm_or => DisjointProperties
| .llvm_trunc => NswNuwProperties
| .llvm_zext => NnegProperties
| .llvm_icmp => IcmpProperties
| .arith_trunci => NswNuwProperties
| .arith_extui => NnegProperties
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
| .riscv_slliw => RISCVImmediateProperties
| .riscv_srliw => RISCVImmediateProperties
| .riscv_sraiw => RISCVImmediateProperties
| .riscv_slliuw => RISCVImmediateProperties
| .riscv_rori => RISCVImmediateProperties
| .riscv_roriw => RISCVImmediateProperties
| .riscv_bclri => RISCVImmediateProperties
| .riscv_bexti => RISCVImmediateProperties
| .riscv_binvi => RISCVImmediateProperties
| .riscv_bseti => RISCVImmediateProperties
| .mod_arith_constant => ModArithConstantProperties
| _ => Unit

instance : HasOpInfo OpCode where
  moduleOpCode := .builtin_module
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
  case arith_shli => exact (NswNuwProperties.fromAttrDict attrDict)
  case arith_shrsi => exact (ExactProperties.fromAttrDict attrDict)
  case arith_shrui => exact (ExactProperties.fromAttrDict attrDict)
  case arith_ori => exact (DisjointProperties.fromAttrDict attrDict)
  case llvm_constant => exact (LLVMConstantProperties.fromAttrDict attrDict)
  case llvm_add => exact (NswNuwProperties.fromAttrDict attrDict)
  case llvm_sub => exact (NswNuwProperties.fromAttrDict attrDict)
  case llvm_mul => exact (NswNuwProperties.fromAttrDict attrDict)
  case llvm_udiv => exact (ExactProperties.fromAttrDict attrDict)
  case llvm_sdiv => exact (ExactProperties.fromAttrDict attrDict)
  case llvm_shl => exact (NswNuwProperties.fromAttrDict attrDict)
  case llvm_lshr => exact (ExactProperties.fromAttrDict attrDict)
  case llvm_ashr => exact (ExactProperties.fromAttrDict attrDict)
  case llvm_or => exact (DisjointProperties.fromAttrDict attrDict)
  case llvm_trunc => exact (NswNuwProperties.fromAttrDict attrDict)
  case llvm_zext => exact (NnegProperties.fromAttrDict attrDict)
  case llvm_icmp => exact (IcmpProperties.fromAttrDict attrDict)
  case arith_trunci => exact (NswNuwProperties.fromAttrDict attrDict)
  case arith_extui => exact (NnegProperties.fromAttrDict attrDict)
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
  case riscv_slliw => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_srliw => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_sraiw => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_slliuw => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_rori => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_roriw => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_bclri => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_bexti => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_binvi => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case riscv_bseti => exact (RISCVImmediateProperties.fromAttrDict attrDict)
  case mod_arith_constant => exact (ModArithConstantProperties.fromAttrDict attrDict)
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
  | .arith_addi | .arith_subi | .arith_muli | .arith_shli | .arith_trunci
  | .llvm_add | .llvm_sub | .llvm_mul | .llvm_shl | .llvm_trunc => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    if props.nsw then
      dict := dict.insert "nsw".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    if props.nuw then
      dict := dict.insert "nuw".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .llvm_icmp => Id.run do
    (Std.HashMap.emptyWithCapacity 2).insert "predicate".toUTF8 (Attribute.integerAttr props.value)
  | .arith_divsi | .arith_divui | .arith_shrsi | .arith_shrui |
    .llvm_udiv | .llvm_sdiv | .llvm_lshr | .llvm_ashr => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    if props.exact then
      dict := dict.insert "exact".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .arith_ori | .llvm_or => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    if props.disjoint then
      dict := dict.insert "disjoint".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .arith_extui | .llvm_zext => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    if props.nneg then
      dict := dict.insert "nneg".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .riscv_li  | .riscv_lui | .riscv_auipc | .riscv_andi | .riscv_ori | .riscv_xori
  | .riscv_addi | .riscv_slti | .riscv_sltiu | .riscv_addiw | .riscv_slli | .riscv_srli | .riscv_srai
  | .riscv_slliw | .riscv_srliw | .riscv_sraiw | .riscv_rori | .riscv_roriw | .riscv_slliuw
  | .riscv_bclri | .riscv_bexti | .riscv_binvi | .riscv_bseti | .mod_arith_constant =>
    (Std.HashMap.emptyWithCapacity 2).insert "value".toUTF8 (Attribute.integerAttr props.value)
  | _ =>
    Std.HashMap.emptyWithCapacity 0

end
end Veir
