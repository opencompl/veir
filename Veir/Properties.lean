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
  A type family that maps an operation code to the type of its properties.
  For operations that do not have any properties, the type is `Unit`.
-/
@[expose]
def propertiesOf (opCode : OpCode) : Type :=
match opCode with
| .arith_constant => ArithConstantProperties
| .llvm_constant => LLVMConstantProperties
| .arith_addi => NswNuwProperties
| .arith_muli => NswNuwProperties
| .llvm_add => NswNuwProperties
| .llvm_mul => NswNuwProperties
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
  case arith_muli => exact (NswNuwProperties.fromAttrDict attrDict)
  case llvm_constant => exact (LLVMConstantProperties.fromAttrDict attrDict)
  case llvm_add => exact (NswNuwProperties.fromAttrDict attrDict)
  case llvm_mul => exact (NswNuwProperties.fromAttrDict attrDict)
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
  | .arith_addi | .arith_muli | .llvm_add | .llvm_mul => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    if props.nsw then
      dict := dict.insert "nsw".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    if props.nuw then
      dict := dict.insert "nuw".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | _ =>
    Std.HashMap.emptyWithCapacity 0

end
end Veir
