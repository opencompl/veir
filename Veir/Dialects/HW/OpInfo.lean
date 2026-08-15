module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.HW.Properties
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive HW where
| constant
| module
| output
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def HW.propertiesOf (op : HW) : Type :=
match op with
| .constant => HWConstantProperties
| .module => HWModuleProperties
| _ => Unit

def HW.fromAttrDict
    (op : HW) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (HW.propertiesOf op) := by
  cases op
  case constant => exact HWConstantProperties.fromAttrDict attrDict
  case module => exact HWModuleProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def HW.toAttrDict
    (op : HW) (props : HW.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .constant =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "value".toUTF8 (Attribute.integerAttr props.value)
  | .module => Id.run do
    let dict := Std.HashMap.emptyWithCapacity 4
    let dict := dict.insert "module_type".toUTF8 (.hwModuleType props.module_type)
    let dict := dict.insert "sym_name".toUTF8 (.stringAttr props.sym_name)
    let dict := dict.insert "per_port_attrs".toUTF8 (.arrayAttr props.per_port_attrs)
    let dict := dict.insert "parameters".toUTF8 (.arrayAttr props.parameters)
    dict
  | _ => Std.HashMap.emptyWithCapacity 0

def HW.hasSideEffects (op : HW) (_props : HW.propertiesOf op) : Bool :=
  match op with
  | .constant => false
  | _ => true

def HW.getEffects
    (_op : HW) (_props : HW.propertiesOf _op) : MemoryEffects :=
  .none

def HW.isConstantLike (op : HW) : Bool :=
  match op with
  | .constant => true
  | _ => false

def HW.hasSSADominance (_op : HW) (_index : Nat) : Bool :=
  true

def HW.isTerminator (op : HW) : Bool :=
  match op with
  | .output => true
  | _ => false

#generate_dialect HW

instance : HasOpInfo HW where
  fromName := HW.fromName
  name := HW.name
  propertiesOf := HW.propertiesOf
  fromAttrDict := HW.fromAttrDict
  toAttrDict := HW.toAttrDict
  hasSideEffects := HW.hasSideEffects
  getEffects := HW.getEffects
  isConstantLike := HW.isConstantLike
  hasSSADominance := HW.hasSSADominance
  isTerminator := HW.isTerminator

/--
Verify the local invariants of an `hw` operation in any operation-info type
containing the `hw` dialect.
-/
def HW.verifyLocalInvariants {OpInfo : Type} [HasOpInfo OpInfo]
    [HasDialect OpInfo HW] (opType : HW) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .constant => do
    op.verifyPlainOpCounts ctx opIn 0 1
    pure ()
  | .module => do
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 1 then
      throw "Expected 1 region"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .output => do
    op.verifyTerminatorCounts ctx opIn 0
    pure ()

end

end Veir
