module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.Verif.Properties
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Verif where
| assume
| assert
| clocked_assume
| clocked_assert
| symbolic_value
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, implicit_reducible, properties_of]
def Verif.propertiesOf (op : Verif) : Type :=
  match op with
  | .assume => VerifAssumeAssertProperties
  | .assert => VerifAssumeAssertProperties
  | .clocked_assume => VerifClockedAssumeAssertProperties
  | .clocked_assert => VerifClockedAssumeAssertProperties
  | .symbolic_value => VerifSymbolicValueProperties

def Verif.fromAttrDict
    (op : Verif) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Verif.propertiesOf op) := by
  cases op
  case assume => exact VerifAssumeAssertProperties.fromAttrDict attrDict
  case assert => exact VerifAssumeAssertProperties.fromAttrDict attrDict
  case clocked_assume => exact VerifClockedAssumeAssertProperties.fromAttrDict attrDict
  case clocked_assert => exact VerifClockedAssumeAssertProperties.fromAttrDict attrDict
  case symbolic_value => exact VerifSymbolicValueProperties.fromAttrDict attrDict

def Verif.toAttrDict
    (op : Verif) (props : Verif.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .assume | .assert => Id.run do
    match props.label with
    | some label => (Std.HashMap.emptyWithCapacity 1).insert "label".toUTF8 (.stringAttr label)
    | none => Std.HashMap.emptyWithCapacity 0
  | .clocked_assume | .clocked_assert => Id.run do
    let dict := (Std.HashMap.emptyWithCapacity 2).insert "edge".toUTF8 (.integerAttr props.edge)
    match props.label with
    | some label => dict.insert "label".toUTF8 (.stringAttr label)
    | none => dict
  | .symbolic_value =>
    match props.name with
    | some name => (Std.HashMap.emptyWithCapacity 1).insert "name".toUTF8 (.stringAttr name)
    | none => Std.HashMap.emptyWithCapacity 0

/--
Prevent DCE from removing asserts and assumes, and CSE from merging symbolic_values.
-/
@[get_effects]
def Verif.getEffects
    (op : Verif) (_props : Verif.propertiesOf op) : MemoryEffects :=
  match op with
  | .assume | .assert | .clocked_assume | .clocked_assert => .write
  | .symbolic_value => .allocate

def Verif.isConstantLike (_op : Verif) : Bool :=
  false

def Verif.isIsolatedFromAbove (_op : Verif) : Bool :=
  false

def Verif.hasSSADominance (_op : Verif) (_index : Nat) : Bool :=
  true

@[is_terminator]
def Verif.isTerminator (_op : Verif) : Bool :=
  false

#generate_dialect Verif

instance : IsOpCode Verif where
  fromName := Verif.fromName
  name := Verif.name
  propertiesOf := Verif.propertiesOf
  fromAttrDict := Verif.fromAttrDict
  toAttrDict := Verif.toAttrDict

def Verif.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Verif] (opType : Verif) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .assume | .assert => do
    let numOps := op.getNumOperands ctx.raw opIn
    if ¬(numOps ≥ 1 ∧ numOps ≤ 2) then
      throw "Expected 1 or 2 operands"
    if op.getNumResults ctx.raw opIn ≠ 0 then
      throw "Expected 0 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .clocked_assume | .clocked_assert => do
    let opName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
    let numOps := op.getNumOperands ctx.raw opIn
    if ¬(numOps ≥ 2 ∧ numOps ≤ 3) then
      throw "Expected 2 or 3 operands"
    op.verifyNonOperandCounts ctx opIn 0 0 0
    let props := match opType with
      | .clocked_assume => op.getProperties! ctx.raw Verif.clocked_assume
      | _ => op.getProperties! ctx.raw Verif.clocked_assert
    let edge := props.edge.value
    if edge < 0 ∨ edge > 2 then
      throw s!"{opName}: 'edge' is 0 posedge, 1 negedge or 2 edge, but got {edge}"
    pure ()
  | .symbolic_value => do
    op.verifyPlainOpCounts ctx opIn 0 1
    pure ()

instance : HasOpInfo Verif where
  verifyLocalInvariants := Verif.verifyLocalInvariants
  getEffects := Verif.getEffects
  isConstantLike := Verif.isConstantLike
  hasSSADominance := Verif.hasSSADominance
  isTerminator := Verif.isTerminator
  isIsolatedFromAbove := Verif.isIsolatedFromAbove

end

end Veir
