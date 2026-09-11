module

public import Veir.IR.OpInfo
public import Veir.Dialects.Seq.Properties
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Seq where
| to_clock
| firreg
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Seq.propertiesOf (op : Seq) : Type :=
match op with
| .to_clock => Unit
| .firreg => SeqFirRegProperties

def Seq.fromAttrDict
    (op : Seq) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Seq.propertiesOf op) := by
  cases op
  case to_clock => exact .ok ()
  case firreg => exact SeqFirRegProperties.fromAttrDict attrDict

def Seq.toAttrDict
    (op : Seq) (props : Seq.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .to_clock => Std.HashMap.emptyWithCapacity 0
  | .firreg => Id.run do
    let dict : Std.HashMap ByteArray Attribute := Std.HashMap.emptyWithCapacity 3
    let dict := dict.insert "name".toUTF8 (.stringAttr props.name)
    let dict :=
      if props.isAsync then dict.insert "isAsync".toUTF8 (.unitAttr .mk) else dict
    let dict :=
      match props.preset with
      | some preset => dict.insert "preset".toUTF8 (.integerAttr preset)
      | none => dict
    dict

def Seq.propagatesPoison (op : Seq) : Bool :=
  match op with
  | .to_clock | .firreg => true

@[is_terminator]
def Seq.isTerminator (_op : Seq) : Bool :=
  false

@[get_effects]
def Seq.getEffects
    (op : Seq) (_props : Seq.propertiesOf op) : MemoryEffects :=
  match op with
  | .to_clock | .firreg => .none

def Seq.isConstantLike (_op : Seq) : Bool :=
  false

def Seq.hasSSADominance (_op : Seq) (_index : Nat) : Bool :=
  true

def Seq.isIsolatedFromAbove (_op : Seq) : Bool :=
  false

#generate_dialect Seq

instance : IsOpCode Seq where
  fromName := Seq.fromName
  name := Seq.name
  propertiesOf := Seq.propertiesOf
  fromAttrDict := Seq.fromAttrDict
  toAttrDict := Seq.toAttrDict

/--
Verify the local invariants of a `seq` operation in any operation-info type
containing the `seq` dialect.
-/
def Seq.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Seq] (opType : Seq) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .to_clock => do
    op.verifyPlainOpCounts ctx opIn 1 1
  | .firreg => do
    let numOps := op.getNumOperands ctx.raw opIn
    if ¬(numOps >= 2 ∧ numOps ≤ 4) then
      throw "Expected 2, 3 or 4 operands"
    if op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"

instance : HasOpInfo Seq where
  verifyLocalInvariants := Seq.verifyLocalInvariants
  getEffects := Seq.getEffects
  isConstantLike := Seq.isConstantLike
  hasSSADominance := Seq.hasSSADominance
  isTerminator := Seq.isTerminator
  isIsolatedFromAbove := Seq.isIsolatedFromAbove

end
