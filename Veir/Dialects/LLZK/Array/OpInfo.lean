module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.Array.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Array_ where
| new
| read
| write
| extract
| insert
| len
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Array_.propertiesOf (op : Array_) : Type :=
match op with
| .new => ArrayNewProperties
| _ => Unit

def Array_.fromAttrDict
    (op : Array_) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Array_.propertiesOf op) := by
  cases op
  case new => exact ArrayNewProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Array_.toAttrDict
    (op : Array_) (props : Array_.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op, props with
  | .new, props => props.toAttrDict
  | _, _ => Std.HashMap.emptyWithCapacity 0

def Array_.getEffects
    (op : Array_) (_props : Array_.propertiesOf op) : MemoryEffects :=
  match op with
  | .new => .allocate
  | .read | .extract => .read
  | .write | .insert => .write
  | .len => .none

def Array_.isConstantLike (_op : Array_) : Bool :=
  false

def Array_.hasSSADominance (_op : Array_) (_index : Nat) : Bool :=
  true

#generate_dialect Array_

instance : IsOpCode Array_ where
  fromName := Array_.fromName
  name := Array_.name
  propertiesOf := Array_.propertiesOf
  fromAttrDict := Array_.fromAttrDict
  toAttrDict := Array_.toAttrDict

@[expose]
def Array_.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Array_] (opType : Array_) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let requireAtLeastOperands (n : Nat) : Except String PUnit :=
    if op.getNumOperands ctx.raw opIn < n then
      throw s!"{instrName}: Expected at least {n} operand(s)"
    else
      pure ()
  let requireResults (n : Nat) : Except String PUnit :=
    if op.getNumResults ctx.raw opIn ≠ n then
      throw s!"{instrName}: Expected {n} result(s)"
    else
      pure ()
  if op.getNumRegions ctx.raw opIn ≠ 0 then
    throw s!"{instrName}: Expected 0 regions"
  if op.getNumSuccessors ctx.raw opIn ≠ 0 then
    throw s!"{instrName}: Expected 0 successors"
  match opType with
  | .new => requireResults 1
  | .read | .extract => do requireAtLeastOperands 1; requireResults 1
  | .write | .insert => do requireAtLeastOperands 2; requireResults 0
  | .len => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw s!"{instrName}: Expected 2 operands (the array and the dimension)"
    requireResults 1

instance : HasOpInfo Array_ where
  verifyLocalInvariants := Array_.verifyLocalInvariants
  getEffects := Array_.getEffects
  isConstantLike := Array_.isConstantLike
  hasSSADominance := Array_.hasSSADominance

end

end Veir
