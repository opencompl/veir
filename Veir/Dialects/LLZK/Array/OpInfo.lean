module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.Array.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

namespace LLZK

@[opcodes]
inductive Array where
| new
| read
| write
| extract
| insert
| len
deriving Inhabited, Repr, Hashable, DecidableEq

end LLZK

@[expose, properties_of]
def LLZK.Array.propertiesOf (op : LLZK.Array) : Type :=
match op with
| .new => ArrayNewProperties
| _ => Unit

def LLZK.Array.fromAttrDict
    (op : LLZK.Array) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (LLZK.Array.propertiesOf op) :=
  match op with
  | .new => ArrayNewProperties.fromAttrDict attrDict
  | .read => .ok ()
  | .write => .ok ()
  | .extract => .ok ()
  | .insert => .ok ()
  | .len => .ok ()

def LLZK.Array.toAttrDict
    (op : LLZK.Array) (props : LLZK.Array.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op, props with
  | .new, props => props.toAttrDict
  | _, _ => Std.HashMap.emptyWithCapacity 0

def LLZK.Array.getEffects
    (op : LLZK.Array) (_props : LLZK.Array.propertiesOf op) : MemoryEffects :=
  match op with
  | .new => .allocate
  | .read | .extract => .read
  | .write | .insert => .write
  | .len => .none

def LLZK.Array.isConstantLike (_op : LLZK.Array) : Bool :=
  false

def LLZK.Array.hasSSADominance (_op : LLZK.Array) (_index : Nat) : Bool :=
  true

#generate_dialect LLZK.Array

instance : IsOpCode LLZK.Array where
  fromName := LLZK.Array.fromName
  name := LLZK.Array.name
  propertiesOf := LLZK.Array.propertiesOf
  fromAttrDict := LLZK.Array.fromAttrDict
  toAttrDict := LLZK.Array.toAttrDict

@[expose]
def LLZK.Array.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo LLZK.Array] (opType : LLZK.Array) (op : OperationPtr)
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
  | .new => do
    requireResults 1
    if !(op.getResultTypes! ctx.raw)[0]!.val.isLLZKArrayType then
      throw s!"{instrName}: Expected valid LLZK array.type return type"
    -- TODO: check operands types/count
  | .read => do
    requireAtLeastOperands 1
    requireResults 1
    for (operType,idx) in (op.getOperandTypes! ctx.raw).zipIdx do
      if idx = 0 && !operType.val.isLLZKArrayType then
        throw s!"{instrName}: Expected operand 0 to have a valid LLZK array type"
      else if !(operType.val matches .indexType _) then
        throw s!"{instrName}: Expected operand {idx} to have an index type"
    if !(op.getResultTypes! ctx.raw)[0]!.val.isLLZKArrayElemType then
      throw s!"{instrName}: Expected return to have a valid LLZK array element type"
  | .extract => do
    requireAtLeastOperands 1
    requireResults 1
    for (operType,idx) in (op.getOperandTypes! ctx.raw).zipIdx do
      if idx = 0 && !operType.val.isLLZKArrayType then
        throw s!"{instrName}: Expected operand 0 to have a valid LLZK array type"
      else if !(operType.val matches .indexType _) then
        throw s!"{instrName}: Expected operand {idx} to have an index type"
    if !(op.getResultTypes! ctx.raw)[0]!.val.isLLZKArrayType then
      throw s!"{instrName}: Expected return to have a valid LLZK array type"
  | .write => do
    requireAtLeastOperands 2
    requireResults 0
    for (operType,idx) in (op.getOperandTypes! ctx.raw).zipIdx do
      if idx = 0 && !operType.val.isLLZKArrayType then
        throw s!"{instrName}: Expected operand 0 to be a valid LLZK array"
      else if idx ≠ (op.getNumOperands! ctx.raw)-1 && !(operType.val matches .indexType _) then
        throw s!"{instrName}: Expected operand {idx} to have an index type"
      else if !operType.val.isLLZKArrayElemType then
        throw s!"{instrName}: Expected operand {idx} to have a valid LLZK array element type"
  | .insert => do
    requireAtLeastOperands 2
    requireResults 0
    for (operType,idx) in (op.getOperandTypes! ctx.raw).zipIdx do
      if idx = 0 && !operType.val.isLLZKArrayType then
        throw s!"{instrName}: Expected operand 0 to be a valid LLZK array"
      else if idx ≠ (op.getNumOperands! ctx.raw)-1 && !(operType.val matches .indexType _) then
        throw s!"{instrName}: Expected operand {idx} to have an index type"
      else if !operType.val.isLLZKArrayType then
        throw s!"{instrName}: Expected operand {idx} to have a valid LLZK array type"
  | .len => do
    requireResults 1
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw s!"{instrName}: Expected 2 operands (the array and the dimension)"
    if !(op.getOperandTypes! ctx.raw)[0]!.val.isLLZKArrayType then
      throw s!"{instrName}: Expected operand 0 to be a valid LLZK array"
    if !((op.getOperandTypes! ctx.raw)[1]!.val matches .indexType _) then
      throw s!"{instrName}: Expected operand 1 to have an index type"
    if !((op.getResultTypes! ctx.raw)[0]!.val matches .indexType _) then
      throw s!"{instrName}: Expected return to have index type"

    requireResults 1

instance : HasOpInfo LLZK.Array where
  verifyLocalInvariants := LLZK.Array.verifyLocalInvariants
  getEffects := LLZK.Array.getEffects
  isConstantLike := LLZK.Array.isConstantLike
  hasSSADominance := LLZK.Array.hasSSADominance

end

end Veir
