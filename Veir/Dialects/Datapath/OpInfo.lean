module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Datapath where
| compress
| partial_product
| pos_partial_product
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Datapath.propertiesOf (_op : Datapath) : Type :=
  Unit

def Datapath.fromAttrDict
    (_op : Datapath) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Datapath.propertiesOf _op) :=
  .ok ()

def Datapath.toAttrDict
    (_op : Datapath) (_props : Datapath.propertiesOf _op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

def Datapath.getEffects
    (_op : Datapath) (_props : Datapath.propertiesOf _op) : MemoryEffects :=
  .none

def Datapath.isConstantLike (_op : Datapath) : Bool :=
  false

def Datapath.hasSSADominance (_op : Datapath) (_index : Nat) : Bool :=
  true

#generate_dialect Datapath

instance : IsOpCode Datapath where
  fromName := Datapath.fromName
  name := Datapath.name
  propertiesOf := Datapath.propertiesOf
  fromAttrDict := Datapath.fromAttrDict
  toAttrDict := Datapath.toAttrDict

/--
Verify the local invariants of a `datapath` operation in any operation-info
type containing the `datapath` dialect.
-/
@[expose]
def Datapath.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Datapath] (opType : Datapath) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .compress => do
    if op.getNumOperands ctx.raw opIn ≤ op.getNumResults ctx.raw opIn then
      throw "Number of inputs must be greater than the number of results"
    if op.getNumResults ctx.raw opIn < 2 then
      throw "Expected at least 2 results"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .partial_product => do
    if op.getNumOperands ctx.raw opIn ≠ 2 then
      throw "Expected 2 operands"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()
  | .pos_partial_product => do
    if op.getNumOperands ctx.raw opIn ≠ 3 then
      throw "Expected 3 operands"
    if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    pure ()

instance : HasOpInfo Datapath where
  verifyLocalInvariants := Datapath.verifyLocalInvariants
  getEffects := Datapath.getEffects
  isConstantLike := Datapath.isConstantLike
  hasSSADominance := Datapath.hasSSADominance

end

end Veir
