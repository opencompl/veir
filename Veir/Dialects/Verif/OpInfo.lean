module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Verif where
| assume
| assert
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Verif.propertiesOf (_op : Verif) : Type :=
  Unit

def Verif.fromAttrDict
    (op : Verif) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Verif.propertiesOf op) := by
  cases op
  all_goals exact .ok ()

def Verif.toAttrDict
    (op : Verif) (_props : Verif.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Verif.getEffects
    (_op : Verif) (_props : Verif.propertiesOf _op) : MemoryEffects :=
  .none

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

instance : HasOpInfo Verif where
  verifyLocalInvariants := Verif.verifyLocalInvariants
  getEffects := Verif.getEffects
  isConstantLike := Verif.isConstantLike
  hasSSADominance := Verif.hasSSADominance
  isTerminator := Verif.isTerminator
  isIsolatedFromAbove := Verif.isIsolatedFromAbove

end

end Veir
