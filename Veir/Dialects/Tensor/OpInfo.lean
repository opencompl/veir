module

public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Tensor where
| empty
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Tensor.propertiesOf (_op : Tensor) : Type :=
  Unit

def Tensor.fromAttrDict
    (op : Tensor) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Tensor.propertiesOf op) := by
  cases op
  all_goals exact .ok ()

def Tensor.toAttrDict
    (op : Tensor) (_props : Tensor.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

/-- All `tensor` operations are pure, as in MLIR. -/
@[get_effects]
def Tensor.getEffects
    (_op : Tensor) (_props : Tensor.propertiesOf _op) : MemoryEffects :=
  .none

def Tensor.isConstantLike (_op : Tensor) : Bool :=
  false

def Tensor.hasSSADominance (_op : Tensor) (_index : Nat) : Bool :=
  true

@[is_terminator]
def Tensor.isTerminator (_op : Tensor) : Bool :=
  false

#generate_dialect Tensor

instance : IsOpCode Tensor where
  fromName := Tensor.fromName
  name := Tensor.name
  propertiesOf := Tensor.propertiesOf
  fromAttrDict := Tensor.fromAttrDict
  toAttrDict := Tensor.toAttrDict

/-- Verify the local invariants of a `tensor` operation. -/
def Tensor.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Tensor] (opType : Tensor) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (Tensor.name opType)
  let resultType (i : Nat) := (op.getResult i).getType! ctx.raw
  match opType with
  | .empty => do
    -- Tensor types are always statically shaped, so there are no dynamic size operands.
    op.verifyPlainOpCounts ctx opIn 0 1
    let _ ← (resultType 0).verifyTensorType s!"{instrName}: Expected result to be a tensor"

instance : HasOpInfo Tensor where
  verifyLocalInvariants := Tensor.verifyLocalInvariants
  getEffects := Tensor.getEffects
  isConstantLike := Tensor.isConstantLike
  hasSSADominance := Tensor.hasSSADominance
  isTerminator := Tensor.isTerminator

end
