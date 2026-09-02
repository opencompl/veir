module

public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Io where
| send
| recv
| rand
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Io.propertiesOf (op : Io) : Type :=
match op with
| _ => Unit

def Io.fromAttrDict (op : Io) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Io.propertiesOf op) := by
  cases op
  all_goals exact .ok ()

def Io.toAttrDict
    (op : Io) (props : Io.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | _ => Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Io.getEffects
    (op : Io) (props : Io.propertiesOf op) : MemoryEffects :=
  match op with
  | .send => .write
  | .recv => .readWrite -- recv is treated as read & write as it consumes input, thus, modifying the environment
  | .rand => .readWrite -- rand is treated as read & write to avoid optimizations that reorder two rand operations as that results in different observable traces

def Io.isConstantLike (_op : Io) : Bool :=
  false

def Io.hasSSADominance (_op : Io) (_index : Nat) : Bool :=
  true

#generate_dialect Io

instance : IsOpCode Io where
  fromName := Io.fromName
  name := Io.name
  propertiesOf := Io.propertiesOf
  fromAttrDict := Io.fromAttrDict
  toAttrDict := Io.toAttrDict

/--
Verify the local invariants of an `Io` operation in any operation-info type
containing the `Io` dialect.
-/
@[expose]
def Io.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo] [HasDialect OpInfo Io]
    (opType : Io) (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  match opType with
  | .send =>
    op.verifyPlainOpCounts ctx opIn 1 0
    ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyI8ArrayType
      s!"{instrName}: Expected operand 0 to have i8 array type"
  | .recv | .rand =>
    op.verifyPlainOpCounts ctx opIn 0 1
    ((op.getResult 0).get! ctx.raw).type.verifyI8ArrayType
      s!"{instrName}: Expected result 0 to have i8 array type"

instance : HasOpInfo Io where
  verifyLocalInvariants := Io.verifyLocalInvariants
  getEffects := Io.getEffects
  isConstantLike := Io.isConstantLike
  hasSSADominance := Io.hasSSADominance

end

end Veir
