module

public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

/--
Operations that exchange bytes with the environment. Every operation takes a
buffer pointer and a byte count, `(ptr : !llvm.ptr, len : integer)`, and has
no results, mirroring the shape of the system calls they lower to.
-/
@[opcodes]
inductive Io where
/--
`io.send` writes the `len` bytes starting at `ptr` to the environment. It reads
the buffer, and its output is observable, so it is modelled as both reading and
writing memory to keep it from being removed or reordered.
-/
| send
/--
`io.recv` reads `len` bytes from the environment and stores them starting at
`ptr`. It consumes input and writes the buffer, so it is modelled as both
reading and writing memory to keep it from being removed or reordered.
-/
| recv
/--
`io.rand` fills the `len` bytes starting at `ptr` with random bytes. Two `rand`
operations must not be reordered, since that changes the observable trace, so
it is modelled as both reading and writing memory.
-/
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

/--
Every `io` operation accesses the buffer it is given and interacts with the
environment, so none of them may be removed when unused or reordered with
respect to each other or to loads and stores.
-/
@[get_effects]
def Io.getEffects
    (_op : Io) (_props : Io.propertiesOf _op) : MemoryEffects :=
  .readWrite

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
Verify the local invariants of an `io` operation in any operation-info type
containing the `io` dialect: two operands, a `!llvm.ptr` buffer followed by an
integer byte count, and no results.
-/
@[expose]
def Io.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo] [HasDialect OpInfo Io]
    (opType : Io) (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  match opType with
  | .send | .recv | .rand =>
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyPlainOpCounts ctx opIn 2 0
    ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyLlvmPointerType
      s!"{instrName}: Expected operand 0 to have !llvm.ptr type"
    ((op.getOperand! ctx.raw 1).getType! ctx.raw).verifyIntegerType
      s!"{instrName}: Expected operand 1 to have integer type"

instance : HasOpInfo Io where
  verifyLocalInvariants := Io.verifyLocalInvariants
  getEffects := Io.getEffects
  isConstantLike := Io.isConstantLike
  hasSSADominance := Io.hasSSADominance

end

end Veir
