module

public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

/--
Operations that exchange bytes with the environment. Buffers are passed as a
pointer and a byte count, `(ptr : !llvm.ptr, len : integer)`, and peers are
named by an opaque `!io.address` value, mirroring the shape of the system
calls the operations lower to.

Every operation returns an `i64` status, following the system call convention.
A non-negative status is the number of bytes transferred, which may be smaller
than `len`. A negative status is one of the error codes in `Io.Error`.
-/
@[opcodes]
inductive Io where
/--
`io.send` writes the `len` bytes starting at `ptr` to the peer `dest`. Its
operands are `(dest : !io.address, ptr : !llvm.ptr, len : integer)` and its
result is the `i64` status. It reads the buffer, and its output is observable,
so it is modelled as both reading and writing memory to keep it from being
removed or reordered.
-/
| send
/--
`io.recv` reads up to `len` bytes from the peer `src` and stores them starting
at `ptr`. Its operands are `(src : !io.address, ptr : !llvm.ptr, len : integer)`
and its result is the `i64` status. It consumes input and writes the buffer,
so it is modelled as both reading and writing memory to keep it from being
removed or reordered.
-/
| recv
/--
`io.rand` fills up to `len` bytes starting at `ptr` with random bytes. Its
operands are `(ptr : !llvm.ptr, len : integer)` and its result is the `i64`
status. Two `rand` operations must not be reordered, since that changes the
observable trace, so it is modelled as both reading and writing memory.
-/
| rand
deriving Inhabited, Repr, Hashable, DecidableEq

/-!
Error codes returned as negative `i64` statuses by `io` operations. A
non-negative status is a byte count, never an error.
-/
namespace Io.Error

/-- The peer is unreachable or has closed the channel. -/
def closed : Int := -1

/-- The environment has no more input or entropy to supply. -/
def exhausted : Int := -2

end Io.Error

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
environment, so none of them may be removed when its status is unused or
reordered with respect to each other or to loads and stores.
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

/-- Check that a type is the `!io.address` type. -/
def TypeAttr.verifyIoAddressType
    (ty : TypeAttr) (errMsg : String) : Except String PUnit :=
  match ty.val with
  | .ioAddressType _ => pure ()
  | _ => throw errMsg

/--
Check that operands `base` and `base + 1` of `op` are a `!llvm.ptr` buffer
followed by an integer byte count.
-/
def Io.verifyBufferOperands {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo) (base : Nat) (instrName : String) :
    Except String PUnit := do
  ((op.getOperand! ctx.raw base).getType! ctx.raw).verifyLlvmPointerType
    s!"{instrName}: Expected operand {base} to have !llvm.ptr type"
  ((op.getOperand! ctx.raw (base + 1)).getType! ctx.raw).verifyIntegerType
    s!"{instrName}: Expected operand {base + 1} to have integer type"

/--
Verify the local invariants of an `io` operation in any operation-info type
containing the `io` dialect. `send` and `recv` take a peer address, a
`!llvm.ptr` buffer, and an integer byte count; `rand` takes only the buffer
and the count. Each returns a single `i64` status.
-/
@[expose]
def Io.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo] [HasDialect OpInfo Io]
    (opType : Io) (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  op.checkIsNonNullIntegerType ctx opIn
  match opType with
  | .send | .recv =>
    op.verifyPlainOpCounts ctx opIn 3 1
    ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyIoAddressType
      s!"{instrName}: Expected operand 0 to have !io.address type"
    Io.verifyBufferOperands op ctx 1 instrName
  | .rand =>
    op.verifyPlainOpCounts ctx opIn 2 1
    Io.verifyBufferOperands op ctx 0 instrName
  ((op.getResult 0).get! ctx.raw).type.verifyI64
    s!"{instrName}: Expected result 0 to have i64 type"

instance : HasOpInfo Io where
  verifyLocalInvariants := Io.verifyLocalInvariants
  getEffects := Io.getEffects
  isConstantLike := Io.isConstantLike
  hasSSADominance := Io.hasSSADominance

end

end Veir
