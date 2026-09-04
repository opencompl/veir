module

public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

/--
Byte exchange with the environment. Buffers are `(ptr : !llvm.ptr, len : integer)`
and peers are `!io.address` values. Every operation returns an `i64` status:
non-negative is the number of bytes transferred, which may be below `len`;
negative is an `Io.Error` code.
-/
@[opcodes]
inductive Io where
/-- `(dest : !io.address, ptr : !llvm.ptr, len : integer) -> i64`: send `len` bytes at `ptr` to `dest`. -/
| send
/-- `(src : !io.address, ptr : !llvm.ptr, len : integer) -> i64`: receive up to `len` bytes from `src` into `ptr`. -/
| recv
/-- `(ptr : !llvm.ptr, len : integer) -> i64`: fill up to `len` bytes at `ptr` with random bytes. -/
| rand
deriving Inhabited, Repr, Hashable, DecidableEq

/-! Error codes, returned as negative `i64` statuses. -/
namespace Io.Error

/-- Peer unreachable or channel closed. -/
def closed : Int := -1

/-- No input or entropy left. -/
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
All `io` operations access their buffer and have observable effects, so they
are `readWrite`: never dead, and never reordered with each other or with memory
accesses.
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

/-- Check that `ty` is `!io.address`. -/
def TypeAttr.verifyIoAddressType
    (ty : TypeAttr) (errMsg : String) : Except String PUnit :=
  match ty.val with
  | .ioAddressType _ => pure ()
  | _ => throw errMsg

/-- Operands `base` and `base + 1` must be a `!llvm.ptr` and an integer byte count, respectively. -/
def Io.verifyBufferOperands {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo) (base : Nat) (instrName : String) :
    Except String PUnit := do
  ((op.getOperand! ctx.raw base).getType! ctx.raw).verifyLlvmPointerType
    s!"{instrName}: Expected operand {base} to have !llvm.ptr type"
  ((op.getOperand! ctx.raw (base + 1)).getType! ctx.raw).verifyIntegerType
    s!"{instrName}: Expected operand {base + 1} to have integer type"

/--
Verify an `io` operation: `send` and `recv` take `(address, ptr, len)`, `rand`
takes `(ptr, len)`; all return one `i64`.
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
