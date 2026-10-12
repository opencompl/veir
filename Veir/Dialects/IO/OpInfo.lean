module

public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode
public import Veir.Interpreter.EffectState

namespace Veir

public section

/--
Byte exchange with the environment. Buffers are `(ptr : !llvm.ptr, len : integer)`
and peers are `!io.address` values. `self` yields the program's own address;
result 0 of every other operation is an `i64` status: non-negative is the number of bytes
transferred, which may be below `len`; negative is an `Io.Error` code.
-/
@[opcodes]
inductive Io where
/-- `() -> !io.address`: the address of the running program, fixed by the environment. -/
| self
/-- `(dest : !io.address, ptr : !llvm.ptr, len : integer) -> i64`: send `len` bytes at `ptr` to `dest`. -/
| send
/--
`(ptr : !llvm.ptr, len : integer) -> (i64, !io.address)`: receive the next message
addressed to this program into `ptr`. Result 1 is the sender; it is unspecified
when the status is negative.
-/
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

/-- The next message exceeds the buffer; it stays in flight. -/
def messageTooLong : Int := -3

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
`self` only reads the environment. Every other `io` operation accesses its buffer
and has observable effects, so it is `readWrite`: never dead, and never
reordered with each other or with memory accesses.
-/
@[get_effects]
def Io.getEffects
    (op : Io) (_props : Io.propertiesOf op) : MemoryEffects :=
  match op with
  | .self => .none
  | _ => .readWrite

/-- `self` is fixed by the environment, not by the operation, so it is not a literal. -/
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

/-- Result 0 must be the `i64` status. -/
def Io.verifyStatusResult {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo) (instrName : String) :
    Except String PUnit :=
  ((op.getResult 0).get! ctx.raw).type.verifyI64
    s!"{instrName}: Expected result 0 to have i64 type"

/--
Verify an `io` operation: `self` takes nothing and returns an `!io.address`;
`send` takes `(address, ptr, len)`, `recv` and `rand` take `(ptr, len)`, and
their result 0 is an `i64` status, with `recv` adding an `!io.address`.
-/
@[expose]
def Io.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo] [HasDialect OpInfo Io]
    (opType : Io) (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  op.checkIsNonNullIntegerType ctx opIn
  match opType with
  | .self =>
    op.verifyPlainOpCounts ctx opIn 0 1
    ((op.getResult 0).get! ctx.raw).type.verifyIoAddressType
      s!"{instrName}: Expected result 0 to have !io.address type"
  | .send =>
    op.verifyPlainOpCounts ctx opIn 3 1
    ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyIoAddressType
      s!"{instrName}: Expected operand 0 to have !io.address type"
    Io.verifyBufferOperands op ctx 1 instrName
    Io.verifyStatusResult op ctx instrName
  | .recv =>
    op.verifyPlainOpCounts ctx opIn 2 2
    Io.verifyBufferOperands op ctx 0 instrName
    Io.verifyStatusResult op ctx instrName
    ((op.getResult 1).get! ctx.raw).type.verifyIoAddressType
      s!"{instrName}: Expected result 1 to have !io.address type"
  | .rand =>
    op.verifyPlainOpCounts ctx opIn 2 1
    Io.verifyBufferOperands op ctx 0 instrName
    Io.verifyStatusResult op ctx instrName

def Io.interpretOp' (opType : Veir.Io) (properties : propertiesOf opType)
    (_resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (_blockOperands : Array BlockPtr) (em : EffectState)
    : Interp ((Array RuntimeValue) × EffectState × Option ControlFlowAction) :=
  match opType with
  | .self => do
    return (#[.ioAddr em.network.selfAddress], em, none)
  | .send => do
    let [.ioAddr dest, .addr ptr, .int _ len] := operands.toList | none
    let .val len := len | Interp.ub none
    let .val ptr := ptr | Interp.ub none
    let lenNat := len.toNat
    if lenNat ≥ UInt64.size then Interp.ub none
    let len : UInt64 := UInt64.ofNat lenNat
    if ← em.memory.hasPoison ptr len then Interp.ub none
    let buf ← em.memory.load ptr len
    let ns' := em.network.sendMessage dest buf
    return (#[.int 64 (.val buf.size)], {em with network := ns'}, none)
  | .recv => do
    let [.addr ptr, .int _ len] := operands.toList | none
    let .val len := len | Interp.ub none
    let .val ptr := ptr | Interp.ub none
    let len := len.toNat
    -- `status` is the number of bytes written, or an `Io.Error` code.
    -- `src` is the source address of the message, or 0 if no message was received.
    let (status, src, em') ← match em.network.consumeMessage with
      | none => pure (Io.Error.exhausted, 0, em)
      | some (ns', msg) =>
        if msg.payload.size > len then
          -- Leave the message in flight so a larger buffer can retry.
          pure (Io.Error.messageTooLong, 0, em)
        else do
          let mem' ← em.memory.store ptr msg.payload
          pure ((msg.payload.size : Int), msg.src, {em with network := ns', memory := mem'})
    return (#[.int 64 (.val (BitVec.ofInt 64 status)), .ioAddr src], em', none)
  | .rand => do
    let [.addr addr, .int _ len] := operands.toList | none
    let .val len := len | Interp.ub none
    let .val addr := addr | Interp.ub none
    let lenNat := len.toNat
    if lenNat ≥ UInt64.size then Interp.ub none
    let len : UInt64 := UInt64.ofNat lenNat
    let ⟨es', buf⟩ ← em.entropy.entropyLoad len
    let mem' ← em.memory.store addr buf
    return  (#[.int 64 (.val len.toNat)], {em with entropy := es', memory := mem'}, none)

instance : HasOpInfo Io where
  verifyLocalInvariants := Io.verifyLocalInvariants
  getEffects := Io.getEffects
  isConstantLike := Io.isConstantLike
  hasSSADominance := Io.hasSSADominance

end

end Veir
