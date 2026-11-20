module

public import Veir.Interpreter.RuntimeValue
public import Veir.Interpreter.CTree

public section

open CTree
/-!
  # CTree-based IO Interpreter

  This file contains relevant effects and
  a simple CTree interpreter for the IO dialect.
-/

namespace Veir

/-- Input type for an IO effect -/
inductive IoEIn where
  | selfAddrE
  | sendE (msg : Message)
  | recvE
  | randE (len : Nat)

/-- Output type for an IO effect -/
abbrev IoE (e : IoEIn) :=
  match e with
  | .selfAddrE => Nat
  | .sendE _ => Unit
  | .recvE => Option Message
  | .randE _ => ByteArray

/-- Emit an IO send effect -/
def ioSend [IoE -< E] (msg : Message) : CTree E C Unit := CTree.trigger (SubE := IoE) (.sendE msg)
/-- Emit an IO receive effect -/
def ioRecv [IoE -< E] : CTree E C (Option Message) := CTree.trigger (SubE := IoE) (.recvE)
/-- Emit an IO random number generation effect -/
def ioRand [IoE -< E] (len : Nat) : CTree E C ByteArray := CTree.trigger (SubE := IoE) (.randE len)
/-- Emit an effect representing getting this process's network address -/
def ioSelfAddress [IoE -< E] : CTree E C Nat := CTree.trigger (SubE := IoE) (.selfAddrE)

def Io.interpretOpCTree [ErrorE -< E] [UBE -< E] [IoE -< E] (opType : Veir.Io)
    (properties : propertiesOf opType)
    (_resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (_blockOperands : Array BlockPtr) (mem : MemoryState)
    : CTree E C ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .self => do
    let selfAddress ← ioSelfAddress
    return (#[.ioAddr selfAddress], mem, none)
  | .send => do
    let [.ioAddr dest, .addr ptr, .int _ len] := operands.toList | ub
    let .val len := len | ub
    let .val ptr := ptr | ub
    let lenNat := len.toNat
    if lenNat ≥ UInt64.size then ub
    let len : UInt64 := UInt64.ofNat lenNat
    if ← monadLift $ mem.hasPoison ptr len then ub
    let buf ← monadLift $ mem.load ptr len
    let selfAddress ← ioSelfAddress
    ioSend { src := selfAddress, dest, payload := buf }
    return (#[.int 64 (.val buf.size)], mem, none)
  | .recv => do
    let [.addr ptr, .int _ len] := operands.toList | ub
    let .val len := len | ub
    let .val ptr := ptr | ub
    let len := len.toNat
    let optResult ← ioRecv
    let (status, src, mem') ← match optResult with
    | none => pure (Io.Error.exhausted, 0, mem)
    | some { src := src, dest := _, payload := payload } =>
      if payload.size > len then
        pure (Io.Error.messageTooLong, 0, mem)
      else do
        let mem' ← monadLift $ mem.store ptr payload
        pure (payload.size, src, mem')
    return (#[.int 64 (.val (BitVec.ofInt 64 status)), .ioAddr src], mem', none)
  | .rand => do
    let [.addr addr, .int _ len] := operands.toList | ub
    let .val len := len | ub
    let .val addr := addr | ub
    let lenNat := len.toNat
    if lenNat ≥ UInt64.size then ub
    let buf ← ioRand lenNat
    let mem' ← monadLift $ mem.store addr buf
    return  (#[.int 64 (.val len.toNat)], mem', none)
