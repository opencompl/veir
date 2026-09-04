module

public import Veir.RuntimeValue
public import Veir.Interpreter.Memory
public import Veir.Interpreter.Util
public import Veir.Interpreter.CTree

public section

open CTree
open Veir.Data
/-!
  # CTree-based IO Interpreter

  This file contains relevant effects and
  a simple CTree interpreter for the IO dialect.
-/

namespace Veir

/-- Input type for an IO effect -/
inductive IoEIn where
  | sendE (msg : Message)
  | recvE
  | randE (len : Nat)

/-- Output type for an IO effect -/
abbrev IoE (e : IoEIn) :=
  match e with
  | .sendE _ => Unit
  | .recvE => Option Message
  | .randE _ => ByteArray

/-- Emit an IO send effect -/
def ioSend [IoE -< E] (msg : Message) : CTree E C Unit := CTree.trigger (SubE := IoE) (.sendE msg)
/-- Emit an IO receive effect -/
def ioRecv [IoE -< E] : CTree E C (Option Message) := CTree.trigger (SubE := IoE) (.recvE)
/-- Emit an IO random number generation effect -/
def ioRand [IoE -< E] (len : Nat) : CTree E C ByteArray := CTree.trigger (SubE := IoE) (.randE len)

def Io.interpretOpCTree [UBE -< E] [IoE -< E] (opType : Veir.Io) (properties : propertiesOf opType)
    (_resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (_blockOperands : Array BlockPtr) (mem : MemoryState)
    : CTree E C ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .self => do
    return (#[.ioAddr mem.selfAddress], mem, none)
  | .send => do
    let [.ioAddr dest, .addr ptr, .int _ len] := operands.toList | ub
    let .val len := len | ub
    let lenNat := len.toNat
    if lenNat ≥ UInt64.size then ub
    let len : UInt64 := UInt64.ofNat lenNat
    if ← mem.hasPoisonCTree ptr len then ub
    let buf ← mem.loadCTree ptr len
    -- note that we update the CTree but not the MemoryState's NetworkState
    ioSend { src := mem.selfAddress, dest, payload := buf }
    return (#[.int 64 (.val buf.size)], mem, none)
  | .recv => do
    let [.addr ptr, .int _ len] := operands.toList | ub
    let .val len := len | ub
    let len := len.toNat
    -- note that we use the CTree to receive a message without using MemoryState's NetworkState
    let optResult ← ioRecv
    let (status, src, mem) ← match optResult with
    | none => pure (Io.Error.exhausted, 0, mem)
    | some { src := src, dest := _, payload := payload } =>
      if payload.size > len then
        pure (Io.Error.messageTooLong, 0, mem)
      else do
        let mem ← mem.storeCTree ptr payload
        pure (payload.size, src, mem)
    return (#[.int 64 (.val (BitVec.ofInt 64 status)), .ioAddr src], mem, none)
  | .rand => do
    let [.addr addr, .int _ len] := operands.toList | ub
    let .val len := len | ub
    let lenNat := len.toNat
    if lenNat ≥ UInt64.size then ub
    -- note that we use the CTree to obtain a buffer with random data without using MemoryState's EntropyState
    let buf ← ioRand lenNat
    let mem ← mem.storeCTree addr buf
    return  (#[.int 64 (.val len.toNat)], mem, none)
