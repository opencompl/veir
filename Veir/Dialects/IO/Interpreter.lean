module

public import Veir.Interpreter.RuntimeValue
public import Veir.Interpreter.Memory
public import Veir.Interpreter.EffectState
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

def Io.interpretOpCTree [ErrorE -< E] [UBE -< E] [IoE -< E] (opType : Veir.Io)
    (properties : propertiesOf opType)
    (_resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (_blockOperands : Array BlockPtr) (em : EffectState)
    : CTree E C ((Array RuntimeValue) × EffectState × Option ControlFlowAction) :=
  match opType with
  | .self => do
    return (#[.ioAddr em.network.selfAddress], em, none)
  | .send => do
    let [.ioAddr dest, .addr ptr, .int _ len] := operands.toList | ub
    let .val len := len | ub
    let .val ptr := ptr | ub
    let lenNat := len.toNat
    if lenNat ≥ UInt64.size then ub
    let len : UInt64 := UInt64.ofNat lenNat
    if ← em.memory.hasPoisonCTree ptr len then ub
    let buf ← em.memory.loadCTree ptr len
    -- note that we update the CTree but not the EffectState's NetworkState
    ioSend { src := em.network.selfAddress, dest, payload := buf }
    return (#[.int 64 (.val buf.size)], em, none)
  | .recv => do
    let [.addr ptr, .int _ len] := operands.toList | ub
    let .val len := len | ub
    let .val ptr := ptr | ub
    let len := len.toNat
    -- note that we use the CTree to receive a message without using EffectState's NetworkState
    let optResult ← ioRecv
    let (status, src, em') ← match optResult with
    | none => pure (Io.Error.exhausted, 0, em)
    | some { src := src, dest := _, payload := payload } =>
      if payload.size > len then
        pure (Io.Error.messageTooLong, 0, em)
      else do
        let mem' ← em.memory.storeCTree ptr payload
        pure (payload.size, src, {em with memory := mem'})
    return (#[.int 64 (.val (BitVec.ofInt 64 status)), .ioAddr src], em', none)
  | .rand => do
    let [.addr addr, .int _ len] := operands.toList | ub
    let .val len := len | ub
    let .val addr := addr | ub
    let lenNat := len.toNat
    if lenNat ≥ UInt64.size then ub
    -- note that we use the CTree to obtain a buffer with random data without using EffectState's EntropyState
    let buf ← ioRand lenNat
    let mem' ← em.memory.storeCTree addr buf
    return  (#[.int 64 (.val len.toNat)], {em with memory := mem'}, none)
