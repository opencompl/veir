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
  | sendE (msg : ByteArray)
  | recvE
  | randE (len : Nat)

/-- Output type for an IO effect -/
abbrev IoE (e : IoEIn) :=
  match e with
  | .sendE _ => Unit
  | .recvE => Option (Nat × ByteArray) -- sender & payload
  | .randE _ => ByteArray

/-- Emit an IO send effect -/
def ioSend [IoE -< E] (msg : ByteArray) : CTree E C Unit := CTree.trigger (SubE := IoE) (.sendE msg)
/-- Emit an IO receive effect -/
def ioRecv [IoE -< E] : CTree E C (Option (Nat × ByteArray)) := CTree.trigger (SubE := IoE) (.recvE)
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
    ioSend buf
    let ns' := em.network.sendMessage dest buf
    return (#[.int 64 (.val buf.size)], {em with network := ns'}, none)
  | .recv => do
    let [.addr ptr, .int _ len] := operands.toList | ub
    let .val len := len | ub
    let .val ptr := ptr | ub
    let len := len.toNat
    let optResult ← ioRecv
    let (status, src, em') ← match optResult with
    | none => pure (Io.Error.exhausted, 0, em)
    | some (src, payload) =>
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
    let buf ← ioRand lenNat
    let mem' ← em.memory.storeCTree addr buf
    return  (#[.int 64 (.val len.toNat)], {em with memory := mem'}, none)
