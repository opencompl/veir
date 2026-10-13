module

public import Veir.Interpreter.Memory

public section

/-!
# Effect State

The state that side-effecting operations read and write: memory, the entropy source, and the
network. It does not depend on the IR context, so that dialects can interpret against it.
-/

namespace Veir

structure EntropyState where
  entropySource : ByteArray

/--
  Create an entropy state with no entropy defined.
-/
def EntropyState.empty : EntropyState :=
  ⟨ByteArray.empty⟩

structure Message where
  src : Nat
  dest : Nat
  payload : ByteArray
deriving BEq, Inhabited

structure NetworkState where
  /-- Address of this run. -/
  selfAddress : Nat
  /-- in-flight messages in the network. -/
  messages : List Message

/--
  Create a network state with no messages defined and a default address.
-/
def NetworkState.empty : NetworkState :=
  {selfAddress := 0, messages := []}

@[ext]
structure EffectState where
  memory : MemoryState
  entropy : EntropyState
  network : NetworkState

/--
  Create an effect state with no values defined.
-/
def EffectState.empty : EffectState :=
  {memory := .empty, entropy := .empty, network := .empty}

/--
  Consume bytes from the entropy source.
  Yields UB if the access is out of bounds.
-/
def EntropyState.entropyLoad (state : EntropyState) (size : UInt64)
    : Interp (EntropyState × ByteArray) := do
  if state.entropySource.size < size.toNat then Interp.ub none
  let ba := state.entropySource.extract 0 size.toNat
  let newState := {state with
    entropySource := state.entropySource.extract size.toNat state.entropySource.size,
  }
  return (newState, ba)

/--
  Get the current self address
-/
def NetworkState.getSelfAddress (state : NetworkState) : Nat :=
  state.selfAddress

/--
  Set the current self address
-/
def NetworkState.setSelfAddress (state : NetworkState) (addr : Nat) : NetworkState :=
  {state with selfAddress := addr}

/--
  Add an inflight message to the network
-/
def NetworkState.sendMessage (state : NetworkState) (dest : Nat) (payload : ByteArray)
    : NetworkState :=
  let msg : Message := { src := state.selfAddress, dest := dest, payload := payload }
  {state with messages := state.messages ++ [msg]}

/--
  Consume the next inflight message destined for the current address
-/
def NetworkState.consumeMessage (state : NetworkState)
    : Option (NetworkState × Message) :=
  let optMsg := state.messages.find? (fun msg => msg.dest = state.selfAddress)
  optMsg.map fun msg =>
    let newState := {state with messages := state.messages.erase msg}
    (newState, msg)

end Veir
