module

public import Veir.Interpreter.RuntimeValue
public import Veir.Interpreter.Memory
public import Veir.IR.WellFormed

public section

open Veir.Data

/-!
# Variable State

Definition of the interpreter's variable state, which maps IR values to runtime values.
-/

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}

/-!
  The interpreter maintains a `VariableState` mapping from IR values (`ValuePtr`) to runtime
  values (`RuntimeValue`). Each supported operation reads its operands from this
  mapping and writes its results back into it.
-/

/--
  Property that a hash map from `ValuePtr` to `RuntimeValue` conforms to the value types in the
  IR context. This is an invariant that must be maintained by the variable state of the interpreter.
-/
def VariableState.ValuesConform (state : Std.ExtHashMap ValuePtr RuntimeValue)
    (ctx : WfIRContext OpInfo) : Prop :=
  ∀ val var, (h : val ∈ state) → state[val] = var → var.Conforms (val.getType! ctx.raw)

structure VariableState (ctx : WfIRContext OpInfo) where
  variables : Std.ExtHashMap ValuePtr RuntimeValue
  conforms : VariableState.ValuesConform variables ctx
  variablesIn : ∀ val, val ∈ variables → val.InBounds ctx.raw

/--
  Create a variable state with no variables defined.
-/
def VariableState.empty (ctx : WfIRContext OpInfo) : VariableState ctx :=
  ⟨Std.ExtHashMap.emptyWithCapacity 8, by simp [VariableState.ValuesConform], by simp⟩

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
  The state of the interpreter at a given point in time.
  It includes a mapping from IR values to their runtime values.
-/
@[ext]
structure InterpreterState (ctx : WfIRContext OpInfo) extends EffectState where
  variables : VariableState ctx

/--
  Create an interpreter state with no variables defined.
-/
def InterpreterState.empty (ctx : WfIRContext OpInfo) : InterpreterState ctx :=
  ⟨ .empty, .empty ctx ⟩

/--
  Set the runtime value of a variable.
  This function dynamically checks that the runtime value conforms to the variable type, and
  return `none` otherwise.
-/
def VariableState.setVar? (state : VariableState ctx) (var : ValuePtr)
    (val : RuntimeValue) (inBounds : var.InBounds ctx.raw := by grind) :
    Option (VariableState ctx) :=
  if h : val.Conforms (var.getType! ctx.raw) then
    some ⟨state.variables.insert var val,
      by grind [VariableState.ValuesConform, cases VariableState],
      by grind [cases VariableState]⟩
  else
    none

/--
  Set the runtime value of a variable.
  This function requires a proof that the runtime value conforms to the variable type.
-/
def VariableState.setVar (state : VariableState ctx) (var : ValuePtr)
    (val : RuntimeValue) (h : val.Conforms (var.getType! ctx.raw) := by grind)
    (inBounds : var.InBounds ctx.raw := by grind) :
    VariableState ctx :=
  ⟨state.variables.insert var val,
    by grind [VariableState.ValuesConform, cases VariableState],
    by grind [cases VariableState]⟩

/--
  Get the value of a variable, if the variable exists.
-/
def VariableState.getVar? (state : VariableState ctx) (var : ValuePtr)
    : Option RuntimeValue :=
  state.variables[var]?

@[ext]
theorem VariableState.ext {s₁ s₂ : VariableState ctx} :
    (∀ var, s₁.getVar? var = s₂.getVar? var) →
    s₁ = s₂ := by
  rcases s₁; rcases s₂
  simp only [VariableState.getVar?, mk.injEq]
  grind

/--
  Get the value of the operands of an operation.
  If any operand is not in the state, return `none`.
-/
@[expose]
def VariableState.getOperandValues (state : VariableState ctx)
    (op : OperationPtr) : Option (Array RuntimeValue) := do
  (op.getOperands! ctx.raw).mapM state.getVar?

def VariableState.setResultValues?_loop (state : VariableState ctx)
    (op : OperationPtr) (resultValues : Array RuntimeValue) (i : Nat)
    (opInBounds : op.InBounds ctx.raw := by grind)
    (iInBounds : i ≤ op.getNumResults! ctx.raw := by grind)
    (hsizes : resultValues.size = op.getNumResults! ctx.raw := by grind)
    : Option (VariableState ctx) :=
  match i with
  | 0 => state
  | i + 1 => do
    let result := op.getResult i
    let value := resultValues[i]
    let newState ← state.setVar? result value
    VariableState.setResultValues?_loop newState op resultValues i

/--
  Set the values of the results of an operation.
-/
def VariableState.setResultValues? (state : VariableState ctx)
    (op : OperationPtr) (resultValues : Array RuntimeValue) (opInBounds : op.InBounds ctx.raw := by grind)
    : Option (VariableState ctx) :=
  if hsize : resultValues.size = op.getNumResults! ctx.raw then
    VariableState.setResultValues?_loop state op resultValues (op.getNumResults! ctx.raw)
  else
    none

/--
  Implementation loop for setting the values of block arguments.
-/
def VariableState.setArgumentValues?_loop (state : VariableState ctx)
    (block : BlockPtr) (values : Array RuntimeValue) (i : Nat)
    (blockInBounds : block.InBounds ctx.raw := by grind)
    (iInBounds : i ≤ block.getNumArguments! ctx.raw := by grind)
    : Option (VariableState ctx) :=
  match i with
  | 0 => state
  | i + 1 => do
    let arg := block.getArgument i
    let value := values[i]!
    let newState ← state.setVar? arg value
    VariableState.setArgumentValues?_loop newState block values i

/--
  Set the values of block arguments.
-/
def VariableState.setArgumentValues? (state : VariableState ctx)
    (block : BlockPtr) (values : Array RuntimeValue)
    (blockInBounds : block.InBounds ctx.raw := by grind)
    : Option (VariableState ctx) :=
  VariableState.setArgumentValues?_loop state block values (block.getNumArguments! ctx.raw)

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
