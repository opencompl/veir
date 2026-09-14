module

public import Veir.RuntimeValue
public import Veir.Interpreter.Memory
public import Veir.IR.WellFormed
public import Veir.GlobalOpInfo

public section

open Veir.Data

/-!
  Various utility definitions for the Veir interpreter.
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

/--
  The state of the interpreter at a given point in time.
  It includes a mapping from IR values to their runtime values.
-/
@[ext]
structure InterpreterState (ctx : WfIRContext OpInfo) where
  variables : VariableState ctx
  memory : MemoryState

/--
  Create an interpreter state with no variables defined.
-/
def InterpreterState.empty (ctx : WfIRContext OpInfo) : InterpreterState ctx :=
  { variables := .empty ctx, memory := .empty }

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
  How the control flow should proceed after interpreting a terminator.
  - `return` indicates that the current block should return with the given values.
  - `branch` indicates that the interpreter should jump to another block
-/
inductive ControlFlowAction where
  | return (vals : Array RuntimeValue)
  | branch (vals : Array RuntimeValue) (dest : BlockPtr)

/--
  Signal UB if the divisor `b` of an unsigned division or remainder could be
  zero. A poison divisor may refine to zero, so it is immediate UB just like a
  concretely-zero one.
-/
@[inline] def Interp.checkUnsignedDivision {w : Nat} (b : LLVM.Int w) : Interp Unit :=
  if b = .poison ∨ b = .val 0 then Interp.ub else pure ()

/--
  Signal UB if the signed division or remainder `a / b` could be undefined:
  a zero divisor, or the `intMin / -1` overflow case. As above, poison operands
  may refine to any value, so they count as possibly triggering either case.
-/
@[inline] def Interp.checkSignedDivision {w : Nat} (a b : LLVM.Int w) : Interp Unit := do
  Interp.checkUnsignedDivision b
  -- The divisor is now concretely nonzero, so only a concrete `-1` can overflow.
  if b = .val (-1) ∧ (a = .poison ∨ a = .val (BitVec.intMin w)) then Interp.ub

end Veir
