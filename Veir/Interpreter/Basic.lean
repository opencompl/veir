module

public import Veir.Interpreter.RuntimeValue
public import Veir.Interpreter.Memory
public import Veir.Interpreter.VariableState
public import Veir.IR.WellFormed
public import Veir.GlobalOpInfo
public import Veir.DataLayout.RISCV64
public import Veir.Data.Felt

import Veir.Data.Comb.Basic
import Veir.Data.HW.Basic
public import Veir.Data.Casting
public import Veir.Interfaces.FunctionInterfaces

public section

open Veir.Data
/-!
  # Veir Interpreter

  This file contains a simple interpreter for a subset of the Veir IR.

  The interpreter walks the linked list of operations in a block. It continues
  until a `func.return` is encountered, at which point the returned values are
  collected and propagated to the caller.

  Calls are performed in a function environment (`FunctionEnv`), which `interpretCall`
  provides. Since functions may call each other, it is a `partial_fixpoint`.
-/

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}

/--
  Interpret a single operation given its opcode, type-dependent properties,
  result types, and the runtime values of its operands.
  Return the result runtime values and an optional control flow action indicating how
  to continue the interpretation.
  If any error occurs during interpretation (e.g., unknown operation, missing variable),
  returns `none`.
-/
@[expose]
def interpretOp' (opType : OpCode) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState) (layout : DataLayout := .riscv64)
    : Interp ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .arith arithOp => do
    let (vals, act) ← Arith.interpretOp' arithOp properties resultTypes operands blockOperands
    return (vals, mem, act)
  | .mod_arith modArithOp => do
    let (vals, act) ← ModArith.interpretOp' modArithOp properties resultTypes operands blockOperands
    return (vals, mem, act)
  | .felt feltOp => do
    let (vals, act) ← Felt.interpretOp' feltOp properties resultTypes operands blockOperands
    return (vals, mem, act)
  | .llvm llvmOp => do
    Llvm.interpretOp' llvmOp properties resultTypes operands blockOperands mem layout
  | .riscv riscvOp => do
    Riscv.interpretOp' riscvOp properties resultTypes operands blockOperands mem
  | .riscv_cf riscvCfOp => do
    let (vals, act) ← Riscv_Cf.interpretOp' riscvCfOp properties resultTypes operands blockOperands
    return (vals, mem, act)
  | .riscv_stack riscvStackOp =>
    Riscv_Stack.interpretOp' riscvStackOp properties resultTypes operands blockOperands mem
  | .rv64 rv64Op => do
    let (vals, act) ← Rv64.interpretOp' rv64Op properties resultTypes operands blockOperands
    return (vals, mem, act)
  | .cf cfOp => do
    let (vals, act) ← Cf.interpretOp' cfOp properties resultTypes operands blockOperands
    return (vals, mem, act)
  | .comb combOp => do
    let (vals, act) ← Comb.interpretOp' combOp properties operands blockOperands
    return (vals, mem, act)
  | .hw hwOp => do
    let (vals, act) ← HW.interpretOp' hwOp properties resultTypes blockOperands
    return (vals, mem, act)
  | .func .return => do
    return (#[], mem, some (.return operands))
  | .func .call => do
    return (#[], mem, some (← Func.callInterface.call? properties operands))
  | .cir .return => do
    return (#[], mem, some (.return operands))
  | .gmir gmirOp => do
    GMIR.interpretOp' gmirOp properties resultTypes operands blockOperands mem
  | .builtin .unrealized_conversion_cast => do
    let some resType := resultTypes[0]? | none
    match resType.val, operands.toList with
    | .registerType _, [.int _bw val] =>
      return (#[.reg (LLVM.Int.toReg val)], mem, none)
    | .registerType _, [.byte _bw val] =>
      return (#[.reg (LLVM.Byte.toReg val)], mem, none)
    | .registerType _, [.addr val] =>
      /- A register has no poison to carry. Like a poison integer, a poison pointer
         may become any register value; the interpreter picks 0. -/
      return (#[.reg (LLVM.Int.toReg val.toInt)], mem, none)
    | .integerType _bw, [.reg val] =>
      let .integerType resBw := resType.val | none
      return (#[.int resBw.bitwidth (RISCV.Reg.toInt val resBw.bitwidth)], mem, none)
    | .byteType _bw, [.reg val] =>
      let .byteType resBw := resType.val | none
      return (#[.byte resBw.bitwidth (RISCV.Reg.toByte val resBw.bitwidth)], mem, none)
    | .llvmPointerType _, [.reg val] =>
      return (#[.addr (mem.ptrFromInt (.val val.val))], mem, none)
    | .integerType resBw, [.byte bw val] =>
      if resBw.bitwidth ≠ bw then none
      return (#[.int bw (LLVM.Byte.toFrozenInt val)], mem, none)
    | .byteType resBw, [.int bw val] =>
      if resBw.bitwidth ≠ bw then none
      return (#[.byte bw (LLVM.Byte.fromInt val)], mem, none)
    | _ , _ => none
  | _ => none

/-- Wrapper around `interpretOp'` that retrieves the operation type, properties,
result types, and successor blocks from the operation pointer. -/
abbrev OperationPtr.interpret (op : OperationPtr) (ctx : IRContext OpCode)
    (operandValues : Array RuntimeValue) (memory : MemoryState)
    (layout : DataLayout := .riscv64) :=
    interpretOp' (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
    (op.getResultTypes! ctx) operandValues (op.getSuccessors! ctx) memory layout

/--
  The context in which a function is executed: the result of calling each callee.
  Callees are symbols rather than bodies, since rewrites preserve symbols.
-/
abbrev FunctionEnv :=
  (callee : FlatSymbolRefAttr) → (args : Array RuntimeValue) → (mem : MemoryState) →
    Interp (MemoryState × Array RuntimeValue)

/--
  Perform the call requested by `action`, if any. The callee's return values replace `results`.
-/
@[expose]
def FunctionEnv.perform (env : FunctionEnv) (results : Array RuntimeValue) (mem : MemoryState) :
    Option ControlFlowAction → Interp (Array RuntimeValue × MemoryState × Option ControlFlowAction)
  | some (.call (.symbol callee) args) => do
    let (mem, results) ← env callee args mem
    return (results, mem, none)
  /- TODO: interpret indirect calls. -/
  | some (.call (.value _) _) => .fail none
  | action => return (results, mem, action)

/-- Interpret an operation and perform the call it requests, if any, in `env`. -/
@[expose]
def OperationPtr.interpretWith (env : FunctionEnv) (op : OperationPtr) (ctx : IRContext OpCode)
    (operandValues : Array RuntimeValue) (memory : MemoryState) :
    Interp (Array RuntimeValue × MemoryState × Option ControlFlowAction) := do
  let (results, mem, action) ← op.interpret ctx operandValues memory
  env.perform results mem action

/--
  Interpret a single operation given the current interpreter state, in `env`.
  Return an updated interpreter state and a control flow action indicating how
  to continue the interpretation.
  If any error occurs during interpretation (e.g., unknown operation, missing variable),
  return `none`. Failures and UB are blamed on `op`, unless a callee already blamed one of its
  operations.
-/
@[expose]
def interpretOp (env : FunctionEnv) (op : OperationPtr) {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (inBounds : op.InBounds ctx.raw := by grind)
    : Interp (InterpreterState ctx × Option ControlFlowAction) := Interp.withBlame op do
  let some operands := state.variables.getOperandValues op | none
  let (resultValues, mem, action) ← op.interpretWith env ctx operands state.memory
  let newVars ← state.variables.setResultValues? op resultValues
  let newState := ⟨newVars, mem⟩
  return (newState, action)

/--
  Interpret a chain of operations, starting from the given operation pointer.
  Continue to interpret operations until a terminator is encountered,
  or the end of the block is reached.
  Return a ControlFlowAction indicating how to continue the interpretation.
  Return `none` if any errors occur during interpretation.
-/
def interpretOpChain (env : FunctionEnv) (op : OperationPtr) {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (opInBounds : op.InBounds ctx.raw := by grind)
    : Interp (InterpreterState ctx × ControlFlowAction) := do
  let (state, action) ← interpretOp env op state
  match action with
  | none =>
    rlet next ← op.getNextOp ctx.raw
    interpretOpChain env next state
  | some action =>
    return (state, action)
termination_by op.idxInParentFromTail ctx.raw
decreasing_by grind

/--
  Interpret a list of operations passed as a `List`, stopping at the first terminator.
  Return the new interpreter state, and an optional control flow action indicating how to
  continue the interpretation, with an absent control flow action indicating that the end of the
  list was reached without encountering a terminator.
  Return `none` if any errors occur during interpretation.
-/
def interpretOpList (env : FunctionEnv) {ctx : WfIRContext OpCode} (ops : List OperationPtr)
    (state : InterpreterState ctx)
    (opInBounds : ∀ op ∈ ops, op.InBounds ctx.raw := by grind)
    : Interp (InterpreterState ctx × Option ControlFlowAction) :=
  match ops with
  | [] => return (state, none)
  | op :: ops => do
    let (state, action) ← interpretOp env op state
    match action with
    | none => interpretOpList env ops state (by grind)
    | some cf => return (state, cf)

/--
  Interpret a list of operations passed as a `List`, stopping at the first terminator.
  Return the new interpreter state, and a control flow action indicating how to continue the
  interpretation. If no terminator is encountered, return `none`.
  Return `none` if any errors occur during interpretation.
-/
@[expose]
def interpretTerminatedOpList (env : FunctionEnv) {ctx : WfIRContext OpCode}
    (ops : List OperationPtr) (state : InterpreterState ctx)
    (opInBounds : ∀ op ∈ ops, op.InBounds ctx.raw := by grind)
    : Interp (InterpreterState ctx × ControlFlowAction) := do
  match ← interpretOpList env ops state opInBounds with
  | (_, none) => none
  | (state, some cf) => return (state, cf)

/--
  Interpret a block of operations, starting from the first operation in the block.
  The block arguments are set from `values` before interpreting the operations.
  Return the resulting interpreter state and a ControlFlowAction indicating how
  to continue the interpretation.
  Return `none` if any errors occur during interpretation.
-/
def interpretBlock (env : FunctionEnv) (blockPtr : BlockPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (blockInBounds : blockPtr.InBounds ctx.raw := by grind) :
    Interp (InterpreterState ctx × ControlFlowAction) := do
  let newVars ← state.variables.setArgumentValues? blockPtr values
  let state := ⟨newVars, state.memory⟩
  rlet firstOp ← blockPtr.getFirstOp ctx.raw
  interpretOpChain env firstOp state

/--
  Interpret a CFG, starting from the given block.
  The arguments of the starting block are set from `values`.
  Return the resulting interpreter state and values eventually returned, if any.
  Return `none` if any errors occur during interpretation.
-/
def interpretBlockCFG (env : FunctionEnv) (blockPtr : BlockPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (blockInBounds : blockPtr.InBounds ctx.raw := by grind) :
    Interp (InterpreterState ctx × Array RuntimeValue) := do
  match interpretBlock env blockPtr values state blockInBounds with
  | .ok (state, .return res) => .ok (state, res)
  | .ok (state, .branch res succ) =>
    if h : succ.InBounds ctx.raw then
      interpretBlockCFG env succ res state h
    else
      .fail none
  /- Unreachable: `interpretOp` performs all calls. -/
  | .ok (_, .call _ _) => .fail none
  | .ub op => .ub op
  | .fail op => .fail op
  | .spin => .spin
partial_fixpoint

/--
  Interpret a region, starting from its first block.
  The arguments of the first block are set from `values`.
  Return the resulting interpreter state and values eventually returned, or `none`
  if any errors occur during interpretation.
-/
def interpretRegion (env : FunctionEnv) (region : RegionPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (regionIn : region.InBounds ctx.raw := by grind) :
    Interp (InterpreterState ctx × Array RuntimeValue) := do
  rlet block ← region.getFirstBlock ctx.raw
  interpretBlockCFG env block values state

/--
  Interpret an operation representing a function, given the runtime values of its arguments
  and the current memory state, in the function environment `env`. Return the resulting memory state
  and the values eventually returned.

  Unlike the other interpreter functions, this does not take an `InterpreterState`:
  a function call starts with a fresh, empty variable state, since the caller's SSA
  values are not visible inside the callee.
-/
def interpretFunctionWith (env : FunctionEnv) {ctx : WfIRContext OpCode} {op : OperationPtr}
    (funcOp : FunctionOp ctx.raw op) (values : Array RuntimeValue)
    (mem : MemoryState) (opIn : op.InBounds ctx.raw := by grind) :
    Interp (MemoryState × Array RuntimeValue) := do
  if h : op.getNumRegions ctx.raw ≠ 1 then
    none
  else
    let state : InterpreterState ctx := ⟨.empty ctx, mem⟩
    let (state, results) ← interpretRegion env funcOp.getFunctionBody values state
    return (state.memory, results)

/-!
  ## Monotonicity in the function environment

  `interpretCall` is a `partial_fixpoint`, so interpreting a function body must be monotone in
  the function environment.
-/

section Monotonicity

open Lean.Order

variable {γ : Type} [PartialOrder γ] {f : γ → FunctionEnv}

/-- Interpreting an operation is monotone in the function environment. -/
@[partial_fixpoint_monotone]
theorem monotone_interpretOp (hmono : monotone f) {op : OperationPtr} {ctx : WfIRContext OpCode}
    {state : InterpreterState ctx} {inBounds : op.InBounds ctx.raw} :
    monotone (fun x => interpretOp (f x) op state inBounds) := by
  unfold interpretOp OperationPtr.interpretWith FunctionEnv.perform
  repeat' monotonicity
  all_goals solve_by_elim [monotone_apply, hmono]

/-- Interpreting an operation chain is monotone in the function environment. -/
@[partial_fixpoint_monotone]
theorem monotone_interpretOpChain (hmono : monotone f) {op : OperationPtr}
    {ctx : WfIRContext OpCode} {state : InterpreterState ctx} {opInBounds : op.InBounds ctx.raw} :
    monotone (fun x => interpretOpChain (f x) op state opInBounds) := by
  induction hn : op.idxInParentFromTail ctx.raw using Nat.strongRecOn
    generalizing op state with
  | ind n ih =>
    unfold interpretOpChain
    repeat' monotonicity
    all_goals first
      | solve_by_elim [monotone_apply, hmono]
      | exact ih _ (by grind) rfl

/-- Interpreting a block is monotone in the function environment. -/
@[partial_fixpoint_monotone]
theorem monotone_interpretBlock (hmono : monotone f) {block : BlockPtr}
    {values : Array RuntimeValue} {ctx : WfIRContext OpCode} {state : InterpreterState ctx}
    {blockInBounds : block.InBounds ctx.raw} :
    monotone (fun x => interpretBlock (f x) block values state blockInBounds) := by
  unfold interpretBlock
  repeat' monotonicity
  all_goals solve_by_elim [monotone_apply, hmono]

/-- Interpreting a CFG is monotone in the function environment. -/
@[partial_fixpoint_monotone]
theorem monotone_interpretBlockCFG (hmono : monotone f) {block : BlockPtr}
    {values : Array RuntimeValue} {ctx : WfIRContext OpCode} {state : InterpreterState ctx}
    {blockInBounds : block.InBounds ctx.raw} :
    monotone (fun x => interpretBlockCFG (f x) block values state blockInBounds) := by
  intro x y hxy
  /- By fixpoint induction, every approximation of `interpretBlockCFG (f x)` is below
     `interpretBlockCFG (f y)`. -/
  refine interpretBlockCFG.fixpoint_induct (env := f x) (ctx := ctx)
    (motive := fun g => @g ⊑ fun block values state blockIn =>
      interpretBlockCFG (f y) block values state blockIn)
    (admissible_rel _) ?_ block values state blockInBounds
  intro g hg block values state blockInBounds
  dsimp only
  rw [interpretBlockCFG]
  /- The block run with `f x` either never terminates or equals the one run with `f y`.
     Only a branch recurses. -/
  rcases Interp.rel_iff.mp (monotone_interpretBlock (block := block) (values := values)
    (state := state) (blockInBounds := blockInBounds) hmono x y hxy) with h | h <;>
    dsimp only at h
  · rw [h]
    exact Interp.rel_iff.mpr (.inl rfl)
  · rw [h]
    split <;> (try split) <;> first | exact hg _ _ _ _ | exact PartialOrder.rel_refl

/-- Interpreting a region is monotone in the function environment. -/
@[partial_fixpoint_monotone]
theorem monotone_interpretRegion (hmono : monotone f) {region : RegionPtr}
    {values : Array RuntimeValue} {ctx : WfIRContext OpCode} {state : InterpreterState ctx}
    {regionIn : region.InBounds ctx.raw} :
    monotone (fun x => interpretRegion (f x) region values state regionIn) := by
  unfold interpretRegion
  repeat' monotonicity
  all_goals solve_by_elim [monotone_apply, hmono]

/-- Interpreting a function body is monotone in the function environment. -/
@[partial_fixpoint_monotone]
theorem monotone_interpretFunctionWith (hmono : monotone f) {ctx : WfIRContext OpCode}
    {op : OperationPtr} {funcOp : FunctionOp ctx.raw op} {values : Array RuntimeValue}
    {mem : MemoryState} {opIn : op.InBounds ctx.raw} :
    monotone (fun x => interpretFunctionWith (f x) funcOp values mem opIn) := by
  unfold interpretFunctionWith
  repeat' monotonicity
  all_goals solve_by_elim [monotone_apply, hmono]

end Monotonicity

/--
  Call the function `callee`, looked up from `scope`, with arguments `args` and memory `mem`.
  Calls in its body are looked up from the callee. This matches MLIR, which looks up from the call,
  unless a symbol table lies between the call and the function.
  A call that never terminates returns `spin`.
-/
def interpretCall (ctx : WfIRContext OpCode) (scope : OperationPtr) (callee : FlatSymbolRefAttr)
    (args : Array RuntimeValue) (mem : MemoryState) :
    Interp (MemoryState × Array RuntimeValue) := do
  let some ⟨function, funcOp⟩ := FunctionOp.lookup? scope ctx.raw callee | .fail none
  if h : function.InBounds ctx.raw then
    interpretFunctionWith (interpretCall ctx function) funcOp args mem h
  else
    .fail none
partial_fixpoint

/--
  Interpret an operation representing a function, given the runtime values of its arguments
  and the current memory state. Return the resulting memory state and the values eventually
  returned. Calls are looked up from `op` and performed by `interpretCall`.
-/
def interpretFunction {ctx : WfIRContext OpCode} {op : OperationPtr}
    (funcOp : FunctionOp ctx.raw op) (values : Array RuntimeValue)
    (mem : MemoryState) (opIn : op.InBounds ctx.raw := by grind) :
    Interp (MemoryState × Array RuntimeValue) :=
  interpretFunctionWith (interpretCall ctx op) funcOp values mem opIn

/--
  Interpret a builtin.module operation.
  This is done by interpreting the unique region of the operation.
  Return the values eventually returned, or `none` if any errors occur during interpretation.
-/
def interpretModule (ctx : WfIRContext OpCode) (op : OperationPtr)
    (opIn : op.InBounds ctx.raw := by grind) : Interp (Array RuntimeValue) := do
  if h: op.getNumRegions ctx.raw ≠ 1 then
    none
  else
    let (_state, results) ←
      interpretRegion (interpretCall ctx op) (op.getRegion ctx.raw 0) #[]
        (InterpreterState.empty ctx)
    return results

end Veir
