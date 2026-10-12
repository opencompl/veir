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
-/

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}

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
    (es : EffectState) (layout : DataLayout := .riscv64)
    : Interp ((Array RuntimeValue) × EffectState × Option ControlFlowAction) :=
  match opType with
  | .arith arithOp => do
    let (vals, act) ← Arith.interpretOp' arithOp properties resultTypes operands blockOperands
    return (vals, es, act)
  | .mod_arith modArithOp => do
    let (vals, act) ← ModArith.interpretOp' modArithOp properties resultTypes operands blockOperands
    return (vals, es, act)
  | .felt feltOp => do
    let (vals, act) ← Felt.interpretOp' feltOp properties resultTypes operands blockOperands
    return (vals, es, act)
  | .llvm llvmOp => do
    let (vals, mem, act) ← Llvm.interpretOp' llvmOp properties resultTypes operands blockOperands es.memory layout
    return (vals, {es with memory := mem}, act)
  | .riscv riscvOp => do
    let (vals, mem, act) ← Riscv.interpretOp' riscvOp properties resultTypes operands blockOperands es.memory
    return (vals, {es with memory := mem}, act)
  | .riscv_cf riscvCfOp => do
    let (vals, act) ← Riscv_Cf.interpretOp' riscvCfOp properties resultTypes operands blockOperands
    return (vals, es, act)
  | .riscv_stack riscvStackOp => do
    let (vals, mem, act) ← Riscv_Stack.interpretOp' riscvStackOp properties resultTypes operands blockOperands es.memory
    return (vals, {es with memory := mem}, act)
  | .rv64 rv64Op => do
    let (vals, act) ← Rv64.interpretOp' rv64Op properties resultTypes operands blockOperands
    return (vals, es, act)
  | .cf cfOp => do
    let (vals, act) ← Cf.interpretOp' cfOp properties resultTypes operands blockOperands
    return (vals, es, act)
  | .io ioOp => do
    Io.interpretOp' ioOp properties resultTypes operands blockOperands es
  | .comb combOp => do
    let (vals, act) ← Comb.interpretOp' combOp properties operands blockOperands
    return (vals, es, act)
  | .hw hwOp => do
    let (vals, act) ← HW.interpretOp' hwOp properties resultTypes blockOperands
    return (vals, es, act)
  | .func .return => do
    return (#[], es, some (.return operands))
  | .cir .return => do
    return (#[], es, some (.return operands))
  | .gmir gmirOp => do
    let (vals, mem, act) ← GMIR.interpretOp' gmirOp properties resultTypes operands blockOperands es.memory
    return (vals, {es with memory := mem}, act)
  | .builtin .unrealized_conversion_cast => do
    let some resType := resultTypes[0]? | none
    match resType.val, operands.toList with
    | .registerType _, [.int _bw val] =>
      return (#[.reg (LLVM.Int.toReg val)], es, none)
    | .registerType _, [.byte _bw val] =>
      return (#[.reg (LLVM.Byte.toReg val)], es, none)
    | .registerType _, [.addr val] =>
      /- A register has no poison to carry. Like a poison integer, a poison pointer
         may become any register value; the interpreter picks 0. -/
      return (#[.reg (LLVM.Int.toReg val.toInt)], es, none)
    | .integerType _bw, [.reg val] =>
      let .integerType resBw := resType.val | none
      return (#[.int resBw.bitwidth (RISCV.Reg.toInt val resBw.bitwidth)], es, none)
    | .byteType _bw, [.reg val] =>
      let .byteType resBw := resType.val | none
      return (#[.byte resBw.bitwidth (RISCV.Reg.toByte val resBw.bitwidth)], es, none)
    | .llvmPointerType _, [.reg val] =>
      return (#[.addr (es.memory.ptrFromInt (.val val.val))], es, none)
    | _ , _ => none
  | _ => none

/-- Wrapper around `interpretOp'` that retrieves the operation type, properties,
result types, and successor blocks from the operation pointer. -/
abbrev OperationPtr.interpret (op : OperationPtr) (ctx : IRContext OpCode)
    (operandValues : Array RuntimeValue) (es : EffectState)
    (layout : DataLayout := .riscv64) :=
    interpretOp' (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
    (op.getResultTypes! ctx) operandValues (op.getSuccessors! ctx) es layout

/--
  Interpret a single operation given the current interpreter state.
  Return an updated interpreter state and a control flow action indicating how
  to continue the interpretation.
  If any error occurs during interpretation (e.g., unknown operation, missing variable),
  return `none`. Failures and UB are blamed on `op`.
-/
@[expose]
def interpretOp (op : OperationPtr) {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (inBounds : op.InBounds ctx.raw := by grind)
    : Interp (InterpreterState ctx × Option ControlFlowAction) := Interp.withBlame op do
  let some operands := state.variables.getOperandValues op | none
  let (resultValues, es, action) ← op.interpret ctx operands state.toEffectState
  let newVars ← state.variables.setResultValues? op resultValues
  let newState := ⟨es, newVars⟩
  return (newState, action)

/--
  Interpret a chain of operations, starting from the given operation pointer.
  Continue to interpret operations until a terminator is encountered,
  or the end of the block is reached.
  Return a ControlFlowAction indicating how to continue the interpretation.
  Return `none` if any errors occur during interpretation.
-/
def interpretOpChain (op : OperationPtr) {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (opInBounds : op.InBounds ctx.raw := by grind)
    : Interp (InterpreterState ctx × ControlFlowAction) := do
  let (state, action) ← interpretOp op state
  match action with
  | none =>
    rlet next ← (op.get ctx.raw).next
    interpretOpChain next state
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
def interpretOpList {ctx : WfIRContext OpCode} (ops : List OperationPtr)
    (state : InterpreterState ctx)
    (opInBounds : ∀ op ∈ ops, op.InBounds ctx.raw := by grind)
    : Interp (InterpreterState ctx × Option ControlFlowAction) :=
  match ops with
  | [] => return (state, none)
  | op :: ops => do
    let (state, action) ← interpretOp op state
    match action with
    | none => interpretOpList ops state (by grind)
    | some cf => return (state, cf)

/--
  Interpret a list of operations passed as a `List`, stopping at the first terminator.
  Return the new interpreter state, and a control flow action indicating how to continue the
  interpretation. If no terminator is encountered, return `none`.
  Return `none` if any errors occur during interpretation.
-/
@[expose]
def interpretTerminatedOpList {ctx : WfIRContext OpCode} (ops : List OperationPtr)
    (state : InterpreterState ctx)
    (opInBounds : ∀ op ∈ ops, op.InBounds ctx.raw := by grind)
    : Interp (InterpreterState ctx × ControlFlowAction) := do
  match ← interpretOpList ops state opInBounds with
  | (_, none) => none
  | (state, some cf) => return (state, cf)

/--
  Interpret a block of operations, starting from the first operation in the block.
  The block arguments are set from `values` before interpreting the operations.
  Return the resulting interpreter state and a ControlFlowAction indicating how
  to continue the interpretation.
  Return `none` if any errors occur during interpretation.
-/
def interpretBlock (blockPtr : BlockPtr) (values : Array RuntimeValue) {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (blockInBounds : blockPtr.InBounds ctx.raw := by grind) :
    Interp (InterpreterState ctx × ControlFlowAction) := do
  let newVars ← state.variables.setArgumentValues? blockPtr values
  let newState := {state with variables := newVars}
  rlet firstOp ← (blockPtr.get ctx.raw).firstOp
  interpretOpChain firstOp newState

/--
  Interpret a CFG, starting from the given block.
  The arguments of the starting block are set from `values`.
  Return the resulting interpreter state and values eventually returned, if any.
  Return `none` if any errors occur during interpretation.
-/
def interpretBlockCFG (blockPtr : BlockPtr) (values : Array RuntimeValue) {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (blockInBounds : blockPtr.InBounds ctx.raw := by grind) :
    Interp (InterpreterState ctx × Array RuntimeValue) := do
  match interpretBlock blockPtr values state blockInBounds with
  | .ok (state, .return res) => .ok (state, res)
  | .ok (state, .branch res succ) =>
    if h : succ.InBounds ctx.raw then
      interpretBlockCFG succ res state h
    else
      .fail none
  | .ub op => .ub op
  | .fail op => .fail op
partial_fixpoint

/--
  Interpret a region, starting from its first block.
  The arguments of the first block are set from `values`.
  Return the resulting interpreter state and values eventually returned, or `none`
  if any errors occur during interpretation.
-/
def interpretRegion (region : RegionPtr) (values : Array RuntimeValue) {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (regionIn : region.InBounds ctx.raw := by grind) :
    Interp (InterpreterState ctx × Array RuntimeValue) := do
  rlet block ← (region.get ctx.raw).firstBlock
  interpretBlockCFG block values state

/--
  Interpret an operation representing a function, given the runtime values of its arguments
  and the current effect state. Return the resulting effect state and the values eventually
  returned.

  Unlike the other interpreter functions, this does not take an `InterpreterState`:
  a function call starts with a fresh, empty variable state, since the caller's SSA
  values are not visible inside the callee.
-/
def interpretFunction {ctx : WfIRContext OpCode} {op : OperationPtr}
    (funcOp : FunctionOp ctx.raw op) (values : Array RuntimeValue)
    (es : EffectState) (opIn : op.InBounds ctx.raw := by grind) :
    Interp (EffectState × Array RuntimeValue) := do
  if h : op.getNumRegions ctx.raw ≠ 1 then
    none
  else
    let state : InterpreterState ctx := ⟨es, .empty ctx⟩
    let (state, results) ← interpretRegion funcOp.getFunctionBody values state
    return (state.toEffectState, results)

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
    let (_state, results) ← interpretRegion (op.getRegion ctx.raw 0) #[] (InterpreterState.empty ctx)
    return results

end Veir
