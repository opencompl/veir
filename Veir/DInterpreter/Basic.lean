import Veir.IR.Basic
import Veir.Rewriter.Basic
import Veir.ForLean
import Veir.IR.WellFormed
import Veir.PatternRewriter.Basic
import Veir.Data.LLVM.Int.Basic
import Veir.Data.RISCV.Reg.Basic
import Veir.Data.Casting
import Veir.Properties
import Veir.GlobalOpInfo

open Veir.Data
/-!
  # Veir Interpreter

  This file contains a simple interpreter for a subset of the Veir IR.

  The interpreter maintains a mapping from IR values (`ValuePtr`) to runtime
  values (`UInt64`). Each supported operation reads its operands from this
  mapping and writes its results back into it.

  The interpreter walks the linked list of operations in a block. It continues
  until a `func.return` is encountered, at which point the returned values are
  collected and propagated to the caller.
-/

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] {ctx : WfIRContext OpInfo}

@[grind]
def runtimeValueType (type : TypeAttr) : Type :=
  match type.val with
  | .integerType bw => LLVM.Int bw.bitwidth
  | .registerType _ => RISCV.Reg
  | _ => Unit

instance : Inhabited (runtimeValueType type) :=
  match type with
  | ⟨.integerType bw, _⟩ => ⟨LLVM.Int.poison (w := bw.bitwidth)⟩
  | ⟨.registerType _, _⟩ => ⟨RISCV.Reg.mk 0⟩
  | _ => sorry

/--
  The state of the interpreter at a given point in time.
  It includes a mapping from IR values to their runtime values.
-/
structure InterpreterState (ctx : WfIRContext OpInfo) where
  variables : Std.ExtDHashMap ValuePtr (fun value => runtimeValueType (value.getType! ctx.raw))

def InterpreterState.move (state : InterpreterState ctx) (newCtx : WfIRContext OpInfo) : InterpreterState newCtx :=
  { variables := state.variables.map
      (fun var val => if h : (var.getType! newCtx.raw) = (var.getType! ctx.raw) then h ▸ val else default) }

/--
  Set the value of a variable.
-/
def InterpreterState.setVar (state : InterpreterState ctx) (var : ValuePtr) (val : runtimeValueType (var.getType! ctx.raw)) :
    InterpreterState ctx :=
  {state with variables := state.variables.insert var val}

def InterpreterState.setVar' (state : InterpreterState ctx) (var : ValuePtr) (α : Type) (val : α)
    (hα : α = runtimeValueType (var.getType! ctx.raw) := by grind) :
    InterpreterState ctx :=
  {state with variables := state.variables.insert var (hα ▸ val)}

/--
  Get the value of a variable, if the variable exists.
-/
def InterpreterState.getVar? (state : InterpreterState ctx) (var : ValuePtr)
    : Option (runtimeValueType (var.getType! ctx.raw)) :=
  state.variables.get? var

def InterpreterState.getVar! (state : InterpreterState ctx) (var : ValuePtr)
    : runtimeValueType (var.getType! ctx.raw) :=
  state.variables.get! var

def InterpreterState.getVar'! (state : InterpreterState ctx) (var : ValuePtr)
    (α : Type) (hα : α = runtimeValueType (var.getType! ctx.raw) := by grind) :
    α :=
  hα ▸ state.variables.get! var

@[ext]
theorem InterpreterState.ext {s₁ s₂ : InterpreterState ctx} :
    (∀ var, s₁.getVar? var = s₂.getVar? var) →
    s₁ = s₂ := by
  rcases s₁; rcases s₂
  simp only [getVar?, mk.injEq]
  grind

/--
  Create an interpreter state with no variables defined.
-/
def InterpreterState.empty : InterpreterState ctx :=
  { variables := Std.ExtDHashMap.emptyWithCapacity 8 }

/--
  How the control flow should proceed after interpreting a terminator.
  - `return` indicates that the current block should return with the given values.
  - `branch` indicates that the interpreter should jump to another block
-/
inductive ControlFlowAction where
  | return (vals : Array RuntimeValue)
  | branch (vals : Array RuntimeValue) (dest : BlockPtr)
deriving Inhabited

def arithConstant_getType (ctx : WfIRContext OpCode) (op : OperationPtr)
    (hop : op.getOpType! ctx.raw = .arith .constant := by grind) : IntegerType :=
  match ((op.getResult 0).get! ctx.raw).type.val with
  | .integerType integerType => integerType
  | _ => sorry

@[grind =]
theorem arithConstant_getType_resultType (ctx : WfIRContext OpCode) (op : OperationPtr)
    (hop : op.getOpType! ctx.raw = .arith .constant := by grind) :
    (op.getResult 0 : ValuePtr).getType! ctx.raw = arithConstant_getType ctx op hop := by sorry

def arithAddi_getType (ctx : WfIRContext OpCode) (op : OperationPtr)
    (hop : op.getOpType! ctx.raw = .arith .addi := by grind) : IntegerType :=
  match ((op.getResult 0).get! ctx.raw).type.val with
  | .integerType integerType => integerType
  | _ => sorry

@[grind =]
theorem arithAddi_getType_resultType {ctx : WfIRContext OpCode} {op : OperationPtr}
    (hop : op.getOpType! ctx.raw = .arith .addi := by grind) :
    (op.getResult 0 : ValuePtr).getType! ctx.raw = arithAddi_getType ctx op hop := by sorry

@[grind =]
theorem arithAddi_getType_lhsType {ctx : WfIRContext OpCode} {op : OperationPtr}
    (hop : op.getOpType! ctx.raw = .arith .addi := by grind) :
    (op.getOperand! ctx.raw 0 : ValuePtr).getType! ctx.raw = arithAddi_getType ctx op hop := by sorry

@[grind =]
theorem arithAddi_getType_rhsType {ctx : WfIRContext OpCode} {op : OperationPtr}
    (hop : op.getOpType! ctx.raw = .arith .addi := by grind) :
    (op.getOperand! ctx.raw 1 : ValuePtr).getType! ctx.raw = arithAddi_getType ctx op hop := by sorry

def interpretConstant (ctx : WfIRContext OpCode) (op : OperationPtr) (state : InterpreterState ctx)
    (hAdd : op.getOpType! ctx.raw = .arith .constant := by grind) : InterpreterState ctx :=
  let resVal : ValuePtr := op.getResult 0
  let resType := arithConstant_getType ctx op
  let properties := op.getProperties! ctx.raw (.arith .constant)
  state.setVar' resVal (LLVM.Int resType.bitwidth) (.val (BitVec.ofInt resType.bitwidth properties.value.value))

def interpretAddi (ctx : WfIRContext OpCode) (op : OperationPtr) (state : InterpreterState ctx)
    (hAdd : op.getOpType! ctx.raw = .arith .addi := by grind) : InterpreterState ctx :=
  let resType := arithAddi_getType ctx op
  let lhsVal := state.getVar'! (op.getOperand! ctx.raw 0) (LLVM.Int resType.bitwidth)
  let rhsVal := state.getVar'! (op.getOperand! ctx.raw 1) (LLVM.Int resType.bitwidth)
  let properties := op.getProperties! ctx.raw (.arith .addi)
  let resVal := LLVM.Int.add lhsVal rhsVal properties.nsw properties.nuw
  let resVar := op.getResult 0
  state.setVar' resVar (LLVM.Int resType.bitwidth) resVal

def interpretOp (ctx : WfIRContext OpCode) (op : OperationPtr) (state : InterpreterState ctx)
    : InterpreterState ctx × Option ControlFlowAction :=
  match h: op.getOpType! ctx.raw with
  | .arith .constant =>
    (interpretConstant ctx op state (by grind), none)
  | .arith .addi =>
    (interpretAddi ctx op state (by grind), none)
  | _ => (state, none)

/--
  Interpret a list of operations, starting from the given operation pointer.
  Continue to interpret operations until a terminator is encountered,
  or the end of the block is reached.
  Return a ControlFlowAction indicating how to continue the interpretation.
  Return `none` if any errors occur during interpretation.
-/
def interpretOpList (ctx : WfIRContext OpCode) (op : OperationPtr) (state : InterpreterState ctx)
    (opInBounds : op.InBounds ctx.raw := by grind) : Option ControlFlowAction := do
  let (state, action) := interpretOp ctx op state
  match action with
  | none =>
    rlet next ← (op.get ctx.raw).next
    interpretOpList ctx next state
  | some action =>
    return action
termination_by op.idxInParentFromTail ctx.raw
decreasing_by grind

/--
  Interpret a list of operations.
  Return the new interpreter state, and a control flow action indicating how to continue
  the interpretation.
  If a `return` is encountered, the following operations are not interpreted.
  Return `none` if any errors occur during interpretation.
-/
def interpretOpList' (ctx : WfIRContext OpCode) (ops : List OperationPtr) (state : InterpreterState ctx)
    (opInBounds : ∀ op ∈ ops, op.InBounds ctx.raw := by grind)
    : InterpreterState ctx × Option ControlFlowAction :=
  match ops with
  | [] => (state, none)
  | op :: ops =>
    let (state, action) := interpretOp ctx op state
    match action with
    | none => interpretOpList' ctx ops state (by grind)
    | some cf => (state, cf)

/--
  Interpret a block of operations, starting from the first operation in the block.
  Return a ControlFlowAction indicating how to continue the interpretation.
  Return `none` if any errors occur during interpretation.
-/
def interpretBlock (ctx : WfIRContext OpCode) (blockPtr : BlockPtr) (state : InterpreterState ctx) (blockInBounds : blockPtr.InBounds ctx.raw := by grind) : Option ControlFlowAction := do
  let block := blockPtr.get ctx.raw (by grind)
  rlet firstOp ← (blockPtr.get ctx.raw).firstOp
  interpretOpList ctx firstOp state

/-
/--
  Interpret a CFG, starting from the given block.
  Return the values eventually returned, if any.
  Return `none` if any errors occur during interpretation.
-/
def interpretBlockCFG (ctx : WfIRContext OpCode) (blockPtr : BlockPtr) (state : InterpreterState ctx) (blockInBounds : blockPtr.InBounds ctx.raw := by grind) : Option (Array RuntimeValue) := do
  match interpretBlock ctx blockPtr state blockInBounds with
  | some (.return res) => some res
  | some (.branch res succ) =>
    if h : succ.InBounds ctx.raw then
      let state := state.setArgumentValues ctx.raw succ res
      interpretBlockCFG ctx.raw succ state h wf else none
  | none => none
partial_fixpoint

/--
  Interpret a region, starting from its first block.
  Return the values eventually returned, or `none` if any errors occur during interpretation.
-/
def interpretRegion (ctx : IRContext OpCode) (region : RegionPtr) (state : InterpreterState) (regionIn : region.InBounds ctx := by grind) (wf : ctx.WellFormed := by grind) : Option (Array RuntimeValue) := do
  rlet block ← (region.get ctx).firstBlock
  interpretBlockCFG ctx block state

/--
  Interpret a builtin.module operation.
  This is done by interpreting the unique region of the operation.
  Return the values eventually returned, or `none` if any errors occur during interpretation.
-/
def interpretModule (ctx : IRContext OpCode) (op : OperationPtr)
    (opIn : op.InBounds ctx := by grind) (wf : ctx.WellFormed := by grind)
    : Option (Array RuntimeValue) := do
  if h: op.getNumRegions ctx ≠ 1 then
    none
  else
    interpretRegion ctx (op.getRegion ctx 0) InterpreterState.empty
-/
end Veir
