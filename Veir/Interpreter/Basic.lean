import Veir.IR.Basic
import Veir.Rewriter.Basic
import Veir.ForLean
import Veir.IR.WellFormed
import Veir.PatternRewriter.Basic
import Veir.Data.Comb.Basic
import Veir.Data.LLVM.Int.Basic
import Veir.Data.RISCV.Reg.Basic
import Veir.Data.HW.Basic
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

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}

/--
  The type-erased representation of a value in the interpreter.
-/
inductive RuntimeValue where
| int (bitwidth : Nat) (value : LLVM.Int bitwidth)
| addr (value : UInt64)
| reg (value : RISCV.Reg)
deriving Inhabited

instance : ToString (RuntimeValue) where
  toString
    | .int _ val => ToString.toString val
    | .addr val => ToString.toString val
    | .reg val => ToString.toString val

namespace RuntimeValue

/--
  A predicate indicating whether a `RuntimeValue` is a value that is a runtime value
  of a given `TypeAttr`.
-/
@[grind]
def Conforms (val : RuntimeValue) (ty : TypeAttr) : Prop :=
  match val, ty with
  | .int bw _, ⟨.integerType intType, _⟩ => intType.bitwidth = bw
  | .reg _, ⟨.registerType _, _⟩ => True
  | .addr _, ⟨.llvmPointerType _, _⟩ => True
  | _, _ => False

instance : Decidable (Conforms val ty) := by
  unfold Conforms
  split <;> infer_instance

@[grind <=]
theorem Conforms.integerType :
    Conforms runtimeValue ⟨.integerType intType, h⟩ →
    ∃ val, runtimeValue = .int intType.bitwidth val := by
  simp only [Conforms]
  cases runtimeValue
  case int bw val =>
    simp only [int.injEq, exists_and_left]
    intro _; subst bw
    grind
  all_goals grind

@[grind <=]
theorem Conforms.registerType :
    Conforms runtimeValue ⟨.registerType regType, h⟩ →
    ∃ val, runtimeValue = .reg val := by
  simp only [Conforms]
  cases runtimeValue <;> grind

@[grind <=]
theorem Conforms.llvmPointerType :
    Conforms runtimeValue ⟨.llvmPointerType _, h⟩ →
    ∃ val, runtimeValue = .addr val := by
  simp only [Conforms]
  cases runtimeValue <;> grind

end RuntimeValue

/--
  Memory state during interpretation
-/
@[ext]
structure MemoryState where
  contents : ByteArray

def MemoryState.empty : MemoryState :=
  { contents := (ByteArray.emptyWithCapacity 1024).extend 8 0xff }

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
  { variables := ⟨Std.ExtHashMap.emptyWithCapacity 8, by simp [VariableState.ValuesConform], by simp⟩, memory := .empty }

/--
  Set the value of a variable.
-/
def VariableState.setVar? (state : VariableState ctx) (var : ValuePtr)
    (val : RuntimeValue) (inBounds : var.InBounds ctx.raw := by grind)
    : Option (VariableState ctx) :=
  if h : val.Conforms (var.getType! ctx.raw) then
    some ⟨state.variables.insert var val,
      by grind [VariableState.ValuesConform, cases VariableState],
      by grind [cases VariableState]⟩
  else
    none

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
def VariableState.getOperandValues (state : VariableState ctx)
    (op : OperationPtr) : Option (Array RuntimeValue) := do
  (op.getOperands! ctx.raw).mapM state.getVar?

def VariableState.setResultValues?_loop (state : VariableState ctx)
    (op : OperationPtr) (resultValues : Array RuntimeValue) (i : Nat)
    (opInBounds : op.InBounds ctx.raw := by grind) (iInBounds : i ≤ op.getNumResults! ctx.raw := by grind)
    : Option (VariableState ctx) :=
  match i with
  | 0 => state
  | i + 1 => do
    let result := op.getResult i
    let value := resultValues[i]!
    let newState ← state.setVar? result value
    VariableState.setResultValues?_loop newState op resultValues i

/--
  Set the values of the results of an operation.
-/
def VariableState.setResultValues? (state : VariableState ctx)
    (op : OperationPtr) (resultValues : Array RuntimeValue) (opInBounds : op.InBounds ctx.raw := by grind)
    : Option (VariableState ctx) :=
  VariableState.setResultValues?_loop state op resultValues (op.getNumResults! ctx.raw)

/--
  Set the values of block arguments.
-/
def VariableState.setArgumentValues? (state : VariableState ctx)
    (block : BlockPtr) (values : Array RuntimeValue)
    (blockInBounds : block.InBounds ctx.raw := by grind)
    : Option (VariableState ctx) :=
  let rec loop (state : VariableState ctx) (i : Nat)
      (iInBounds : i ≤ block.getNumArguments! ctx.raw := by grind) :=
    match i with
    | 0 => state
    | i + 1 => do
      let arg := block.getArgument i
      let value := values[i]!
      let newState ← state.setVar? arg value
      loop newState i
  loop state (block.getNumArguments! ctx.raw)

/--
  How the control flow should proceed after interpreting a terminator.
  - `return` indicates that the current block should return with the given values.
  - `branch` indicates that the interpreter should jump to another block
-/
inductive ControlFlowAction where
  | return (vals : Array RuntimeValue)
  | branch (vals : Array RuntimeValue) (dest : BlockPtr)

/--
  Wrapper for interpreter step results: either a successful value `ok` or the
  program has triggered undefined behaviour (`ub`). UB is a property of the
  execution, not of any value, so it lives here rather than inside `RuntimeValue`
  or `LLVM.Int`.
-/
inductive UBOr (α : Type) where
  | ok : α → UBOr α
  | ub : UBOr α
deriving Inhabited

def UBOr.map {α β : Type} (f : α → β) : UBOr α → UBOr β
  | .ok a => .ok (f a)
  | .ub => .ub

/--
  The interpreter monad. `Option (UBOr α)` has three states:
  - `some (.ok x)` — successful execution producing `x`.
  - `some .ub`     — execution triggered undefined behaviour.
  - `none`         — interpreter could not proceed (malformed IR, unsupported op).
-/
def Interp (α : Type) : Type := Option (UBOr α)

def Interp.map {α β : Type} (f : α → β) : Interp α → Interp β :=
  Option.map (UBOr.map f)

instance : Monad Interp where
  pure x := (some (.ok x) : Option (UBOr _))
  bind x f := match (x : Option (UBOr _)) with
    | none => none
    | some .ub => some .ub
    | some (.ok a) => f a

instance : MonadLift Option Interp where
  monadLift
    | none => none
    | some v => some (.ok v)

instance : Inhabited (Interp α) := ⟨(none : Option (UBOr α))⟩

/-- Signal undefined behaviour from inside the interpreter monad. -/
@[inline] def Interp.ub : Interp α := some .ub

/--
  Allocate the given number of bytes of memory.
  Return the updated memory state and the freshly allocated address.
-/
def MemoryState.alloc (state : MemoryState) (size : UInt64)
    : MemoryState × UInt64 :=
  ({ contents := state.contents.extend size.toNat 0 }, state.contents.size.toUInt64)

/--
  Store raw bytes to the given address in memory.
  Yields UB if the access is out of bounds.
-/
def MemoryState.store (state : MemoryState) (addr : UInt64) (val : ByteArray)
    : Interp MemoryState :=
  if addr.toNat != 0 && addr.toNat + val.size <= state.contents.size then
    return { state with contents := val.copySlice 0 state.contents addr.toNat val.size false }
  else
    Interp.ub

/--
  Store a value to memory.
  Yields UB if the access is out of bounds.
-/
def MemoryState.storeValue (state : MemoryState) (addr : UInt64) (val : RuntimeValue)
    : Interp MemoryState :=
  match val with
  | .int 8 (.val v) => state.store addr (ByteArray.empty.push (UInt8.ofBitVec v))
  | .int 64 (.val v) | .reg {val := v} => state.store addr (UInt64.ofBitVec v).toByteArrayLE
  | .int _ .poison => return state
  | .addr v => state.store addr v.toByteArrayLE
  | _ => none

/--
  Load raw bytes from the given memory address.
  Yields UB if the access is out of bounds.
-/
def MemoryState.load (state : MemoryState) (addr size : UInt64)
    : Interp ByteArray :=
  if addr.toNat != 0 && addr.toNat + size.toNat <= state.contents.size then
    return state.contents.extract addr.toNat (addr + size).toNat
  else
    Interp.ub

/--
  Load a value from the given memory address.
  Yields UB if access is out of bounds.
-/
def MemoryState.loadValue (state : MemoryState) (addr : UInt64) (type : TypeAttr)
    : Interp RuntimeValue := do
  match type.val with
  | Attribute.integerType { bitwidth := 8 } =>
      let ba ← state.load addr 1
      return .int 8 (.val ba[0]!.toNat)
  | Attribute.integerType { bitwidth := 64 } =>
      let ba ← state.load addr 8
      return .int 64 (.val (BitVec.ofNat 64 ba.toUInt64LE!.toNat))
  | Attribute.llvmPointerType _ =>
      let ba ← state.load addr 8
      return .addr ba.toUInt64LE!
  | _ => none

/--
  Returns the size of an LLVM type, in bytes.
-/
def sizeOfType (type : Attribute) : Option Nat :=
  match type with
  | .integerType { bitwidth } | .floatType { bitwidth } => some $ (bitwidth + 7) / 8
  | .llvmPointerType _ => some 8
  | .llvmArrayType { size, type } => do
      let inner ← sizeOfType type
      some (inner * size)
  | _ => none


def Arith.interpretOp' (opType : Veir.Arith) (properties : HasDialectOpInfo.propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    : Interp ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .constant => do
    let some resType := resultTypes[0]? | none
    let .integerType bw := resType.val
      | none
    return (#[.int bw.bitwidth
      (.val (BitVec.ofInt bw.bitwidth properties.value.value))], none)
  | .addi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.add lhs rhs properties.nsw properties.nuw)], none)
  | .subi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.sub lhs rhs properties.nsw properties.nuw)], none)
  | .muli => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.mul lhs rhs properties.nsw properties.nuw)], none)
  | .divui => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    -- A poison divisor could refine to 0, so it is immediate UB just like a
    -- concrete-zero divisor.
    match rhs with
    | .poison => Interp.ub
    | .val v' =>
      if v' = 0 then Interp.ub
      else return (#[.int bw (LLVM.Int.udiv lhs rhs properties.exact)], none)
  | .divsi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    match rhs with
    | .poison => Interp.ub
    | .val v' =>
      if v' = 0 then Interp.ub
      else if v' = -1 then
        -- Divisor is concretely -1; if the dividend could be intMin, the
        -- overflow case applies and is UB.
        match lhs with
        | .poison => Interp.ub
        | .val v =>
          if v = BitVec.intMin bw then Interp.ub
          else return (#[.int bw (LLVM.Int.sdiv lhs rhs properties.exact)], none)
      else
        return (#[.int bw (LLVM.Int.sdiv lhs rhs properties.exact)], none)
  | .remui => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    match rhs with
    | .poison => Interp.ub
    | .val v' =>
      if v' = 0 then Interp.ub
      else return (#[.int bw (LLVM.Int.urem lhs rhs)], none)
  | .remsi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    match rhs with
    | .poison => Interp.ub
    | .val v' =>
      if v' = 0 then Interp.ub
      else if v' = -1 then
        match lhs with
        | .poison => Interp.ub
        | .val v =>
          if v = BitVec.intMin bw then Interp.ub
          else return (#[.int bw (LLVM.Int.srem lhs rhs)], none)
      else
        return (#[.int bw (LLVM.Int.srem lhs rhs)], none)
  | .shli => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.shl lhs rhs properties.nsw properties.nuw)], none)
  | .shrsi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.ashr lhs rhs properties.exact)], none)
  | .shrui => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.lshr lhs rhs properties.exact)], none)
  | .andi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.and lhs rhs)], none)
  | .ori => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.or lhs rhs properties.disjoint)], none)
  | .xori => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.xor lhs rhs)], none)
  | .trunci => do
    let [.int w val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth >= w then none else
    return (#[.int resBw.bitwidth (LLVM.Int.trunc val resBw.bitwidth properties.nsw properties.nuw (by omega))], none)
  | .extui => do
    let [.int w val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth <= w then none else
    return (#[.int resBw.bitwidth (LLVM.Int.zext val resBw.bitwidth properties.nneg (by omega))], none)
  | .extsi => do
    let [.int w val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth <= w then none else
    return (#[.int resBw.bitwidth (LLVM.Int.sext val resBw.bitwidth (by omega))], none)
  | .select => do
    let [.int 1 cond, .int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simpa using h)
    return (#[.int bw (LLVM.Int.select cond lhs rhs)], none)
  | _ => none

def Llvm.interpretOp' (opType : Veir.Llvm) (properties : HasDialectOpInfo.propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState)
    : Interp ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .mlir__constant => do
    let some resType := resultTypes[0]? | none
    let .integerType bw := resType.val
      | none
    return (#[.int bw.bitwidth (LLVM.Int.constant bw.bitwidth properties.value.value)], mem, none)
  | .add => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.add lhs rhs properties.nsw properties.nuw)], mem, none)
  | .sub => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.sub lhs rhs properties.nsw properties.nuw)], mem, none)
  | .mul => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.mul lhs rhs properties.nsw properties.nuw)], mem, none)
  | .sdiv => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    match rhs with
    | .poison => Interp.ub
    | .val v' =>
      if v' = 0 then Interp.ub
      else if v' = -1 then
        match lhs with
        | .poison => Interp.ub
        | .val v =>
          if v = BitVec.intMin bw then Interp.ub
          else return (#[.int bw (LLVM.Int.sdiv lhs rhs properties.exact)], mem, none)
      else
        return (#[.int bw (LLVM.Int.sdiv lhs rhs properties.exact)], mem, none)
  | .udiv => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    match rhs with
    | .poison => Interp.ub
    | .val v' =>
      if v' = 0 then Interp.ub
      else return (#[.int bw (LLVM.Int.udiv lhs rhs properties.exact)], mem, none)
  | .srem => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    match rhs with
    | .poison => Interp.ub
    | .val v' =>
      if v' = 0 then Interp.ub
      else if v' = -1 then
        match lhs with
        | .poison => Interp.ub
        | .val v =>
          if v = BitVec.intMin bw then Interp.ub
          else return (#[.int bw (LLVM.Int.srem lhs rhs)], mem, none)
      else
        return (#[.int bw (LLVM.Int.srem lhs rhs)], mem, none)
  | .urem => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    match rhs with
    | .poison => Interp.ub
    | .val v' =>
      if v' = 0 then Interp.ub
      else return (#[.int bw (LLVM.Int.urem lhs rhs)], mem, none)
  | .shl => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.shl lhs rhs properties.nsw properties.nuw)], mem, none)
  | .lshr => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.lshr lhs rhs properties.exact)], mem, none)
  | .ashr => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.ashr lhs rhs properties.exact)], mem, none)
  | .and => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.and lhs rhs)], mem, none)
  | .or => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.or lhs rhs properties.disjoint)], mem, none)
  | .xor => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.xor lhs rhs)], mem, none)
  | .trunc => do
    let [.int w val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth >= w then none else
    return (#[.int resBw.bitwidth (LLVM.Int.trunc val resBw.bitwidth properties.nsw properties.nuw (by omega))], mem, none)
  | .zext => do
    let [.int w val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth <= w then none else
    return (#[.int resBw.bitwidth (LLVM.Int.zext val resBw.bitwidth properties.nneg (by omega))], mem, none)
  | .sext => do
    let [.int w val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth <= w then none else
    return (#[.int resBw.bitwidth (LLVM.Int.sext val resBw.bitwidth (by omega))], mem, none)
  | .icmp => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simpa using h)
    return (#[.int 1 (LLVM.Int.icmp lhs rhs properties.predicate)], mem, none)
  | .select => do
    let [.int 1 cond, .int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simpa using h)
    return (#[.int bw (LLVM.Int.select cond lhs rhs)], mem, none)
  | .return => do
    return (#[], mem, some (.return operands))
  | .br => do
    let [dest] := blockOperands.toList | none
    return (#[], mem, some (.branch operands dest))
  | .cond_br => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some condVal := operands[0]? | none
    let some (trueSizeInt : Int) := properties.operandSegmentSizes.values[1]? | none
    let trueSize := trueSizeInt.toNat
    match condVal with
    | .int 1 (.val cond) =>
      if cond = 1#1 then
        return (#[], mem, some (.branch (operands.extract 1 (trueSize + 1)) destTrue))
      else
        return (#[], mem, some (.branch (operands.extract (trueSize + 1) operands.size) destFalse))
    | .int 1 .poison => Interp.ub
    | _ => none
  | .alloca => do
    let [.int _ (.val count)] := operands.toList | none
    let size ← match properties.elem_type.val with
    | Attribute.integerType { bitwidth := bw } => some (.ok (bw / 8))
    | .llvmPointerType _ => some (.ok 8)
    | _ => none
    let totalSize := (size * count.toNat).toUInt64
    let (mem, addr) := mem.alloc totalSize
    return (#[.addr addr], mem, none)
  | .load => do
    let [.addr addr] := operands.toList | none
    let [type] := resultTypes.toList | none
    let val ← mem.loadValue addr type
    return (#[val], mem, none)
  | .store => do
    let [.addr addr, val] := operands.toList | none
    let mem ← mem.storeValue addr val
    return (#[], mem, none)
  | .getelementptr => do
    /- only supports exactly one dynamic index for now -/
    let [.addr ptr, .int _ idx] := operands.toList | none
    let size ← sizeOfType properties.elem_type.val
    match idx with
    | .val idx => return (#[.addr (ptr.toNat + idx.toNat * size).toUInt64], mem, none)
    | .poison => Interp.ub
  | _ => none

def Riscv.interpretOp' (opType : Veir.Riscv) (properties : HasDialectOpInfo.propertiesOf opType)
    (_resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    : Interp ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .li => do
    let imm := BitVec.ofInt 64 properties.value.value
    return (#[.reg (RISCV.li imm)], none)
  | .lui => do
    let imm := BitVec.ofInt 20 properties.value.value
    return (#[.reg (RISCV.lui imm)], none)
  | .auipc => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 20 properties.value.value
    return (#[.reg (RISCV.auipc imm op)], none)
  | .addi => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.addi imm op)], none)
  | .slti => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.slti imm op)], none)
  | .sltiu => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.sltiu imm op)], none)
  | .andi => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.andi imm op)], none)
  | .ori => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.ori imm op)], none)
  | .xori => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.xori imm op)], none)
  | .addiw => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.addiw imm op)], none)
  | .slli => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.slli imm op)], none)
  | .srli => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.srli imm op)], none)
  | .srai => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.srai imm op)], none)
  | .add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.add op2 op1)], none)
  | .sub => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sub op2 op1)], none)
  | .sll => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sll op2 op1)], none)
  | .slt => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.slt op2 op1)], none)
  | .sltu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sltu op2 op1)], none)
  | .xor => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.xor op2 op1)], none)
  | .srl => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.srl op2 op1)], none)
  | .sra => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sra op2 op1)], none)
  | .or => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.or op2 op1)], none)
  | .and => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.and op2 op1)], none)
  | .slliw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.slliw imm op1)], none)
  | .srliw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.srliw imm op1)], none)
  | .sraiw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.sraiw imm op1)], none)
  | .addw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.addw op2 op1)], none)
  | .subw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.subw op2 op1)], none)
  | .sllw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sllw op2 op1)], none)
  | .srlw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.srlw op2 op1)], none)
  | .sraw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sraw op2 op1)], none)
  | .rem => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.rem op2 op1)], none)
  | .remu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.remu op2 op1)], none)
  | .remw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.remw op2 op1)], none)
  | .remuw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.remuw op2 op1)], none)
  | .mul => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mul op2 op1)], none)
  | .mulh => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulh op2 op1)], none)
  | .mulhu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulhu op2 op1)], none)
  | .mulhsu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulhsu op2 op1)], none)
  | .mulw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulw op2 op1)], none)
  | .div => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.div op2 op1)], none)
  | .divw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.divw op2 op1)], none)
  | .divu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.divu op2 op1)], none)
  | .divuw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.divuw op2 op1)], none)
  | .adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.adduw op2 op1)], none)
  | .sh1adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh1adduw op2 op1)], none)
  | .sh2adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh2adduw op2 op1)], none)
  | .sh3adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh3adduw op2 op1)], none)
  | .sh1add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh1add op2 op1)], none)
  | .sh2add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh2add op2 op1)], none)
  | .sh3add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh3add op2 op1)], none)
  | .slliuw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.slliuw imm op1)], none)
  | .andn => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.andn op2 op1)], none)
  | .orn => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.orn op2 op1)], none)
  | .xnor => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.xnor op2 op1)], none)
  | .max => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.max op2 op1)], none)
  | .maxu => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.maxu op2 op1)], none)
  | .min => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.min op2 op1)], none)
  | .minu => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.minu op2 op1)], none)
  | .rol => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.rol op2 op1)], none)
  | .ror => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.ror op2 op1)], none)
  | .rolw => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.rolw op2 op1)], none)
  | .rorw => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.rorw op2 op1)], none)
  | .sextb => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sextb op)], none)
  | .sexth => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sexth op)], none)
  | .zexth => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.zexth op)], none)
  | .clz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.clz op)], none)
  | .clzw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.clzw op)], none)
  | .ctz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.ctz op)], none)
  | .ctzw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.ctzw op)], none)
  | .cpop => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.cpop op)], none)
  | .cpopw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.cpopw op)], none)
  | .roriw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.roriw imm op1)], none)
  | .rori => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.rori imm op1)], none)
  | .bclr => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.bclr op2 op1)], none)
  | .bext => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.bext op2 op1)], none)
  | .binv => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.binv op2 op1)], none)
  | .bset => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.bset op2 op1)], none)
  | .bclri => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.bclri imm op)], none)
  | .bexti => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.bexti imm op)], none)
  | .binvi => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.binvi imm op)], none)
  | .bseti => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.bseti imm op)], none)
  | .pack => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.pack op2 op1)], none)
  | .packh => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.packh op2 op1)], none)
  | .packw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.packw op2 op1)], none)
  | .mv => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.mv op)], none)
  | .not => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.not op)], none)
  | .neg => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.neg op)], none)
  | .negw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.negw op)], none)
  | .sextw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sextw op)], none)
  | .zextb => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.zextb op)], none)
  | .zextw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.zextw op)], none)
  | .seqz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.seqz op)], none)
  | .snez => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.snez op)], none)
  | .sltz=> do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sltz op)], none)
  | .sgtz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sgtz op)], none)
  | _ => none

def Riscv_Cf.interpretOp' (opType : Veir.Riscv_Cf) (properties : HasDialectOpInfo.propertiesOf opType)
    (_resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    : Interp (Array RuntimeValue × Option ControlFlowAction) :=
  match opType with
  | .branch => do
    let [dest] := blockOperands.toList | none
    return (#[], some (.branch operands dest))
  | .beq => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg lhs) := operands[0]? | none
    let some (RuntimeValue.reg rhs) := operands[1]? | none
    let some trueSize := properties.operandSegmentSizes.values[2]? | none
    let trueSize := trueSize.toNat
    if lhs == rhs then
      return (#[], some (.branch (operands.extract 2 (trueSize + 2)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 2) operands.size) destFalse))
  | .bne => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg lhs) := operands[0]? | none
    let some (RuntimeValue.reg rhs) := operands[1]? | none
    let some trueSize := properties.operandSegmentSizes.values[2]? | none
    let trueSize := trueSize.toNat
    if lhs != rhs then
      return (#[], some (.branch (operands.extract 2 (trueSize + 2)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 2) operands.size) destFalse))

def Cf.interpretOp' (opType : Veir.Cf) (properties : HasDialectOpInfo.propertiesOf opType)
    (_resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    : Interp ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .br => do
    let [dest] := blockOperands.toList | none
    return (#[], some (.branch operands dest))
  | .cond_br => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some condVal := operands[0]? | none
    let some (trueSizeInt : Int) := properties.operandSegmentSizes.values[1]? | none
    let trueSize := trueSizeInt.toNat
    match condVal with
    | .int 1 (.val cond) =>
      if cond = 1#1 then
        return (#[], some (.branch (operands.extract 1 (trueSize + 1)) destTrue))
      else
        return (#[], some (.branch (operands.extract (trueSize + 1) operands.size) destFalse))
    | .int 1 .poison => Interp.ub
    | _ => none

def Comb.interpretOp' (opType : Veir.Comb) (properties : HasDialectOpInfo.propertiesOf opType)
    (operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    : Option ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .add => do
    let l : List _ := operands.toList
    let .int w fst := l[0]! | none
    let some nl := l.mapM (
        fun e => do
          let .int w' val := e | none
          if h : w' ≠ w then none else
          return val.cast (by simpa using h)) | none
    return (#[.int w (Veir.Data.Comb.add nl)], none)
  | _ => none

def HW.interpretOp' (opType : Veir.HW) (properties : HasDialectOpInfo.propertiesOf opType)
    (resultTypes : Array TypeAttr) (_blockOperands : Array BlockPtr)
    : Option ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .constant => do
    let resType ← resultTypes[0]?
    let .integerType bw := resType.val
      | none
    return (#[.int bw.bitwidth
      (.val (Veir.Data.HW.constant (BitVec.ofInt bw.bitwidth properties.value.value)).val)], none)
  | _ => none
/--
  Interpret a single operation given its opcode, type-dependent properties,
  result types, and the runtime values of its operands.
  Return the result runtime values and an optional control flow action indicating how
  to continue the interpretation.
  If any error occurs during interpretation (e.g., unknown operation, missing variable),
  returns `none`.
-/
def interpretOp' (opType : OpCode) (properties : HasOpInfo.propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState)
    : Interp ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .arith arithOp => do
    let (vals, act) ← Arith.interpretOp' arithOp properties resultTypes operands blockOperands
    return (vals, mem, act)
  | .llvm llvmOp => do
    Llvm.interpretOp' llvmOp properties resultTypes operands blockOperands mem
  | .riscv riscvOp => do
    let (vals, act) ← Riscv.interpretOp' riscvOp properties resultTypes operands blockOperands
    return (vals, mem, act)
  | .riscv_cf riscvCfOp => do
    let (vals, act) ← Riscv_Cf.interpretOp' riscvCfOp properties resultTypes operands blockOperands
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
  | .builtin .unrealized_conversion_cast => do
    let some resType := resultTypes[0]? | none
    match resType.val, operands.toList with
    | .registerType _, [.int _bw val] =>
      return (#[.reg (LLVM.Int.toReg val )], mem, none)
    | .integerType _bw, [.reg val] =>
      let .integerType resBw := resType.val | none
      return (#[.int resBw.bitwidth (RISCV.Reg.toInt val resBw.bitwidth)], mem, none)
    | _ , _ => none
  | _ => none

/--
  Interpret a single operation given the current interpreter state.
  Return an updated interpreter state and a control flow action indicating how
  to continue the interpretation.
  If any error occurs during interpretation (e.g., unknown operation, missing variable),
  return `none`.
-/
def interpretOp (op : OperationPtr) {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (inBounds : op.InBounds ctx.raw := by grind)
    : Interp (InterpreterState ctx × Option ControlFlowAction) := do
  let some operands := state.variables.getOperandValues op | none
  let opType := op.getOpType! ctx
  let (resultValues, mem, action) ← interpretOp' opType (op.getProperties! ctx opType)
    (op.getResultTypes! ctx.raw) operands (op.getSuccessors! ctx.raw) state.memory
  let newVars ← state.variables.setResultValues? op resultValues
  let newState := ⟨newVars, mem⟩
  return (newState, action)

/--
  Interpret a list of operations, starting from the given operation pointer.
  Continue to interpret operations until a terminator is encountered,
  or the end of the block is reached.
  Return a ControlFlowAction indicating how to continue the interpretation.
  Return `none` if any errors occur during interpretation.
-/
def interpretOpList (op : OperationPtr) {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (opInBounds : op.InBounds ctx.raw := by grind)
    : Interp (InterpreterState ctx × ControlFlowAction) := do
  let (state, action) ← interpretOp op state
  match action with
  | none =>
    rlet next ← (op.get ctx.raw).next
    interpretOpList next state
  | some action =>
    return (state, action)
termination_by op.idxInParentFromTail ctx.raw
decreasing_by grind

/--
  Interpret a block of operations, starting from the first operation in the block.
  Return the resulting interpreter state and a ControlFlowAction indicating how
  to continue the interpretation.
  Return `none` if any errors occur during interpretation.
-/
def interpretBlock (blockPtr : BlockPtr) {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (blockInBounds : blockPtr.InBounds ctx.raw := by grind) :
    Interp (InterpreterState ctx × ControlFlowAction) := do
  rlet firstOp ← (blockPtr.get ctx.raw).firstOp
  interpretOpList firstOp state

/--
  Interpret a CFG, starting from the given block.
  Return the resulting interpreter state and values eventually returned, if any.
  Return `none` if any errors occur during interpretation.
-/
def interpretBlockCFG (blockPtr : BlockPtr) {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (blockInBounds : blockPtr.InBounds ctx.raw := by grind) :
    Interp (InterpreterState ctx × Array RuntimeValue) := do
  match interpretBlock blockPtr state blockInBounds with
  | some (.ok (state, .return res)) => some (.ok (state, res))
  | some (.ok (state, .branch res succ)) =>
    if h : succ.InBounds ctx.raw then
      rlet newVars ← state.variables.setArgumentValues? succ res
      let state := ⟨newVars, state.memory⟩
      interpretBlockCFG succ state h
    else
      none
  | some .ub => Interp.ub
  | none => none
partial_fixpoint

/--
  Interpret a region, starting from its first block.
  Return the resulting interpreter state and values eventually returned, or `none`
  if any errors occur during interpretation.
-/
def interpretRegion (region : RegionPtr) {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (regionIn : region.InBounds ctx.raw := by grind) :
    Interp (InterpreterState ctx × Array RuntimeValue) := do
  rlet block ← (region.get ctx.raw).firstBlock
  interpretBlockCFG block state

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
    let (_state, results) ← interpretRegion (op.getRegion ctx.raw 0) (InterpreterState.empty ctx)
    return results

end Veir
