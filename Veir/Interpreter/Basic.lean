import Veir.IR.Basic
import Veir.Rewriter.Basic
import Veir.ForLean
import Veir.IR.WellFormed
import Veir.Data.Comb.Basic
import Veir.Data.LLVM.Int.Basic
import Veir.Data.LLVM.Byte.Basic
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
| byte (bitwidth : Nat) (value : LLVM.Byte bitwidth)
| float (bitwidth : Nat) (value : Float)
| addr (value : UInt64)
| reg (value : RISCV.Reg)
deriving Inhabited

instance : ToString (RuntimeValue) where
  toString
    | .int _ val => ToString.toString val
    | .byte _ val => ToString.toString val
    | .float _ val => ToString.toString val
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
  | .float bw _, ⟨.floatType floatType, _⟩ => floatType.bitwidth = bw
  | .byte bw _, ⟨.byteType byteType, _⟩ => byteType.bitwidth = bw
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
theorem Conforms.byteType {runtimeValue byteType h} :
    Conforms runtimeValue ⟨.byteType byteType, h⟩ →
    ∃ val, runtimeValue = .byte byteType.bitwidth val := by
  simp only [Conforms]
  cases runtimeValue
  case byte bw val =>
    simp only [byte.injEq, exists_and_left]
    intro _; subst bw
    grind
  all_goals grind

@[grind <=]
theorem Conforms.floatType :
    Conforms runtimeValue ⟨.floatType fltType, h⟩ →
    ∃ val, runtimeValue = .float fltType.bitwidth val := by
  simp only [Conforms]
  cases runtimeValue
  case float bw val =>
    simp only [float.injEq, exists_and_left]
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

def ArrayConforms (source : Array RuntimeValue) (target : Array TypeAttr) : Prop :=
  source.size = target.size ∧ ∀ (i : Nat) (_ : i < source.size), source[i]!.Conforms target[i]!

theorem ArrayConforms.take_succ_eq {source : Array RuntimeValue} {target : Array TypeAttr} :
    source.size = target.size →
    n < source.size →
    (ArrayConforms (source.take (n + 1)) (target.take (n + 1)) ↔
    (ArrayConforms (source.take n) (target.take n) ∧ (source[n]!).Conforms target[n]!)) := by
  simp only [ArrayConforms]
  intro hsize hn
  constructor
  · rintro ⟨_, h⟩
    constructor
    · constructor; grind
      intro i hi
      grind [h i]
    · grind [h n]
  · rintro ⟨⟨_, h⟩, hn⟩
    constructor; grind
    intro i hi
    grind [h i]

end RuntimeValue

/--
  Memory state during interpretation.
  Set bits in the poison mask represent poison bits.
-/
@[ext]
structure MemoryState where
  contents : ByteArray
  poisonMask : ByteArray
  consistentSize : contents.size = poisonMask.size

def MemoryState.empty : MemoryState := {
  contents := (ByteArray.emptyWithCapacity 1024).extend 8 0xff,
  poisonMask := (ByteArray.emptyWithCapacity 1024).extend 8 0xff,
  consistentSize := (by grind)
}

def MemoryState.ensureSize (mem : MemoryState) (size : Nat) : MemoryState :=
  if mem.contents.size < size then
    ⟨mem.contents.extend (size - mem.contents.size) 0,
      mem.poisonMask.extend (size - mem.contents.size) 0xff,
      (by simp [mem.consistentSize])⟩
  else
    mem

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
  (⟨state.contents.extend size.toNat 0,
    state.poisonMask.extend size.toNat 0xff,
    by simp [state.consistentSize]⟩, state.contents.size.toUInt64)

/--
  Store raw bytes to the given address in memory,
  and unset the corresponding poison bits.
  Yields UB if the access is out of bounds.
-/
def MemoryState.store (state : MemoryState) (addr : UInt64) (val : ByteArray)
    : Interp MemoryState :=
  if addr.toNat + val.size ≤ state.contents.size then
    let poison := ByteArray.replicate val.size 0
    return ⟨val.copySlice 0 state.contents addr.toNat val.size false,
      poison.copySlice 0 state.poisonMask addr.toNat val.size false,
      by
        have h : poison.size = val.size := by grind
        simp [ByteArray.copySlice_eq_append, state.consistentSize, h]
      ⟩
  else
    Interp.ub

/--
  Poison the given number n of bytes, starting from the given address in memory.
  Yields UB if the access is out of bounds.
-/
def MemoryState.empoison (state : MemoryState) (addr : UInt64) (n : Nat)
    : Interp MemoryState :=
  if h : addr.toNat + n ≤ state.poisonMask.size then
    let mask := ByteArray.replicate n 0xff
    return ⟨state.contents,
      mask.copySlice 0 state.poisonMask addr.toNat n false,
      by
        have h' : min n mask.size = n := by grind
        have h'' : min addr.toNat state.poisonMask.size = addr.toNat := by grind
        simp [ByteArray.copySlice_eq_append, state.consistentSize, h', h'']
        grind

      ⟩
  else
    Interp.ub

/--
  Store an LLVM value to memory.
  Yields UB if the access is out of bounds or the address is 0.
-/
def MemoryState.storeValue (state : MemoryState) (addr : UInt64) (val : RuntimeValue)
    : Interp MemoryState :=
  if addr.toNat == 0 then Interp.ub else
  match val with
  | .int 8 (.val v) => state.store addr (ByteArray.empty.push (UInt8.ofBitVec v))
  | .int 64 (.val v) => state.store addr (UInt64.ofBitVec v).toByteArrayLE
  | .int n .poison => state.empoison addr (n / 8)
  | .addr v => state.store addr v.toByteArrayLE
  | _ => none

/--
  Load raw bytes from the given memory address.
  Yields UB if the access is out of bounds.
-/
def MemoryState.load (state : MemoryState) (addr size : UInt64)
    : Interp ByteArray :=
  if addr.toNat + size.toNat <= state.contents.size then
    return state.contents.extract addr.toNat (addr + size).toNat
  else
    Interp.ub

/--
  Check if any of the `size` bytes at the given memory address `addr` is poison.
  Yields UB if the access is out of bounds.
-/
def MemoryState.hasPoison (state : MemoryState) (addr size : UInt64)
    : Interp Bool :=
  if addr.toNat + size.toNat <= state.contents.size then do
    let mut poison := false
    for b in state.poisonMask.extract addr.toNat (addr + size).toNat do
      if b ≠ 0 then
        poison := true
        break
    return poison
  else
    Interp.ub

/--
  Load an LLVM value from the given memory address.
  Yields UB if access is out of bounds or the address is 0.
-/
def MemoryState.loadValue (state : MemoryState) (addr : UInt64) (type : TypeAttr)
    : Interp RuntimeValue := do
  if addr == 0 then Interp.ub else
  match type.val with
  | Attribute.integerType { bitwidth := 8 } =>
      let ba ← state.load addr 1
      if ← state.hasPoison addr 1 then return .int 8 .poison
      return .int 8 (.val ba[0]!.toNat)
  | Attribute.integerType { bitwidth := 64 } =>
      let ba ← state.load addr 8
      if ← state.hasPoison addr 8 then return .int 64 .poison
      return .int 64 (.val (BitVec.ofNat 64 ba.toUInt64LE!.toNat))
  | Attribute.llvmPointerType _ =>
      let ba ← state.load addr 8
      -- FIXME poison address
      if ← state.hasPoison addr 8 then return .addr 0
      return .addr ba.toUInt64LE!
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
    return (#[.int bw (LLVM.Int.add lhs rhs properties.attr.nsw properties.attr.nuw)], none)
  | .subi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.sub lhs rhs properties.attr.nsw properties.attr.nuw)], none)
  | .muli => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.mul lhs rhs properties.attr.nsw properties.attr.nuw)], none)
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
    return (#[.int bw (LLVM.Int.shl lhs rhs properties.attr.nsw properties.attr.nuw)], none)
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
    return (#[.int resBw.bitwidth (LLVM.Int.trunc val resBw.bitwidth properties.attr.nsw properties.attr.nuw (by omega))], none)
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
    match properties.value with
    | .integer intAttr =>
      let .integerType bw := resType.val
        | none
      return (#[.int bw.bitwidth (LLVM.Int.constant bw.bitwidth intAttr.value)], mem, none)
    | .float floatAttr =>
      let .floatType bw := resType.val
        | none
      if bw.bitwidth ≠ 64 then
        none
      return (#[.float 64 floatAttr.value], mem, none)
    | .dense denseAttr =>
      none
  | .mlir__poison => do
    let some resType := resultTypes[0]? | none
    let .integerType bw := resType.val | none
    return (#[.int bw.bitwidth (LLVM.Int.mlir_poison bw.bitwidth)], mem, none)
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
  | .intr__fshl => do
    let [.int bw a, .int bw' b, .int bw'' c] := operands.toList | none
    if h: bw' ≠ bw then none else
    if h'': bw'' ≠ bw then none else
    let b := b.cast (by simp at h; exact h)
    let c := c.cast (by simp at h''; exact h'')
    return (#[.int bw (LLVM.Int.fshl a b c)], mem, none)
  | .intr__fshr => do
    let [.int bw a, .int bw' b, .int bw'' c] := operands.toList | none
    if h: bw' ≠ bw then none else
    if h'': bw'' ≠ bw then none else
    let b := b.cast (by simp at h; exact h)
    let c := c.cast (by simp at h''; exact h'')
    return (#[.int bw (LLVM.Int.fshr a b c)], mem, none)
  | .intr__ctlz => do
    let [.int bw x] := operands.toList | none
    return (#[.int bw (LLVM.Int.ctlz x properties.is_zero_poison)], mem, none)
  | .intr__cttz => do
    let [.int bw x] := operands.toList | none
    return (#[.int bw (LLVM.Int.cttz x properties.is_zero_poison)], mem, none)
  | .intr__ctpop => do
    let [.int bw x] := operands.toList | none
    return (#[.int bw (LLVM.Int.ctpop x)], mem, none)
  | .intr__bswap => do
    let [.int bw x] := operands.toList | none
    return (#[.int bw (LLVM.Int.bswap x)], mem, none)
  | .intr__bitreverse => do
    let [.int bw x] := operands.toList | none
    return (#[.int bw (LLVM.Int.bitreverse x)], mem, none)
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
  | .intr__smax => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.smax lhs rhs)], mem, none)
  | .intr__smin => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.smin lhs rhs)], mem, none)
  | .intr__umax => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.umax lhs rhs)], mem, none)
  | .intr__umin => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.umin lhs rhs)], mem, none)
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
  | .unreachable =>
    Interp.ub
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
    let [val, .addr addr] := operands.toList | none
    let mem ← mem.storeValue addr val
    return (#[], mem, none)
  | .getelementptr => do
    /- only supports exactly one dynamic index for now -/
    let [.addr ptr, .int _ idx] := operands.toList | none
    let size ← Attribute.sizeOfType properties.elem_type.val
    match idx with
    | .val idx => return (#[.addr (ptr.toNat + idx.toNat * size).toUInt64], mem, none)
    | .poison => Interp.ub
  | .freeze => do
    let [RuntimeValue.int w val] := operands.toList | none
    return (#[RuntimeValue.int w (LLVM.Int.freeze val)], mem, none)
  | _ => none

/-- Effective address of a RISC-V load/store: the base register value plus the
    sign-extended 12-bit immediate offset. -/
def riscvEffectiveAddr (base : BitVec 64) (offset : Int) : BitVec 64 :=
  base + (BitVec.ofInt 12 offset).signExtend 64

/-- For RISC-V sub-register loads. -/
inductive LoadExtension
  | signExt
  | zeroExt

/-- Interpret the first `bytes` bytes of a little-endian `ByteArray`
    as a `BitVec (8 * bytes)` (byte 0 is the least significant). -/
def _root_.ByteArray.toBitVecLE (ba : ByteArray) (bytes : Nat) : BitVec (8 * bytes) :=
  -- NB ByteArray does not define its own foldr
  ba.toList.foldr (fun b acc => acc <<< 8 ||| b.toBitVec.setWidth (8 * bytes)) 0

/-- Read `bytes` of little-endian data from memory starting at
    `eaddr` and extend it to 64 bits according to `ext`. Memory is
    grown so that the access is in bounds and cannot raise UB. -/
def riscvLoad (mem : MemoryState) (eaddr : BitVec 64) (bytes : Nat) (ext : LoadExtension) :
    Interp (BitVec 64 × MemoryState) := do
  let mem := mem.ensureSize (eaddr.toNat + bytes)
  let ba ← mem.load eaddr.toNat.toUInt64 bytes.toUInt64
  let val := ba.toBitVecLE bytes
  let extended := match ext with
    | .signExt => val.signExtend 64
    | .zeroExt => val.setWidth 64
  return (extended, mem)

def Riscv.interpretOp' (opType : Veir.Riscv) (properties : HasDialectOpInfo.propertiesOf opType)
    (_resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    (mem : MemoryState)
    : Interp ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .li => do
    let imm := BitVec.ofInt 64 properties.value.value
    return (#[.reg (RISCV.li imm)], mem, none)
  | .lui => do
    let imm := BitVec.ofInt 20 properties.value.value
    return (#[.reg (RISCV.lui imm)], mem, none)
  | .auipc => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 20 properties.value.value
    return (#[.reg (RISCV.auipc imm op)], mem, none)
  | .addi => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.addi imm op)], mem, none)
  | .slti => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.slti imm op)], mem, none)
  | .sltiu => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.sltiu imm op)], mem, none)
  | .andi => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.andi imm op)], mem, none)
  | .ori => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.ori imm op)], mem, none)
  | .xori => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.xori imm op)], mem, none)
  | .addiw => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.addiw imm op)], mem, none)
  | .slli => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.slli imm op)], mem, none)
  | .srli => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.srli imm op)], mem, none)
  | .srai => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.srai imm op)], mem, none)
  | .add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.add op2 op1)], mem, none)
  | .sub => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sub op2 op1)], mem, none)
  | .sll => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sll op2 op1)], mem, none)
  | .slt => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.slt op2 op1)], mem, none)
  | .sltu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sltu op2 op1)], mem, none)
  | .xor => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.xor op2 op1)], mem, none)
  | .srl => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.srl op2 op1)], mem, none)
  | .sra => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sra op2 op1)], mem, none)
  | .or => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.or op2 op1)], mem, none)
  | .and => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.and op2 op1)], mem, none)
  | .slliw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.slliw imm op1)], mem, none)
  | .srliw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.srliw imm op1)], mem, none)
  | .sraiw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.sraiw imm op1)], mem, none)
  | .addw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.addw op2 op1)], mem, none)
  | .subw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.subw op2 op1)], mem, none)
  | .sllw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sllw op2 op1)], mem, none)
  | .srlw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.srlw op2 op1)], mem, none)
  | .sraw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sraw op2 op1)], mem, none)
  | .rem => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.rem op2 op1)], mem, none)
  | .remu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.remu op2 op1)], mem, none)
  | .remw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.remw op2 op1)], mem, none)
  | .remuw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.remuw op2 op1)], mem, none)
  | .mul => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mul op2 op1)], mem, none)
  | .mulh => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulh op2 op1)], mem, none)
  | .mulhu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulhu op2 op1)], mem, none)
  | .mulhsu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulhsu op2 op1)], mem, none)
  | .mulw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulw op2 op1)], mem, none)
  | .div => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.div op2 op1)], mem, none)
  | .divw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.divw op2 op1)], mem, none)
  | .divu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.divu op2 op1)], mem, none)
  | .divuw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.divuw op2 op1)], mem, none)
  | .adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.adduw op2 op1)], mem, none)
  | .sh1adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh1adduw op2 op1)], mem, none)
  | .sh2adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh2adduw op2 op1)], mem, none)
  | .sh3adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh3adduw op2 op1)], mem, none)
  | .sh1add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh1add op2 op1)], mem, none)
  | .sh2add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh2add op2 op1)], mem, none)
  | .sh3add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh3add op2 op1)], mem, none)
  | .slliuw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.slliuw imm op1)], mem, none)
  | .andn => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.andn op2 op1)], mem, none)
  | .orn => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.orn op2 op1)], mem, none)
  | .xnor => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.xnor op2 op1)], mem, none)
  | .max => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.max op2 op1)], mem, none)
  | .maxu => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.maxu op2 op1)], mem, none)
  | .min => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.min op2 op1)], mem, none)
  | .minu => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.minu op2 op1)], mem, none)
  | .rol => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.rol op2 op1)], mem, none)
  | .ror => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.ror op2 op1)], mem, none)
  | .rolw => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.rolw op2 op1)], mem, none)
  | .rorw => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.rorw op2 op1)], mem, none)
  | .sextb => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sextb op)], mem, none)
  | .sexth => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sexth op)], mem, none)
  | .zexth => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.zexth op)], mem, none)
  | .clz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.clz op)], mem, none)
  | .clzw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.clzw op)], mem, none)
  | .ctz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.ctz op)], mem, none)
  | .ctzw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.ctzw op)], mem, none)
  | .cpop => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.cpop op)], mem, none)
  | .cpopw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.cpopw op)], mem, none)
  | .orcb => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.orcb op)], mem, none)
  | .rev8 => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.rev8 op)], mem, none)
  | .roriw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.roriw imm op1)], mem, none)
  | .rori => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.rori imm op1)], mem, none)
  | .bclr => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.bclr op2 op1)], mem, none)
  | .bext => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.bext op2 op1)], mem, none)
  | .binv => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.binv op2 op1)], mem, none)
  | .bset => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.bset op2 op1)], mem, none)
  | .bclri => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.bclri imm op)], mem, none)
  | .bexti => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.bexti imm op)], mem, none)
  | .binvi => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.binvi imm op)], mem, none)
  | .bseti => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.bseti imm op)], mem, none)
  | .pack => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.pack op2 op1)], mem, none)
  | .packh => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.packh op2 op1)], mem, none)
  | .packw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.packw op2 op1)], mem, none)
  | .czeroeqz => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.czeroeqz op2 op1)], mem, none)
  | .czeronez => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.czeronez op2 op1)], mem, none)
  | .mv => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.mv op)], mem, none)
  | .not => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.not op)], mem, none)
  | .neg => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.neg op)], mem, none)
  | .negw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.negw op)], mem, none)
  | .sextw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sextw op)], mem, none)
  | .zextb => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.zextb op)], mem, none)
  | .zextw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.zextw op)], mem, none)
  | .seqz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.seqz op)], mem, none)
  | .snez => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.snez op)], mem, none)
  | .sltz=> do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sltz op)], mem, none)
  | .sgtz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sgtz op)], mem, none)
  | .ld => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let (val, mem) ← riscvLoad mem eaddr 8 .zeroExt
    return (#[.reg $ .mk val], mem, none)
  | .lw => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let (val, mem) ← riscvLoad mem eaddr 4 .signExt
    return (#[.reg $ .mk val], mem, none)
  | .lwu => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let (val, mem) ← riscvLoad mem eaddr 4 .zeroExt
    return (#[.reg $ .mk val], mem, none)
  | .lh => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let (val, mem) ← riscvLoad mem eaddr 2 .signExt
    return (#[.reg $ .mk val], mem, none)
  | .lhu => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let (val, mem) ← riscvLoad mem eaddr 2 .zeroExt
    return (#[.reg $ .mk val], mem, none)
  | .lb => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let (val, mem) ← riscvLoad mem eaddr 1 .signExt
    return (#[.reg $ .mk val], mem, none)
  | .lbu => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let (val, mem) ← riscvLoad mem eaddr 1 .zeroExt
    return (#[.reg $ .mk val], mem, none)
  | .sd => do
    let [.reg addr, .reg { val }] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let mem := mem.ensureSize (eaddr.toNat + 8)
    let mem ← mem.store eaddr.toNat.toUInt64 (UInt64.ofBitVec val).toByteArrayLE
    return (#[], mem, none)
  | .sw => do
    let [.reg addr, .reg { val }] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let mem := mem.ensureSize (eaddr.toNat + 4)
    -- store only the low 4 bytes of the register
    let mem ← mem.store eaddr.toNat.toUInt64 ((UInt64.ofBitVec val).toByteArrayLE.extract 0 4)
    return (#[], mem, none)
  | .sh => do
    let [.reg addr, .reg { val }] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let mem := mem.ensureSize (eaddr.toNat + 2)
    -- store only the low 2 bytes of the register
    let mem ← mem.store eaddr.toNat.toUInt64 ((UInt64.ofBitVec val).toByteArrayLE.extract 0 2)
    return (#[], mem, none)
  | .sb => do
    let [.reg addr, .reg { val }] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let mem := mem.ensureSize (eaddr.toNat + 1)
    -- store only the low byte of the register
    let mem ← mem.store eaddr.toNat.toUInt64 ((UInt64.ofBitVec val).toByteArrayLE.extract 0 1)
    return (#[], mem, none)

def Riscv_Stack.interpretOp' (opType : Veir.Riscv_Stack) (properties : HasDialectOpInfo.propertiesOf opType)
    (_resultTypes : Array TypeAttr) (_operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    (mem : MemoryState)
    : Interp ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .alloca => do
    let size ← match properties.value_type.val with
    | Attribute.integerType ⟨bw⟩ => some (.ok (bw / 8))
    | Attribute.llvmPointerType _ => some (.ok 8)
    | _ => none
    let (mem, addr) := mem.alloc size.toUInt64
    return (#[.reg ⟨.ofNat 64 addr.toNat⟩], mem, none)

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
  | .blt => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg lhs) := operands[0]? | none
    let some (RuntimeValue.reg rhs) := operands[1]? | none
    let some trueSize := properties.operandSegmentSizes.values[2]? | none
    let trueSize := trueSize.toNat
    if BitVec.slt lhs.val rhs.val then
      return (#[], some (.branch (operands.extract 2 (trueSize + 2)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 2) operands.size) destFalse))
  | .bge => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg lhs) := operands[0]? | none
    let some (RuntimeValue.reg rhs) := operands[1]? | none
    let some trueSize := properties.operandSegmentSizes.values[2]? | none
    let trueSize := trueSize.toNat
    if !BitVec.slt lhs.val rhs.val then
      return (#[], some (.branch (operands.extract 2 (trueSize + 2)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 2) operands.size) destFalse))
  | .bltu => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg lhs) := operands[0]? | none
    let some (RuntimeValue.reg rhs) := operands[1]? | none
    let some trueSize := properties.operandSegmentSizes.values[2]? | none
    let trueSize := trueSize.toNat
    if BitVec.ult lhs.val rhs.val then
      return (#[], some (.branch (operands.extract 2 (trueSize + 2)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 2) operands.size) destFalse))
  | .bgeu => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg lhs) := operands[0]? | none
    let some (RuntimeValue.reg rhs) := operands[1]? | none
    let some trueSize := properties.operandSegmentSizes.values[2]? | none
    let trueSize := trueSize.toNat
    if !BitVec.ult lhs.val rhs.val then
      return (#[], some (.branch (operands.extract 2 (trueSize + 2)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 2) operands.size) destFalse))
  | .beqz => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg cond) := operands[0]? | none
    let some trueSize := properties.operandSegmentSizes.values[1]? | none
    let trueSize := trueSize.toNat
    if cond.val = 0#64 then
      return (#[], some (.branch (operands.extract 1 (trueSize + 1)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 1) operands.size) destFalse))
  | .bnez => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg cond) := operands[0]? | none
    let some trueSize := properties.operandSegmentSizes.values[1]? | none
    let trueSize := trueSize.toNat
    if cond.val ≠ 0#64 then
      return (#[], some (.branch (operands.extract 1 (trueSize + 1)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 1) operands.size) destFalse))

def Rv64.interpretOp' (opType : Veir.Rv64) (properties : HasDialectOpInfo.propertiesOf opType)
    (resultTypes : Array TypeAttr) (_operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    : Option ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .get_register => do
    let [⟨.registerType reg, _⟩] := resultTypes.toList | none
    if reg.index = some 0 then
      return (#[.reg ⟨0⟩], none)
    else
      none

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

/-- Wrapper around `interpretOp'` that retrieves the operation type, properties,
result types, and successor blocks from the operation pointer. -/
abbrev OperationPtr.interpret (op : OperationPtr) (ctx : IRContext OpCode)
    (operandValues : Array RuntimeValue) (memory : MemoryState) :=
    interpretOp' (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
    (op.getResultTypes! ctx) operandValues (op.getSuccessors! ctx) memory

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
  let (resultValues, mem, action) ← op.interpret ctx operands state.memory
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
  let state := ⟨newVars, state.memory⟩
  rlet firstOp ← (blockPtr.get ctx.raw).firstOp
  interpretOpChain firstOp state

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
  | some (.ok (state, .return res)) => some (.ok (state, res))
  | some (.ok (state, .branch res succ)) =>
    if h : succ.InBounds ctx.raw then
      interpretBlockCFG succ res state h
    else
      none
  | some .ub => Interp.ub
  | none => none
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
  and the current memory state. Return the resulting memory state and the values eventually
  returned.

  Unlike the other interpreter functions, this does not take an `InterpreterState`:
  a function call starts with a fresh, empty variable state, since the caller's SSA
  values are not visible inside the callee.
-/
def interpretFunction (op : OperationPtr) (values : Array RuntimeValue) {ctx : WfIRContext OpCode}
    (mem : MemoryState) (opIn : op.InBounds ctx.raw := by grind) :
    Interp (MemoryState × Array RuntimeValue) := do
  if h : op.getNumRegions ctx.raw ≠ 1 then
    none
  else
    let state : InterpreterState ctx := ⟨.empty ctx, mem⟩
    let (state, results) ← interpretRegion (op.getRegion ctx.raw 0) values state
    return (state.memory, results)

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
