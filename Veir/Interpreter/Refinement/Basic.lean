module

public import Veir.Interpreter.Basic
public import Veir.Interpreter.Memory.Layout
public import Veir.Dominance


public section

/-!
# Refinement of programs

Defines when one program is *refined by* another across two `WfIRContext`s (which lets us
relate a program to a rewritten or lowered version of it). Refinement is defined at three levels:

* `RuntimeValue.isRefinedBy` relates two runtime values: integers refine via the `· ⊒ ·` ordering on
  `LLVM.Int`, while other types of values must match exactly.
* `FunctionOp.isRefinedBy` relates two function-like operations: interpreting the source
  with any arguments and memory is refined by interpreting the target.
  `OperationPtr.isRefinedByAsFunction` states the same for operation pointers.
* `OperationPtr.isRefinedByAsModule` relates two modules: every top-level `func.func` of the source
  module must be refined, as a function, by a same-named top-level `func.func` of the target module.

Additionally, we define a refinement relation between two interpreter states given a mapping of
variables in the source to variables in the target.
-/

open Veir.Data

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] {ctx : WfIRContext OpInfo}

/-!
## Modes

Refinement comes in two modes. In LLVM mode a pointer is refined only by itself:
provenance matters. In assembly mode the target has been lowered to code that
holds pointers in registers, which carry an address and nothing else, so a
pointer is also refined by the wild pointer at its address. That comparison
needs the memory, which the mode carries; the state-level relations below take
it from the state they relate.
-/

/-- The mode a refinement is read in. -/
inductive RefinementMode where
  /-- Pointers compare as pointers. -/
  | llvm
  /-- Pointers compare through their address in `mem`. -/
  | asm (mem : MemoryState)

/-- The mode for a state with memory `mem`, assembly or not. -/
@[expose]
def RefinementMode.of (asm : Bool) (mem : MemoryState) : RefinementMode :=
  if asm then .asm mem else .llvm

@[simp, grind =]
theorem RefinementMode.of_false (mem : MemoryState) : RefinementMode.of false mem = .llvm := rfl

@[simp, grind =]
theorem RefinementMode.of_true (mem : MemoryState) : RefinementMode.of true mem = .asm mem := rfl

/-- What a mode asks of a memory: assembly mode needs the layout. -/
@[expose]
def RefinementMode.Wf (asm : Bool) (mem : MemoryState) : Prop :=
  asm = true → mem.LayoutWf

@[simp, grind =]
theorem RefinementMode.wf_false (mem : MemoryState) : RefinementMode.Wf false mem = True := by
  simp [RefinementMode.Wf]

@[simp, grind =]
theorem RefinementMode.wf_true (mem : MemoryState) :
    RefinementMode.Wf true mem = mem.LayoutWf := by
  simp [RefinementMode.Wf]

/--
`p` names an object of `mem`, and the null object if it is wild. Naming an object
keeps the address meaningful when memory grows. A wild pointer is built at an
address and only ever moved, so its object is the null one, whose base is 0, and
its address is its offset. Nothing the interpreter produces fails this.
-/
@[expose]
def Data.Pointer.ValidIn (mem : MemoryState) (p : Data.Pointer) : Prop :=
  p.object < mem.objects.size ∧ (p.wild = true → p.object = 0)

/--
In assembly mode, a pointer is refined by itself and by the wild pointer at its
address. The pointer has to be valid in the memory.
-/
@[expose]
def Data.Pointer.isRefinedByIn (mem : MemoryState) (p q : Data.Pointer) : Prop :=
  p.ValidIn mem ∧
    (p = q ∨ (p.wild = false ∧ q = Data.Pointer.ofAddress (mem.address p)))

/-- `Data.Pointer.isRefinedByIn`, with poison refined by anything. -/
@[expose]
def Data.LLVM.Ptr.isRefinedByIn (mem : MemoryState) : Data.LLVM.Ptr → Data.LLVM.Ptr → Prop
  | .poison, _ => True
  | .val p, .val q => p.isRefinedByIn mem q
  | .val _, .poison => False

/-- Refinement relation between two runtime values, in LLVM mode unless told otherwise. -/
@[expose]
def RuntimeValue.isRefinedBy (source target : RuntimeValue) (m : RefinementMode := .llvm) : Prop :=
  match source, target with
  | .int bw s, .int bw' t => ∃ h : bw = bw', s.cast h ⊒ t
  | .byte bw s, .byte bw' t => ∃ h : bw = bw', s.cast h ⊒ t
  | .addr s, .addr t =>
    match m with
    | .llvm => s ⊒ t
    | .asm mem => s.isRefinedByIn mem t
  | .reg s, .reg t => s = t
  | .felt fieldType s, .felt fieldType' t => fieldType = fieldType' ∧ s = t
  | .float ty s, .float ty' t =>
      if h : ty = ty' then
        s = h ▸ t
      else
        False
  | _, _ => False

@[inherit_doc] infix:50 " ⊒ " => RuntimeValue.isRefinedBy
@[inherit_doc] notation:50 source:51 " ⊒[" m "] " target:51 => RuntimeValue.isRefinedBy source target m

/--
An array `source` of runtime values is refined by `target`. This asserts that the arrays have
the same size, and that they refine pointwise.
-/
@[expose]
def RuntimeValue.arrayIsRefinedBy (source target : Array RuntimeValue)
    (m : RefinementMode := .llvm) : Prop :=
  source.size = target.size ∧
    ∀ (i : Nat) (_ : i < source.size), source[i]! ⊒[m] target[i]!

@[inherit_doc] infix:50 " ⊒ " => RuntimeValue.arrayIsRefinedBy
@[inherit_doc] notation:50 source:51 " ⊒[" m "] " target:51 =>
  RuntimeValue.arrayIsRefinedBy source target m

/--
Refinement of memory objects, which can involve poison bits being refined into concrete bits.
This should be kept consistent with the definition of refinement on the byte type.
-/
@[expose]
def MemoryObject.isRefinedBy (source target : MemoryObject) : Prop :=
  source.base = target.base ∧
  ∀ addr, source.poisonMask.getD addr 0 ||| ((source.contents.getD addr 0 ^^^ ~~~target.contents.getD addr 0) &&& ~~~target.poisonMask.getD addr 0) = 0xff

@[inherit_doc] infix:50 " ⊒ " => MemoryObject.isRefinedBy

/-- Refinement of memory states: the same objects, each refined bytewise. -/
@[expose]
def MemoryState.isRefinedBy (source target : MemoryState) : Prop :=
  source.objects.size = target.objects.size ∧ ∀ i : Nat, source.objects[i]! ⊒ target.objects[i]!

@[inherit_doc] infix:50 " ⊒ " => MemoryState.isRefinedBy

/--
A function interpretation `source` is refined by `target`. This asserts that the final memories
are equal, and the returned values refine pointwise, in the mode of the final memory.
-/
@[expose]
def FunctionResult.isRefinedBy (source target : MemoryState × Array RuntimeValue)
    (asm : Bool := false) : Prop :=
  source.1 = target.1 ∧ source.2 ⊒[.of asm source.1] target.2

@[inherit_doc] infix:50 " ⊒ " => FunctionResult.isRefinedBy

/--
An interpretation result `source` is refined by `target` given a refinement relation `R`
on the underlying values. This asserts:
* every well-defined outcome `.ok a` of `source` must be matched by an outcome
  `.ok b` of `target` with `R a b`;
* when `source` is undefined behaviour (`.ub`) or failed interpretation (`.fail`), `target`
  is unconstrained
-/
@[expose]
def Interp.isRefinedBy (R : α → β → Prop) (source : Interp α) (target : Interp β) : Prop :=
  match source, target with
  | .ok a, .ok b => R a b
  | .ub _, _ => True
  | .fail _, _ => True
  | _, _ => False

/--
Refinement between two control flow actions: same constructor, equal successor block `dest`, and
the carried value payloads refine pointwise.
-/
@[expose]
def ControlFlowAction.isRefinedBy (source target : ControlFlowAction)
    (m : RefinementMode := .llvm) : Prop :=
  match source, target with
  | .return vals, .return vals' => vals ⊒[m] vals'
  | .branch vals dest, .branch vals' dest' => dest = dest' ∧ vals ⊒[m] vals'
  | _, _ => False

@[inherit_doc] infix:50 " ⊒ " => ControlFlowAction.isRefinedBy

/--
Refinement between two optional control flow actions. They should either both be `none`, or both be
`some` and refine.
-/
@[expose]
def ControlFlowAction.optionIsRefinedBy (source target : Option ControlFlowAction)
    (m : RefinementMode := .llvm) : Prop :=
  match source, target with
  | none, none => True
  | some a, some b => a.isRefinedBy b m
  | _, _ => False

/--
The result of interpreting a single operation. `source` is refined by `target`
when values refine pointwise, memories are equal, and actions refine, all in the
mode of the memory the operation left; in assembly mode that memory keeps its
layout.
-/
@[expose]
def OperationResult.isRefinedBy (source target :
    Array RuntimeValue × MemoryState × Option ControlFlowAction) (asm : Bool := false) : Prop :=
  source.1 ⊒[.of asm source.2.1] target.1 ∧ source.2.1 = target.2.1 ∧
    ControlFlowAction.optionIsRefinedBy source.2.2 target.2.2 (.of asm source.2.1) ∧
    RefinementMode.Wf asm source.2.1

/--
What one step of interpretation leaves, seen from the memory `mem` it started from: a refined
result, and in assembly mode a memory that extends `mem`.
-/
@[expose]
def OperationResult.isRefinedByFrom (mem : MemoryState) (asm : Bool)
    (source target : Array RuntimeValue × MemoryState × Option ControlFlowAction) : Prop :=
  OperationResult.isRefinedBy source target asm ∧ (asm = true → mem.Extends source.2.1)

/--
The function `func₁` (in `ctx₁`) is *refined by* `func₂` (in `ctx₂`) when, for every argument
`values` and initial memory `mem`, interpreting `func₁` is refined by interpreting `func₂`.
-/
@[expose]
def FunctionOp.isRefinedBy {ctx₁ ctx₂ : WfIRContext OpCode} {op₁ op₂ : OperationPtr}
    (func₁ : FunctionOp ctx₁.raw op₁) (func₂ : FunctionOp ctx₂.raw op₂)
    (op₁In : op₁.InBounds ctx₁.raw := by grind)
    (op₂In : op₂.InBounds ctx₂.raw := by grind) (asm : Bool := false) : Prop :=
  ∀ (valuesSource valuesTarget : Array RuntimeValue) (mem : MemoryState),
    RefinementMode.Wf asm mem →
    valuesSource ⊒[.of asm mem] valuesTarget →
    Interp.isRefinedBy (FunctionResult.isRefinedBy · · asm)
      (interpretFunction func₁ valuesSource mem op₁In)
      (interpretFunction func₂ valuesTarget mem op₂In)

/--
The function-like operation `op₁` (in `ctx₁`) is *refined by* the function-like operation `op₂`
(in `ctx₂`) when their `FunctionOp`s are. This does not hold if either is not function-like.
-/
@[expose]
def OperationPtr.isRefinedByAsFunction (op₁ : OperationPtr) (ctx₁ : WfIRContext OpCode)
    (op₂ : OperationPtr) (ctx₂ : WfIRContext OpCode)
    (op₁In : op₁.InBounds ctx₁.raw := by grind)
    (op₂In : op₂.InBounds ctx₂.raw := by grind) (asm : Bool := false) : Prop :=
  match FunctionOp.cast? op₁ ctx₁.raw, FunctionOp.cast? op₂ ctx₂.raw with
  | some func₁, some func₂ => func₁.isRefinedBy func₂ op₁In op₂In asm
  | _, _ => False

/--
`op` is a top-level function of the module operation `moduleOp` (in `ctx`): it is a `func.func`
operation whose parent operation is `moduleOp`.
-/
structure OperationPtr.IsTopLevelFuncWithName (op : OperationPtr) (moduleOp : OperationPtr)
    (ctx : IRContext OpCode) (name : StringAttr) : Prop where
  isFunc : op.getOpType! ctx = .func .func
  hasName : name = (op.getProperties! ctx Func.func).sym_name
  isTopLevel : op.getParentOp! ctx = some moduleOp

/--
The module `mod₁` (in `ctx₁`) is *refined by* the module `mod₂` (in `ctx₂`) when every top-level
`func.func` of `mod₁` is refined, as a function, by a top-level `func.func` of `mod₂` that carries
the same symbol name.

In particular, note that `mod₂` may have extra top-level functions that are not in `mod₁`, but
every function in `mod₁` must be matched by a same-named function in `mod₂` that refines it.
-/
@[expose]
def OperationPtr.isModuleRefinedBy (mod₁ : OperationPtr) (ctx₁ : WfIRContext OpCode)
    (mod₂ : OperationPtr) (ctx₂ : WfIRContext OpCode) (asm : Bool := false) : Prop :=
  ∀ (func₁ : OperationPtr) (func₁In : func₁.InBounds ctx₁.raw) (name : StringAttr),
    func₁.IsTopLevelFuncWithName mod₁ ctx₁.raw name →
      ∃ (func₂ : OperationPtr) (func₂In : func₂.InBounds ctx₂.raw),
        func₂.IsTopLevelFuncWithName mod₂ ctx₂.raw name ∧
          func₁.isRefinedByAsFunction ctx₁ func₂ ctx₂ func₁In func₂In asm

abbrev ValueMapping (ctx ctx' : WfIRContext OpInfo) : Type :=
  {v : ValuePtr // v.InBounds ctx.raw} → {v : ValuePtr // v.InBounds ctx'.raw}

/-- Apply the value mapping to an array of values with separately their bounds information. -/
@[expose]
def ValueMapping.applyToArray {ctx ctx' : WfIRContext OpInfo} (mapping : ValueMapping ctx ctx')
    (vals : Array ValuePtr) (valsIn : ∀ v ∈ vals, v.InBounds ctx.raw := by grind) : Array ValuePtr :=
  vals.attach.map (fun ⟨v, hv⟩ => (mapping ⟨v, valsIn v hv⟩).val)

/--
`mapping` *reflects* `op'`'s result pointers back to `op`'s if the only value it sends onto `op'`'s
`i`-th result pointer is `op`'s `i`-th result pointer. Paired with the "fixes" equation
`mapping.applyToArray (op.getResults! ..) = op'.getResults! ..`, this says `mapping` matches the two
operations' results index-by-index without mapping any other value onto them. -/
def ValueMapping.ReflectsResults {ctx ctx' : WfIRContext OpInfo} (mapping : ValueMapping ctx ctx')
    (op op' : OperationPtr) : Prop :=
  ∀ (val : ValuePtr) (valIn : val.InBounds ctx.raw) (i : Nat),
    (mapping ⟨val, valIn⟩).val = op'.getResult i → val = op.getResult i

/-- An operation `op` in `ctx` is *preserved* and renamed to an operation `op'` in `ctx'` by the
mapping `mapping` if `op` and `op'` have the same type, properties, result types, successors, and
their operands and results are related by `mapping`. Additionally, `mapping` must reflect `op'`'s
results back to `op`'s, so no other value is sent onto `op'`'s results. -/
structure ValueMapping.PreservesOperation {ctx ctx' : WfIRContext OpInfo}
    (mapping : ValueMapping ctx ctx') (op op' : OperationPtr)
    (opIn : op.InBounds ctx.raw := by grind)
    (opIn' : op'.InBounds ctx'.raw := by grind) : Prop where
  opType : op'.getOpType! ctx'.raw = op.getOpType! ctx.raw
  props : op'.getProperties! ctx'.raw (op'.getOpType! ctx'.raw) =
            opType ▸ op.getProperties! ctx.raw (op.getOpType! ctx.raw)
  resultTypes : op'.getResultTypes! ctx'.raw = op.getResultTypes! ctx.raw
  successors : op'.getSuccessors! ctx'.raw = op.getSuccessors! ctx.raw
  operands : op'.getOperands! ctx'.raw = mapping.applyToArray (op.getOperands! ctx.raw)
  results : op'.getResults! ctx'.raw = mapping.applyToArray (op.getResults! ctx.raw) (by grind)
  reflect : mapping.ReflectsResults op op'

/--
A variable state `state` is refined by `state'` through the value renaming `mapping`: every
variable defined in `state` is, after renaming through `mapping`, also defined in `state'` with a
value that refines the source value.
-/
@[expose]
def VariableState.isRefinedBy {ctx ctx' : WfIRContext OpInfo}
    (state : VariableState ctx) (state' : VariableState ctx')
    (mapping : ValueMapping ctx ctx') (m : RefinementMode := .llvm) : Prop :=
  ∀ (val : ValuePtr) (valIn : val.InBounds ctx.raw),
  ∀ sourceVar, state.getVar? val = some sourceVar →
  ∃ targetVar, state'.getVar? (mapping ⟨val, valIn⟩) = some targetVar ∧
  sourceVar ⊒[m] targetVar

/--
An interpreter state `state` is refined by `state'` through the value mapping
`mapping`: they have the same memory, and the variable state of `state` is refined by the variable
state of `state'` through `mapping`, in the mode of that memory. In assembly
mode the memory keeps its layout.
-/
@[expose]
def InterpreterState.isRefinedBy {ctx ctx' : WfIRContext OpInfo}
    (state : InterpreterState ctx) (state' : InterpreterState ctx')
    (mapping : ValueMapping ctx ctx') (asm : Bool := false) : Prop :=
  state.memory = state'.memory ∧
  state.variables.isRefinedBy state'.variables mapping (.of asm state.memory) ∧
  RefinementMode.Wf asm state.memory

/-!
## `InterpreterState.IsRefinedByAt`

The `isRefinedByAt` family relates two interpreter states (a *source* `state` and a *target*
`state'`), asserting that `state'` refines `state`. Each value in scope defined in `state` is,
after renaming through the `mapping`, also defined in `state'` with a value that refines the
source value. Importantly, it does not constrain *every* defined value. It is parameterised by a
pair of `RefinementPoint`s `(s, s')` and only constrains values that are *in scope* at both
points.

This scoping is what makes the relation usable in practice, as the variable state carries
stale values (blocks that are not dominating the current location such as prior iterations of a
loop).
-/

/--
A *refinement point* provides a location for a refinement relation.

It is either:
* `.at p`, an `InsertPoint` in a program, which is either a location just before an operation, or
  at the end of a block; or
* `.blockEntry b`, a `BlockPtr` entry, just before the block's arguments. It represents the
  location where the control flow has just entered the block, but before the block's arguments have
  been set.
-/
inductive RefinementPoint where
  | at (p : InsertPoint)
  | blockEntry (b : BlockPtr)

instance : Coe InsertPoint RefinementPoint := ⟨.at⟩

def RefinementPoint.InBounds (point : RefinementPoint) (ctx : IRContext OpInfo) : Prop :=
  match point with
  | .at p => p.InBounds ctx
  | .blockEntry b => b.InBounds ctx

@[simp, grind =]
theorem RefinementPoint.inBounds_at {p : InsertPoint} {ctx : IRContext OpInfo} :
    (RefinementPoint.at p).InBounds ctx = p.InBounds ctx := by
  simp [RefinementPoint.InBounds]

@[simp, grind =]
theorem RefinementPoint.inBounds_blockEntry {b : BlockPtr} {ctx : IRContext OpInfo} :
    (RefinementPoint.blockEntry b).InBounds ctx = b.InBounds ctx := by
  simp [RefinementPoint.InBounds]

/-- Whether `value` is *in scope* at a refinement point. For `.at p` this holds exactly when the
value dominates `p`; for `.blockEntry b` it must dominate the block entry and not be one of `b`'s
own arguments. -/
def ValuePtr.InScopeAt (value : ValuePtr) (point : RefinementPoint) (ctx : WfIRContext OpInfo) :
    Prop :=
  match point with
  | .at p => value.dominatesIp p ctx
  | .blockEntry b =>
    value.dominatesIp (InsertPoint.atStart! b ctx.raw) ctx ∧ value ∉ b.getArguments! ctx.raw

@[simp, grind =]
theorem ValuePtr.inScopeAt_at :
    ValuePtr.InScopeAt val (.at p) ctx = val.dominatesIp p ctx := by
  simp [ValuePtr.InScopeAt]

@[simp, grind =]
theorem ValuePtr.inScopeAt_blockEntry :
    ValuePtr.InScopeAt val (.blockEntry b) ctx =
      (val.dominatesIp (InsertPoint.atStart! b ctx.raw) ctx
      ∧ val ∉ b.getArguments! ctx.raw) := by
  simp [ValuePtr.InScopeAt]

/--
A refinement relation for variable states in two different contexts at different locations.
This asserts that every value in `state` and in scope, that is mapped to a value in `state'` and
in scope, have refining runtime values.
-/
def VariableState.isRefinedByAt {ctx ctx' : WfIRContext OpInfo}
    (state : VariableState ctx) (state' : VariableState ctx')
    (mapping : ValueMapping ctx ctx') (s : RefinementPoint) (s' : RefinementPoint)
    (_sIn : s.InBounds ctx.raw := by grind) (_s'In : s'.InBounds ctx'.raw := by grind)
    (m : RefinementMode := .llvm) : Prop :=
  ∀ (val : ValuePtr) (valIn : val.InBounds ctx.raw),
  val.InScopeAt s ctx →
  (mapping ⟨val, valIn⟩).val.InScopeAt s' ctx' →
  ∀ sv, state.getVar? val = some sv →
  ∀ tv, state'.getVar? (mapping ⟨val, valIn⟩) = some tv →
  sv ⊒[m] tv

/--
A refinement relation for intepreter states in two different locations.
This asserts that memory is equal, and that the variable states are refined at the given points.
-/
def InterpreterState.isRefinedByAt {ctx ctx' : WfIRContext OpInfo}
    (state : InterpreterState ctx) (state' : InterpreterState ctx')
    (mapping : ValueMapping ctx ctx') (s : RefinementPoint) (s' : RefinementPoint)
    (_sIn : s.InBounds ctx.raw := by grind) (_s'In : s'.InBounds ctx'.raw := by grind)
    (asm : Bool := false) : Prop :=
  state.memory = state'.memory ∧
  state.variables.isRefinedByAt state'.variables mapping s s' _sIn _s'In (.of asm state.memory) ∧
  RefinementMode.Wf asm state.memory

end Veir
