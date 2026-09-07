module

public import Veir.Interpreter.Basic
public import Veir.Dominance


public section

/-!
# Refinement of programs

Defines when one program is *refined by* another across two `WfIRContext`s (which lets us
relate a program to a rewritten or lowered version of it). Refinement is defined at three levels:

* `RuntimeValue.isRefinedBy` relates two runtime values: integers refine via the `· ⊒ ·` ordering on
  `LLVM.Int`, while other types of values must match exactly.
* `OperationPtr.isRefinedByAsFunction` relates two function-like operations: interpreting the source
  with any arguments and memory is refined by interpreting the target.
* `OperationPtr.isRefinedByAsModule` relates two modules: every top-level `func.func` of the source
  module must be refined, as a function, by a same-named top-level `func.func` of the target module.

Additionally, we define a refinement relation between two interpreter states given a mapping of
variables in the source to variables in the target.
-/

open Veir.Data

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] {ctx : WfIRContext OpInfo}

/-- Refinement relation between two runtime values. -/
@[expose]
def RuntimeValue.isRefinedBy (source target : RuntimeValue) : Prop :=
  match source, target with
  | .int bw s, .int bw' t => ∃ h : bw = bw', s.cast h ⊒ t
  | .byte bw s, .byte bw' t => ∃ h : bw = bw', s.cast h ⊒ t
  | .addr s, .addr t => s = t
  | .reg s, .reg t => s = t
  | .felt fieldType s, .felt fieldType' t => fieldType = fieldType' ∧ s = t
  | .float ty s, .float ty' t =>
      if h : ty = ty' then
        s = h ▸ t
      else
        False
  | _, _ => False

@[inherit_doc] infix:50 " ⊒ " => RuntimeValue.isRefinedBy

/--
An array `source` of runtime values is refined by `target`. This asserts that the arrays have
the same size, and that they refine pointwise.
-/
@[expose]
def RuntimeValue.arrayIsRefinedBy (source target : Array RuntimeValue) : Prop :=
  source.size = target.size ∧
    ∀ (i : Nat) (_ : i < source.size), source[i]! ⊒ target[i]!

@[inherit_doc] infix:50 " ⊒ " => RuntimeValue.arrayIsRefinedBy

/--
Refinement of memory states, which can involve poison bits being refined into concrete bits.
This should be kept consistent with the definition of refinement on the byte type.
-/
@[expose]
def MemoryState.isRefinedBy (source target : MemoryState) : Prop :=
  ∀ addr, source.poisonMask.getD addr 0 ||| ((source.contents.getD addr 0 ^^^ ~~~target.contents.getD addr 0) &&& ~~~target.poisonMask.getD addr 0) = 0xff

@[inherit_doc] infix:50 " ⊒ " => MemoryState.isRefinedBy

/--
A function interpretation `source` is refined by `target`. This asserts that the final memories
are equal, and the returned values refine pointwise.
-/
@[expose]
def FunctionResult.isRefinedBy (source target : MemoryState × Array RuntimeValue) : Prop :=
  source.1 = target.1 ∧ source.2 ⊒ target.2

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
  | .ub, _ => True
  | .fail, _ => True
  | _, _ => False

/--
Refinement between two control flow actions: same constructor, equal successor block `dest`, and
the carried value payloads refine pointwise.
-/
@[expose]
def ControlFlowAction.isRefinedBy : ControlFlowAction → ControlFlowAction → Prop
  | .return vals, .return vals' => vals ⊒ vals'
  | .branch vals dest, .branch vals' dest' => dest = dest' ∧ vals ⊒ vals'
  | _, _ => False

@[inherit_doc] infix:50 " ⊒ " => ControlFlowAction.isRefinedBy

/--
Refinement between two optional control flow actions. They should either both be `none`, or both be
`some` and refine.
-/
@[expose]
def ControlFlowAction.optionIsRefinedBy : Option ControlFlowAction → Option ControlFlowAction → Prop
  | none, none => True
  | some a, some b => a.isRefinedBy b
  | _, _ => False

/--
The function described by source `op₁` (in `ctx₁`) is *refined by* target `op₂` (in `ctx₂`) when,
for every argument `values` and initial memory `mem`, interpreting `op₁` is refined by interpreting
`op₂`.
-/
@[expose]
def OperationPtr.isRefinedByAsFunction (op₁ : OperationPtr) (ctx₁ : WfIRContext OpCode)
    (op₂ : OperationPtr) (ctx₂ : WfIRContext OpCode)
    (op₁In : op₁.InBounds ctx₁.raw := by grind)
    (op₂In : op₂.InBounds ctx₂.raw := by grind) : Prop :=
  ∀ (valuesSource valuesTarget : Array RuntimeValue) (mem : MemoryState),
    valuesSource ⊒ valuesTarget →
    Interp.isRefinedBy FunctionResult.isRefinedBy
      (interpretFunction op₁ valuesSource mem (ctx := ctx₁) op₁In)
      (interpretFunction op₂ valuesTarget mem (ctx := ctx₂) op₂In)

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
    (mod₂ : OperationPtr) (ctx₂ : WfIRContext OpCode) : Prop :=
  ∀ (func₁ : OperationPtr) (func₁In : func₁.InBounds ctx₁.raw) (name : StringAttr),
    func₁.IsTopLevelFuncWithName mod₁ ctx₁.raw name →
      ∃ (func₂ : OperationPtr) (func₂In : func₂.InBounds ctx₂.raw),
        func₂.IsTopLevelFuncWithName mod₂ ctx₂.raw name ∧
          func₁.isRefinedByAsFunction ctx₁ func₂ ctx₂ func₁In func₂In

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
    (mapping : ValueMapping ctx ctx') : Prop :=
  ∀ (val : ValuePtr) (valIn : val.InBounds ctx.raw),
  ∀ sourceVar, state.getVar? val = some sourceVar →
  ∃ targetVar, state'.getVar? (mapping ⟨val, valIn⟩) = some targetVar ∧
  sourceVar ⊒ targetVar

/--
An interpreter state `state` is refined by `state'` through the value mapping
`mapping`: they have the same memory, and the variable state of `state` is refined by the variable
state of `state'` through `mapping`.
-/
@[expose]
def InterpreterState.isRefinedBy {ctx ctx' : WfIRContext OpInfo}
    (state : InterpreterState ctx) (state' : InterpreterState ctx')
    (mapping : ValueMapping ctx ctx') : Prop :=
  state.memory = state'.memory ∧
  state.variables.isRefinedBy state'.variables mapping

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
    (_sIn : s.InBounds ctx.raw := by grind) (_s'In : s'.InBounds ctx'.raw := by grind) : Prop :=
  ∀ (val : ValuePtr) (valIn : val.InBounds ctx.raw),
  val.InScopeAt s ctx →
  (mapping ⟨val, valIn⟩).val.InScopeAt s' ctx' →
  ∀ sv, state.getVar? val = some sv →
  ∀ tv, state'.getVar? (mapping ⟨val, valIn⟩) = some tv →
  sv ⊒ tv

/--
A refinement relation for intepreter states in two different locations.
This asserts that memory is equal, and that the variable states are refined at the given points.
-/
def InterpreterState.isRefinedByAt {ctx ctx' : WfIRContext OpInfo}
    (state : InterpreterState ctx) (state' : InterpreterState ctx')
    (mapping : ValueMapping ctx ctx') (s : RefinementPoint) (s' : RefinementPoint)
    (_sIn : s.InBounds ctx.raw := by grind) (_s'In : s'.InBounds ctx'.raw := by grind) : Prop :=
  state.memory = state'.memory ∧
  state.variables.isRefinedByAt state'.variables mapping s s'

end Veir
