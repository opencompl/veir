import Veir.Interpreter.Basic
import Veir.Data.Refinement
import Veir.Dominance

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

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- Refinement relation between two runtime values. -/
def RuntimeValue.isRefinedBy (source target : RuntimeValue) : Prop :=
  match source, target with
  | .int bw s, .int bw' t => ∃ h : bw = bw', s.cast h ⊒ t
  | .addr s, .addr t => s = t
  | .reg s, .reg t => s = t
  | .float bw s, .float bw' t => bw = bw' ∧ s = t
  | _, _ => False

@[inherit_doc] infix:50 " ⊒ " => RuntimeValue.isRefinedBy

/--
An array `source` of runtime values is refined by `target`. This asserts that the arrays have
the same size, and that they refine pointwise.
-/
def RuntimeValue.arrayIsRefinedBy (source target : Array RuntimeValue) : Prop :=
  source.size = target.size ∧
    ∀ (i : Nat) (_ : i < source.size), source[i]! ⊒ target[i]!

@[inherit_doc] infix:50 " ⊒ " => RuntimeValue.arrayIsRefinedBy

/--
A function interpretation `source` is refined by `target`. This asserts that the final memories
are equal, and the returned values refine pointwise.
-/
def FunctionResult.isRefinedBy (source target : MemoryState × Array RuntimeValue) : Prop :=
  source.1 = target.1 ∧ source.2 ⊒ target.2

@[inherit_doc] infix:50 " ⊒ " => FunctionResult.isRefinedBy

/--
An interpretation result `source` is refined by `target` given a refinement relation `R`
on the underlying values. This asserts:
* every well-defined outcome `some (.ok a)` of `source` must be matched by an outcome
  `some (.ok b)` of `target` with `R a b`;
* when `source` is undefined behaviour (`some .ub`) or failed interpretation (`none`), `target`
  is unconstrained
-/
def Interp.isRefinedBy (R : α → β → Prop) (source : Interp α) (target : Interp β) : Prop :=
  match source, target with
  | some (.ok a), some (.ok b) => R a b
  | some .ub, _ => True
  | none, _ => True
  | _, _ => False

/--
Refinement between two control flow actions: same constructor, equal successor block `dest`, and
the carried value payloads refine pointwise.
-/
def ControlFlowAction.isRefinedBy : ControlFlowAction → ControlFlowAction → Prop
  | .return vals, .return vals' => vals ⊒ vals'
  | .branch vals dest, .branch vals' dest' => dest = dest' ∧ vals ⊒ vals'
  | _, _ => False

@[inherit_doc] infix:50 " ⊒ " => ControlFlowAction.isRefinedBy

/--
Refinement between two optional control flow actions. They should either both be `none`, or both be
`some` and refine.
-/
def ControlFlowAction.optionIsRefinedBy : Option ControlFlowAction → Option ControlFlowAction → Prop
  | none, none => True
  | some a, some b => a.isRefinedBy b
  | _, _ => False

/--
The function described by source `op₁` (in `ctx₁`) is *refined by* target `op₂` (in `ctx₂`) when,
for every argument `values` and initial memory `mem`, interpreting `op₁` is refined by interpreting
`op₂`.
-/
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
The symbol name (`sym_name`) of `op` when it is a `func.func` operation, and `none` otherwise.
Used to match a source function against a target function carrying the same name.
-/
def OperationPtr.funcSymName? (op : OperationPtr) (ctx : IRContext OpCode) : Option StringAttr :=
  let opType := op.getOpType! ctx
  match opType, (op.getProperties! ctx opType) with
    | .llvm .func, props => props.sym_name
    | _, _ => none

/--
`op` is a top-level function of the module operation `moduleOp` (in `ctx`): it is a `func.func`
operation whose parent operation is `moduleOp`.
-/
structure OperationPtr.IsTopLevelFuncWithName (op : OperationPtr) (moduleOp : OperationPtr)
    (ctx : IRContext OpCode) (name : StringAttr) : Prop where
  isFunc : op.getOpType! ctx = .func .func
  hasName : name = (op.getProperties! ctx (.func .func)).sym_name
  isTopLevel : op.getParentOp! ctx = some moduleOp

/--
The module `mod₁` (in `ctx₁`) is *refined by* the module `mod₂` (in `ctx₂`) when every top-level
`func.func` of `mod₁` is refined, as a function, by a top-level `func.func` of `mod₂` that carries
the same symbol name.

In particular, note that `mod₂` may have extra top-level functions that are not in `mod₁`, but
every function in `mod₁` must be matched by a same-named function in `mod₂` that refines it.
-/
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
def InterpreterState.isRefinedBy {ctx ctx' : WfIRContext OpInfo}
    (state : InterpreterState ctx) (state' : InterpreterState ctx')
    (mapping : ValueMapping ctx ctx') : Prop :=
  state.memory = state'.memory ∧
  state.variables.isRefinedBy state'.variables mapping

/--
A variable state `state` is refined by `state'` through the value renaming `mapping`, scoped to
the program points `p` (in `ctx`) and `p'` (in `ctx'`). Only values that are *in scope* at both
points are constrained: a source value `val` must dominate `p`, and its image `mapping val` must
dominate `p'`. This excuses stale values that remain in the persistent map from prior iterations
or prior blocks without constraining them.

The relation uses `∀ sv tv` (not `∃ tv`) so existence is delegated to `DefinesDominating`
at the call site, which simplifies proof obligations at maintenance steps.
-/
def VariableState.isRefinedByAt {ctx ctx' : WfIRContext OpInfo}
    (state : VariableState ctx) (state' : VariableState ctx')
    (mapping : ValueMapping ctx ctx') (p : InsertPoint) (p' : InsertPoint)
    (_pIn : p.InBounds ctx.raw := by grind) (_p'In : p'.InBounds ctx'.raw := by grind) : Prop :=
  ∀ (val : ValuePtr) (valIn : val.InBounds ctx.raw),
    val.dominatesIp p ctx →
    (mapping ⟨val, valIn⟩).val.dominatesIp p' ctx' →
    ∀ sv tv, state.getVar? val = some sv →
             state'.getVar? (mapping ⟨val, valIn⟩) = some tv → sv ⊒ tv

/--
An interpreter state `state` is refined by `state'` through the value mapping `mapping`, scoped
to source point `p` and target point `p'`: they have the same memory, and the variable state of
`state` is scoped-refined by the variable state of `state'` through `mapping` at `(p, p')`.
-/
def InterpreterState.isRefinedByAt {ctx ctx' : WfIRContext OpInfo}
    (state : InterpreterState ctx) (state' : InterpreterState ctx')
    (mapping : ValueMapping ctx ctx') (p : InsertPoint) (p' : InsertPoint)
    (_pIn : p.InBounds ctx.raw := by grind) (_p'In : p'.InBounds ctx'.raw := by grind) : Prop :=
  state.memory = state'.memory ∧
  state.variables.isRefinedByAt state'.variables mapping p p'

end Veir
