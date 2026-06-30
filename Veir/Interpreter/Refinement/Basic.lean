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
`mapping` *reflects* `op'`'s result pointers back to `op`'s if the only **in-scope** value it sends
onto `op'`'s `i`-th result pointer is `op`'s `i`-th result pointer. Paired with the "fixes" equation
`mapping.applyToArray (op.getResults! ..) = op'.getResults! ..`, this says `mapping` matches the two
operations' results index-by-index without mapping any other in-scope value onto them.

The reflection is required only for `val` that **dominate the program point before `op`** — i.e. the
values actually live at `op`'s step. This is exactly the set of values the sole consumer
(`setResultValues?_isRefinedByAt`, via `not_mem_getResults`) ever queries, and the scoping is what
makes op-result *forwarding* sound: a rewrite that redirects `op`'s result onto a result of a
surviving operation `o` (`o` defined before `op`) does *not* break `ReflectsResults o o`, because the
only would-be witness — `op`'s own result mapping onto `o`'s — fails the dominance guard (`op`'s
result cannot dominate `.before o` when `o` is defined before `op`; SSA antisymmetry). -/
def ValueMapping.ReflectsResults {ctx ctx' : WfIRContext OpInfo} (mapping : ValueMapping ctx ctx')
    (op op' : OperationPtr) : Prop :=
  ∀ (val : ValuePtr) (valIn : val.InBounds ctx.raw) (i : Nat),
    val.dominatesIp (InsertPoint.before op) ctx →
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
A *refinement point* selects which values a scoped refinement relation constrains. It is the
position parameter of `isRefinedByAt`, richer than a bare `InsertPoint`:

* `.at p` — the usual scope: the values dominating the program point `p`.
* `.blockEntry b` — the *incoming-edge* scope of a block `b`: the values dominating `b`'s entry,
  **minus** `b`'s own arguments. This is the scope on the pre-argument input state of a block:
  `setArgumentValues?` immediately overwrites `b`'s arguments with fresh (refined) values, so their
  stale incoming values need not be constrained. At a loop back-edge the successor's stale arguments
  cannot be transported from the predecessor's end, so excusing them is what makes the cross-edge
  transport sound.
-/
inductive RefinementPoint where
  | at (p : InsertPoint)
  | blockEntry (b : BlockPtr)

/-- An `InsertPoint` is used as a refinement point via the `.at` scope. -/
instance : Coe InsertPoint RefinementPoint := ⟨.at⟩

/-- The values *in scope* at a refinement point. For `.at p` this is exactly the values dominating
`p`; for `.blockEntry b` it additionally excludes `b`'s own arguments. -/
def RefinementPoint.inScope {OpInfo : Type} [HasOpInfo OpInfo] :
    RefinementPoint → ValuePtr → WfIRContext OpInfo → Prop
  | .at p,         val, ctx => val.dominatesIp p ctx
  | .blockEntry b, val, ctx =>
      val.dominatesIp (InsertPoint.atStart! b ctx.raw) ctx ∧ val ∉ b.getArguments! ctx.raw

/-- `inScope (.at p)` is, definitionally, just domination of `p`. -/
@[simp, grind =]
theorem RefinementPoint.inScope_at {OpInfo : Type} [HasOpInfo OpInfo]
    {p : InsertPoint} {val : ValuePtr} {ctx : WfIRContext OpInfo} :
    RefinementPoint.inScope (.at p) val ctx = val.dominatesIp p ctx := rfl

/-- In-bounds witness carried by `isRefinedByAt` for a refinement point. -/
def RefinementPoint.InBounds : RefinementPoint → IRContext OpInfo → Prop
  | .at p,         ctx => p.InBounds ctx
  | .blockEntry b, ctx => b.InBounds ctx

@[simp, grind =]
theorem RefinementPoint.inBounds_at {p : InsertPoint} {ctx : IRContext OpInfo} :
    (RefinementPoint.at p).InBounds ctx = p.InBounds ctx := rfl

@[simp, grind =]
theorem RefinementPoint.inBounds_blockEntry {b : BlockPtr} {ctx : IRContext OpInfo} :
    (RefinementPoint.blockEntry b).InBounds ctx = b.InBounds ctx := rfl

/--
A variable state `state` is refined by `state'` through the value renaming `mapping`, scoped to
the refinement points `s` (in `ctx`) and `s'` (in `ctx'`). Only values that are *in scope* at both
points are constrained. This excuses stale values that remain in the persistent map from prior
iterations or prior blocks without constraining them; the `.blockEntry` scope additionally excuses
a block's own arguments at its entry.

The relation uses `∀ sv tv` (not `∃ tv`) so existence is delegated to `DefinesDominating`
at the call site, which simplifies proof obligations at maintenance steps.
-/
def VariableState.isRefinedByAt {ctx ctx' : WfIRContext OpInfo}
    (state : VariableState ctx) (state' : VariableState ctx')
    (mapping : ValueMapping ctx ctx') (s : RefinementPoint) (s' : RefinementPoint)
    (_sIn : s.InBounds ctx.raw := by grind) (_s'In : s'.InBounds ctx'.raw := by grind) : Prop :=
  ∀ (val : ValuePtr) (valIn : val.InBounds ctx.raw),
    s.inScope val ctx →
    s'.inScope (mapping ⟨val, valIn⟩).val ctx' →
    ∀ sv tv, state.getVar? val = some sv →
             state'.getVar? (mapping ⟨val, valIn⟩) = some tv → sv ⊒ tv

/--
An interpreter state `state` is refined by `state'` through the value mapping `mapping`, scoped
to source point `s` and target point `s'`: they have the same memory, and the variable state of
`state` is scoped-refined by the variable state of `state'` through `mapping` at `(s, s')`.
-/
def InterpreterState.isRefinedByAt {ctx ctx' : WfIRContext OpInfo}
    (state : InterpreterState ctx) (state' : InterpreterState ctx')
    (mapping : ValueMapping ctx ctx') (s : RefinementPoint) (s' : RefinementPoint)
    (_sIn : s.InBounds ctx.raw := by grind) (_s'In : s'.InBounds ctx'.raw := by grind) : Prop :=
  state.memory = state'.memory ∧
  state.variables.isRefinedByAt state'.variables mapping s s'

/-- Scope-weakening (antitone): `isRefinedByAt` at a *wider* pair of scopes implies it at a
*narrower* pair. If every value in scope at `(t, t')` is in scope at `(s, s')`, the relation
transports from `(s, s')` to `(t, t')`. -/
theorem VariableState.isRefinedByAt.weaken {ctx ctx' : WfIRContext OpInfo}
    {state : VariableState ctx} {state' : VariableState ctx'}
    {mapping : ValueMapping ctx ctx'} {s s' t t' : RefinementPoint}
    {sIn : s.InBounds ctx.raw} {s'In : s'.InBounds ctx'.raw}
    {tIn : t.InBounds ctx.raw} {t'In : t'.InBounds ctx'.raw}
    (h : state.isRefinedByAt state' mapping s s' sIn s'In)
    (hsrc : ∀ (val : ValuePtr), t.inScope val ctx → s.inScope val ctx)
    (htgt : ∀ (val : ValuePtr), t'.inScope val ctx' → s'.inScope val ctx') :
    state.isRefinedByAt state' mapping t t' tIn t'In :=
  fun val valIn hsc htsc sv tv hsv htv =>
    h val valIn (hsrc val hsc) (htgt _ htsc) sv tv hsv htv

/-- Interpreter-state version of `VariableState.isRefinedByAt.weaken`. -/
theorem InterpreterState.isRefinedByAt.weaken {ctx ctx' : WfIRContext OpInfo}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    {mapping : ValueMapping ctx ctx'} {s s' t t' : RefinementPoint}
    {sIn : s.InBounds ctx.raw} {s'In : s'.InBounds ctx'.raw}
    {tIn : t.InBounds ctx.raw} {t'In : t'.InBounds ctx'.raw}
    (h : state.isRefinedByAt state' mapping s s' sIn s'In)
    (hsrc : ∀ (val : ValuePtr), t.inScope val ctx → s.inScope val ctx)
    (htgt : ∀ (val : ValuePtr), t'.inScope val ctx' → s'.inScope val ctx') :
    state.isRefinedByAt state' mapping t t' tIn t'In :=
  ⟨h.1, h.2.weaken hsrc htgt⟩

end Veir
