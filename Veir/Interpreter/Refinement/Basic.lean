import Veir.Interpreter.Basic
import Veir.Data.Refinement

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
-/

open Veir.Data

namespace Veir

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
* when `source` is undefined behaviour (`some .ub`), `target` must succeed (i.e. not be `none`),
  but may be either `some .ub` or `some (.ok _)`;
* when `source` or `target` failed interpretation (i.e. are `none`), no refinement exists.
-/
def Interp.isRefinedBy (R : α → α → Prop) (source target : Interp α) : Prop :=
  match source, target with
  | some (.ok a), some (.ok b) => R a b
  | some .ub, some _ => True
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

end Veir
