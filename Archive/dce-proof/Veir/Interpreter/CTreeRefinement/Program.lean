module

public import Veir.Interpreter.CTreeInterpreter
public import Veir.Interpreter.CTreeRefinement

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.VariableState

public section

/-!
# Whole-program refinement with CTree semantics

`Veir.Tree.Refinement` mirrors the function and module relations from
`Veir.Interpreter.Refinement`, using `Tree.Refines` and hence `CTree.Sim`.
Arguments may refine pointwise, the initial memory is shared, and successful results
must have refining final memories and pointwise-refining return values. Final memories
have the same allocation metadata and globals, with pointwise-refining bytes. Every target
choice must be matched by a source choice. Source UB and interpreter failure are
handled by `Tree.Refines` using the existing `Interp.isRefinedBy` convention.

`OperationPtr.isModuleRefinedBy` is the whole-program relation: every top-level
`func.func` in the source must have a same-named refining function in the target.
The target may contain additional functions. A whole-module pass can state its
correctness using this relation between its input and output contexts and module pointers.

The namespace keeps these relations distinct from the outcome-monad versions. For
example, write `Tree.Refinement.OperationPtr.isModuleRefinedBy source sourceCtx
target targetCtx` in a pass correctness theorem. No termination assumption is made.
-/

namespace Veir.CTree

/-- The memory-aware implementation preserves the original empty-memory function API. -/
theorem interpretFunction_eq_body (op : OperationPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (opIn : op.InBounds ctx.raw := by grind) :
    interpretFunction op values opIn = (do
      let some funcOp := FunctionOp.of? op ctx.raw | fail
      if h : op.getNumRegions ctx.raw ≠ 1 then
        fail
      else
        let (_, results) ← interpretRegion funcOp.getFunctionBody values (.empty ctx)
        return results) := by
  cases hfunc : FunctionOp.of? op ctx.raw with
  | none => simp [interpretFunction, hfunc]
  | some funcOp =>
    simp only [interpretFunction, hfunc, interpretFunctionWithMemory]
    split
    · simp [Bind.bind]
    · simp [InterpreterState.empty]

end Veir.CTree

namespace Veir.Tree.Refinement

/--
Memory refinement for CTree programs: allocated objects and the global-symbol table
are unchanged, while each source byte may contain more poison than its target byte.
-/
@[expose]
def MemoryState.isRefinedBy (source target : Veir.MemoryState) : Prop :=
  Veir.MemoryState.isRefinedBy source target ∧ source.globals = target.globals

@[simp]
theorem MemoryState.isRefinedBy_refl (mem : Veir.MemoryState) : isRefinedBy mem mem :=
  ⟨Veir.MemoryState.isRefinedBy_refl mem, rfl⟩

theorem MemoryState.isRefinedBy_trans {mem₁ mem₂ mem₃ : Veir.MemoryState}
    (h₁₂ : isRefinedBy mem₁ mem₂) (h₂₃ : isRefinedBy mem₂ mem₃) : isRefinedBy mem₁ mem₃ :=
  ⟨Veir.MemoryState.isRefinedBy_trans h₁₂.1 h₂₃.1, h₁₂.2.trans h₂₃.2⟩

/-- Function results refine in both their final memory and their returned values. -/
@[expose]
def FunctionResult.isRefinedBy
    (source target : Veir.MemoryState × Array RuntimeValue) : Prop :=
  MemoryState.isRefinedBy source.1 target.1 ∧ RuntimeValue.arrayIsRefinedBy source.2 target.2

@[simp]
theorem FunctionResult.isRefinedBy_refl (result : Veir.MemoryState × Array RuntimeValue) :
    isRefinedBy result result :=
  ⟨MemoryState.isRefinedBy_refl _, RuntimeValue.arrayIsRefinedBy_refl _⟩

theorem FunctionResult.isRefinedBy_trans {result₁ result₂ result₃ :
    Veir.MemoryState × Array RuntimeValue}
    (h₁₂ : isRefinedBy result₁ result₂) (h₂₃ : isRefinedBy result₂ result₃) :
    isRefinedBy result₁ result₃ :=
  ⟨MemoryState.isRefinedBy_trans h₁₂.1 h₂₃.1,
    RuntimeValue.arrayIsRefinedBy_trans h₁₂.2 h₂₃.2⟩

/-- Operation results refine in their values, memory, and optional control-flow action. -/
@[expose]
def OperationResult.isRefinedBy (source target :
    Array RuntimeValue × Veir.MemoryState × Option ControlFlowAction) : Prop :=
  RuntimeValue.arrayIsRefinedBy source.1 target.1 ∧
    MemoryState.isRefinedBy source.2.1 target.2.1 ∧
      ControlFlowAction.optionIsRefinedBy source.2.2 target.2.2

@[simp]
theorem OperationResult.isRefinedBy_refl (result :
    Array RuntimeValue × Veir.MemoryState × Option ControlFlowAction) :
    isRefinedBy result result :=
  ⟨RuntimeValue.arrayIsRefinedBy_refl _, MemoryState.isRefinedBy_refl _,
    ControlFlowAction.optionIsRefinedBy_refl _⟩

/--
CTree refinement of function-like operations in potentially different contexts.
For every pair of related arguments and every common initial memory, the target
function's behaviors are simulated by the source function's behaviors, with
`FunctionResult.isRefinedBy` relating successful results.
-/
@[expose]
def FunctionOp.isRefinedBy {ctx₁ ctx₂ : WfIRContext OpCode} {op₁ op₂ : OperationPtr}
    (func₁ : Veir.FunctionOp ctx₁.raw op₁) (func₂ : Veir.FunctionOp ctx₂.raw op₂)
    (op₁In : op₁.InBounds ctx₁.raw := by grind)
    (op₂In : op₂.InBounds ctx₂.raw := by grind) : Prop :=
  ∀ (valuesSource valuesTarget : Array RuntimeValue) (mem : MemoryState),
    RuntimeValue.arrayIsRefinedBy valuesSource valuesTarget →
    Tree.Refines FunctionResult.isRefinedBy
      (CTree.interpretFunctionWithMemory func₁ valuesSource mem op₁In)
      (CTree.interpretFunctionWithMemory func₂ valuesTarget mem op₂In)

/-- Specialize function refinement to particular related arguments and initial memory. -/
theorem FunctionOp.isRefinedBy.interpret
    {ctx₁ ctx₂ : WfIRContext OpCode} {op₁ op₂ : OperationPtr}
    {func₁ : Veir.FunctionOp ctx₁.raw op₁} {func₂ : Veir.FunctionOp ctx₂.raw op₂}
    {op₁In : op₁.InBounds ctx₁.raw} {op₂In : op₂.InBounds ctx₂.raw}
    (h : FunctionOp.isRefinedBy func₁ func₂ op₁In op₂In)
    {valuesSource valuesTarget : Array RuntimeValue} (mem : MemoryState)
    (hvalues : RuntimeValue.arrayIsRefinedBy valuesSource valuesTarget) :
    Tree.Refines FunctionResult.isRefinedBy
      (CTree.interpretFunctionWithMemory func₁ valuesSource mem op₁In)
      (CTree.interpretFunctionWithMemory func₂ valuesTarget mem op₂In) :=
  h valuesSource valuesTarget mem hvalues

/--
CTree function refinement for operation pointers. Both pointers must designate
function-like operations; otherwise this proposition is false.
-/
@[expose]
def OperationPtr.isRefinedByAsFunction (op₁ : OperationPtr) (ctx₁ : WfIRContext OpCode)
    (op₂ : OperationPtr) (ctx₂ : WfIRContext OpCode)
    (op₁In : op₁.InBounds ctx₁.raw := by grind)
    (op₂In : op₂.InBounds ctx₂.raw := by grind) : Prop :=
  match Veir.FunctionOp.of? op₁ ctx₁.raw, Veir.FunctionOp.of? op₂ ctx₂.raw with
  | some func₁, some func₂ => FunctionOp.isRefinedBy func₁ func₂ op₁In op₂In
  | _, _ => False

/-- Resolve the function-pointer relation after identifying the two functions. -/
theorem OperationPtr.isRefinedByAsFunction_iff
    {ctx₁ ctx₂ : WfIRContext OpCode} {op₁ op₂ : OperationPtr}
    {func₁ : Veir.FunctionOp ctx₁.raw op₁} {func₂ : Veir.FunctionOp ctx₂.raw op₂}
    (hfunc₁ : Veir.FunctionOp.of? op₁ ctx₁.raw = some func₁)
    (hfunc₂ : Veir.FunctionOp.of? op₂ ctx₂.raw = some func₂)
    (op₁In : op₁.InBounds ctx₁.raw := by grind)
    (op₂In : op₂.InBounds ctx₂.raw := by grind) :
    OperationPtr.isRefinedByAsFunction op₁ ctx₁ op₂ ctx₂ op₁In op₂In ↔
      FunctionOp.isRefinedBy func₁ func₂ op₁In op₂In := by
  simp [OperationPtr.isRefinedByAsFunction, hfunc₁, hfunc₂]

/--
Whole-program refinement: every top-level source `func.func` is refined, with
CTree semantics, by a same-named top-level target `func.func`. Additional target
functions are allowed. Top-level membership and names use the same structural
predicate as the outcome-monad refinement API.
-/
@[expose]
def OperationPtr.isModuleRefinedBy (mod₁ : OperationPtr) (ctx₁ : WfIRContext OpCode)
    (mod₂ : OperationPtr) (ctx₂ : WfIRContext OpCode) : Prop :=
  ∀ (func₁ : OperationPtr) (func₁In : func₁.InBounds ctx₁.raw) (name : StringAttr),
    func₁.IsTopLevelFuncWithName mod₁ ctx₁.raw name →
      ∃ (func₂ : OperationPtr) (func₂In : func₂.InBounds ctx₂.raw),
        func₂.IsTopLevelFuncWithName mod₂ ctx₂.raw name ∧
          OperationPtr.isRefinedByAsFunction func₁ ctx₁ func₂ ctx₂ func₁In func₂In

end Veir.Tree.Refinement
