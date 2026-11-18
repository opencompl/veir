module

public import Veir.IR.RootedIso
public import Veir.Interpreter.Basic

public section

namespace Veir

/-- Forget allocation-dependent diagnostic pointers, retaining errors, UB, and successful results. -/
def Interp.eraseBlame : Interp α → Interp α
  | .fail _ => .fail none
  | .ub _ => .ub none
  | .ok a => .ok a

/-- Closed isomorphic functions have identical interpreter behavior for the same arguments
and initial memory, including multi-block control flow. Only diagnostic pointers are erased.
The current `Interp` semantics represents nontermination by `ub none`. -/
theorem RootedIso.semantic_equivalence
    {ctx₁ ctx₂ : WfIRContext OpCode} {root₁ root₂ : OperationPtr}
    (_ : RootedIso ctx₁ root₁ ctx₂ root₂)
    (closed₁ : RootedClosed ctx₁ root₁) (closed₂ : RootedClosed ctx₂ root₂)
    (func₁ : FunctionOp ctx₁.raw root₁) (func₂ : FunctionOp ctx₂.raw root₂)
    (args : Array RuntimeValue) (memory : MemoryState) :
    (interpretFunction func₁ args memory closed₁.1).eraseBlame =
      (interpretFunction func₂ args memory closed₂.1).eraseBlame := sorry

end Veir
