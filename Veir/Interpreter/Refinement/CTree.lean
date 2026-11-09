module

public import Veir.Interpreter.Refinement.Lemmas
public import Veir.Interpreter.CTreeStateRefinement
import all Veir.Interpreter.CTreeStateRefinement

public section

namespace Veir

/-- Compose CTree refinement of function operations, including refinement of their arguments. -/
theorem OperationPtr.isRefinedByAsFunctionCTree_trans
    {ctx₁ ctx₂ ctx₃ : WfIRContext OpCode} {op₁ op₂ op₃ : OperationPtr}
    {op₁In : op₁.InBounds ctx₁.raw} {op₂In : op₂.InBounds ctx₂.raw}
    {op₃In : op₃.InBounds ctx₃.raw}
    (h₁₂ : op₁.isRefinedByAsFunctionCTree ctx₁ op₂ ctx₂ op₁In op₂In)
    (h₂₃ : op₂.isRefinedByAsFunctionCTree ctx₂ op₃ ctx₃ op₂In op₃In) :
    op₁.isRefinedByAsFunctionCTree ctx₁ op₃ ctx₃ op₁In op₃In := by
  simp only [isRefinedByAsFunctionCTree] at h₁₂ h₂₃ ⊢
  cases h₁ : FunctionOp.of? op₁ ctx₁.raw <;>
    cases h₂ : FunctionOp.of? op₂ ctx₂.raw <;>
    cases h₃ : FunctionOp.of? op₃ ctx₃.raw <;> simp_all only
  intro source target mem hargs
  exact _root_.CTree.Sim.trans
    (h₂₃ source target mem hargs) (h₁₂ source source mem (RuntimeValue.arrayIsRefinedBy_refl _))
    (fun _ _ _ h₃₂ h₂₁ => RuntimeValue.arrayIsRefinedBy_trans h₂₁ h₃₂)

/-- Module refinement composes through the same-named intermediate functions. -/
theorem OperationPtr.isModuleRefinedByCTree_trans
    {ctx₁ ctx₂ ctx₃ : WfIRContext OpCode} {mod₁ mod₂ mod₃ : OperationPtr}
    (h₁₂ : mod₁.isModuleRefinedByCTree ctx₁ mod₂ ctx₂)
    (h₂₃ : mod₂.isModuleRefinedByCTree ctx₂ mod₃ ctx₃) :
    mod₁.isModuleRefinedByCTree ctx₁ mod₃ ctx₃ := by
  intro func₁ func₁In name hname₁
  obtain ⟨func₂, func₂In, hname₂, hfunc₁₂⟩ := h₁₂ func₁ func₁In name hname₁
  obtain ⟨func₃, func₃In, hname₃, hfunc₂₃⟩ := h₂₃ func₂ func₂In name hname₂
  exact ⟨func₃, func₃In, hname₃, isRefinedByAsFunctionCTree_trans hfunc₁₂ hfunc₂₃⟩

end Veir
