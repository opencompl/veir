module

public import Veir.Rewriter.LinkedList.GetSet
import Veir.IR.LayoutUnchanged

public section

namespace Veir.Sim

attribute [local grind] 
  OperationPtr.LayoutPreserved BlockPtr.LayoutPreserved
  IRContext.LayoutPreserved IRContext.LayoutUnchanged


variable {OpInfo : Type} [HasOpInfo OpInfo]

variable {ctx : IRContext OpInfo}

/-! Basic functions preserve layouts. -/

variable {op : OperationPtr} (h : op.InBounds ctx)

@[grind .]
theorem OpOperandPtr.removeFromCurrent_layoutUnchanged :
    ctx.spec.LayoutUnchanged (removeFromCurrent ctx oper h₁ h₂).spec := by
  grind

@[grind .]
theorem OpOperandPtr.insertIntoCurrent_layoutUnchanged :
    ctx.spec.LayoutUnchanged (insertIntoCurrent ctx oper h₁ h₂).spec := by
  grind

@[grind .]
theorem BlockOperandPtr.removeFromCurrent_layoutUnchanged :
    ctx.spec.LayoutUnchanged (removeFromCurrent ctx oper h₁ h₂).spec := by
  grind

@[grind .]
theorem BlockOperandPtr.insertIntoCurrent_layoutUnchanged :
    ctx.spec.LayoutUnchanged (insertIntoCurrent ctx oper h₁ h₂).spec := by
  grind

@[grind .]
theorem OperationPtr.linkBetween_layoutUnchanged :
    ctx.spec.LayoutUnchanged (linkBetween self ctx prevOp nextOp h₁ h₂ h₃).spec := by
  grind

@[grind .]
theorem OperationPtr.setParentWithCheck_layoutUnchanged :
    setParentWithCheck self ctx parent h₁ h₂ = some ctx' →
    ctx.spec.LayoutUnchanged ctx'.spec := by
  grind

@[grind .]
theorem OperationPtr.linkBetweenWithParent_layoutUnchanged :
    linkBetweenWithParent self ctx prevOp nextOp parent h₁ h₂ h₃ h₄ = some ctx' →
    ctx.spec.LayoutUnchanged ctx'.spec := by
  grind

@[grind .]
theorem BlockPtr.linkBetween_layoutUnchanged :
    ctx.spec.LayoutUnchanged (linkBetween self ctx prevBl nextBl h₁ h₂ h₃).spec := by
  grind

@[grind .]
theorem BlockPtr.setParentWithCheck_layoutUnchanged :
    setParentWithCheck self ctx parent h₁ h₂ = some ctx' →
    ctx.spec.LayoutUnchanged ctx'.spec := by
  grind

@[grind .]
theorem BlockPtr.linkBetweenWithParent_layoutUnchanged :
    linkBetweenWithParent self ctx prevBl nextBl parent h₁ h₂ h₃ h₄ = some ctx' →
    ctx.spec.LayoutUnchanged ctx'.spec := by
  grind
