module

public import Veir.PatternRewriter.Basic

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

namespace PatternRewriter

@[simp, grind =]
theorem replaceValue_ctx {rewriter : PatternRewriter OpInfo} {oldVal newVal : ValuePtr}
    {neValues : oldVal ≠ newVal} {oldIn : oldVal.InBounds rewriter.ctx.raw}
    {newIn : newVal.InBounds rewriter.ctx.raw} :
    (rewriter.replaceValue oldVal newVal neValues oldIn newIn).ctx
      = WfRewriter.replaceValue rewriter.ctx oldVal newVal neValues oldIn newIn := by
  simp [replaceValue, addUsersInWorklist_same_ctx]
