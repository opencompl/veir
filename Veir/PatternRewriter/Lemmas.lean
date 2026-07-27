module

public import Veir.PatternRewriter.Basic

import all Veir.PatternRewriter.Basic

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

/-- `replaceValue!` only touches the context through `WfRewriter.replaceValue!`; combine with
`WfRewriter.replaceValue!_eq_replaceValue` to reach the checked version. -/
@[grind =]
theorem replaceValue!_ctx {rewriter : PatternRewriter OpInfo} {oldVal newVal : ValuePtr}
    (oldIn : oldVal.InBounds rewriter.ctx.raw) :
    (rewriter.replaceValue! oldVal newVal).ctx
      = WfRewriter.replaceValue! rewriter.ctx oldVal newVal := by
  simp [replaceValue!, oldIn, addUsersInWorklist_same_ctx]
