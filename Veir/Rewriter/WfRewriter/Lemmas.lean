module

public import Veir.Rewriter.WfRewriter.GetSet

import all Veir.Rewriter.WfRewriter.Basic

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] {ctx : WfIRContext OpInfo}
variable {oldValue newValue : ValuePtr} {op : OperationPtr}

/-! ## `WfRewriter.replaceValue` -/

theorem ValuePtr.hasUses!_WfRewriter_replaceValue_oldValue
    {ne : oldValue ≠ newValue} {oldIn : oldValue.InBounds ctx.raw}
    {newIn : newValue.InBounds ctx.raw} :
    oldValue.hasUses! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw
      = false := by
  fun_induction WfRewriter.replaceValue <;>
    grind [Id.run, ValuePtr.hasUses!_def, ValuePtr.getFirstUse!_eq_getFirstUse]

/-- After replacing the (sole) result of `op` with another value, `op` no longer has any uses. -/
@[grind =]
theorem OperationPtr.hasUses!_WfRewriter_replaceValue_getResult0
    {hne : (op.getResult 0 : ValuePtr) ≠ newValue}
    {hres : (op.getResult 0 : ValuePtr).InBounds ctx.raw}
    {newIn : newValue.InBounds ctx.raw} (hone : op.getNumResults! ctx.raw = 1) :
    op.hasUses!
      (WfRewriter.replaceValue ctx (op.getResult 0) newValue hne hres newIn).raw = false := by
  rw [OperationPtr.hasUses!_eq_false_iff_hasUses!_getResult_eq_false]
  intro index hindex
  obtain rfl : index = 0 := by grind
  exact ValuePtr.hasUses!_WfRewriter_replaceValue_oldValue
