module

public import Veir.Rewriter.WfRewriter.GetSet
public import Veir.Rewriter.WfRewriter.InBounds

import all Veir.Rewriter.WfRewriter.Basic

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}

/-! ## `WfRewriter.replaceValue` -/

section WfRewriter.replaceValue

variable {oldValue newValue : ValuePtr}
variable {oldIn : oldValue.InBounds ctx.raw} {newIn : newValue.InBounds ctx.raw}
variable {ne : oldValue ≠ newValue}

@[simp, grind =]
theorem ValuePtr.hasUses!_WfRewriter_replaceValue_oldValue :
    oldValue.hasUses! (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw = false := by
  fun_induction WfRewriter.replaceValue <;>
    grind [Id.run, ValuePtr.hasUses!_def, ValuePtr.getFirstUse!_eq_getFirstUse]

/-- After replacing the (sole) result of `op` with another value, `op` no longer has any uses. -/
@[grind =]
theorem OperationPtr.hasUses!_WfRewriter_replaceValue_getResult0
    {op : OperationPtr} {newValue : ValuePtr}
    {hres : (op.getResult 0 : ValuePtr).InBounds ctx.raw}
    {hnew : newValue.InBounds ctx.raw}
    {hne : (op.getResult 0 : ValuePtr) ≠ newValue}
    (hone : op.getNumResults! ctx.raw = 1) :
    op.hasUses!
      (WfRewriter.replaceValue ctx (op.getResult 0) newValue hne hres hnew).raw = false := by
  rw [OperationPtr.hasUses!_eq_false_iff_hasUses!_getResult_eq_false]
  intro index hindex
  have hnum : op.getNumResults!
      (WfRewriter.replaceValue ctx (op.getResult 0) newValue hne hres hnew).raw = 1 := by
    rw [OperationPtr.getNumResults!_WfRewriter_replaceValue]
    exact hone
  have hidx0 : index = 0 := by omega
  subst hidx0
  exact ValuePtr.hasUses!_WfRewriter_replaceValue_oldValue

/-- After replacing `op`'s single result with `newValue`, `op` still exists, still has no regions,
and now has no uses — exactly the preconditions required to erase it. -/
theorem OperationPtr.erase_preconditions_after_replace_result0
    {op : OperationPtr} {newValue : ValuePtr}
    (hop : op.InBounds ctx.raw)
    (hres : (op.getResult 0 : ValuePtr).InBounds ctx.raw)
    (hnew : newValue.InBounds ctx.raw)
    (hne : (op.getResult 0 : ValuePtr) ≠ newValue)
    (hone : op.getNumResults! ctx.raw = 1)
    (hregions : op.getNumRegions! ctx.raw = 0) :
    let ctx' :=
      WfRewriter.replaceValue ctx (op.getResult 0 : ValuePtr) newValue hne hres hnew
    op.InBounds ctx'.raw ∧
    op.getNumRegions! ctx'.raw = 0 ∧
    op.hasUses! ctx'.raw = false := by
  have h1 : op.InBounds
      (WfRewriter.replaceValue ctx (op.getResult 0) newValue hne hres hnew).raw := by
    rw [← GenericPtr.iff_operation, WfRewriter.replaceValue_inBounds, GenericPtr.iff_operation]
    exact hop
  have h2 : op.getNumRegions!
      (WfRewriter.replaceValue ctx (op.getResult 0) newValue hne hres hnew).raw = 0 := by
    rw [OperationPtr.getNumRegions!_WfRewriter_replaceValue]
    exact hregions
  exact ⟨h1, h2, OperationPtr.hasUses!_WfRewriter_replaceValue_getResult0 hone⟩

end WfRewriter.replaceValue
