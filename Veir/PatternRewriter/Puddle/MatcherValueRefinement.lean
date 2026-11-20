module
public import Veir.PatternRewriter.Puddle.CTreeRewriteInvariant
import all Veir.PatternRewriter.Puddle.MatcherResolverHistory
import all Veir.Interpreter.VariableState
import all Veir.Dominance.Basic
import all Veir.IR.Basic
import all Veir.Interpreter.CTreeEntryInvariant

namespace Veir.Puddle
public section

/-- Refinement of original SSA slots watched by the matcher, irrespective of target scope. -/
@[expose]
def ValueResolver.WatchedRefines (source target : ValueResolver) (ctx : WfIRContext OpCode)
    (region : RegionPtr) (rewriteRoot : OperationPtr) (point : InsertPoint) : Prop :=
  ∀ value, value.InBounds ctx.raw → value.DefinedInRegion region ctx →
    value.DominatesIp (.before rewriteRoot) ctx → value.DominatesIp point ctx →
    ∀ sourceValue targetValue, source value = some sourceValue → target value = some targetValue →
      RuntimeValue.isRefinedBy sourceValue targetValue

theorem ValueResolver.WatchedRefines.after_operation
    {source target updatedSource updatedTarget : ValueResolver} {ctx : WfIRContext OpCode}
    {region : RegionPtr} {rewriteRoot op : OperationPtr} {block : BlockPtr}
    (opIn : op.InBounds ctx.raw) (opParent : op.getParent! ctx.raw = some block)
    (blockParent : block.getParent! ctx.raw = some region)
    (prior : source.WatchedRefines target ctx region rewriteRoot (.before op))
    (sourcePreserved : ∀ value, value.InBounds ctx.raw → value ∉ op.getResults! ctx.raw →
      updatedSource value = source value)
    (targetPreserved : ∀ value, value.InBounds ctx.raw → value ∉ op.getResults! ctx.raw →
      updatedTarget value = target value)
    (installed : ∀ value ∈ op.getResults! ctx.raw, ∀ s t,
      updatedSource value = some s → updatedTarget value = some t → s ⊒ t) :
    updatedSource.WatchedRefines updatedTarget ctx region rewriteRoot (InsertPoint.after op ctx.raw block) := by
  intro value bounds inside static dynamic s t hs ht
  by_cases result : value ∈ op.getResults! ctx.raw
  · exact installed value result s t hs ht
  · obtain old | fresh := (ValuePtr.DominatesIp.after_iff blockParent).mp dynamic
    · exact prior value bounds inside static old s t
        ((sourcePreserved value bounds result).symm.trans hs)
        ((targetPreserved value bounds result).symm.trans ht)
    · exact False.elim (result fresh)

theorem ValueResolver.WatchedRefines.successor_entry
    {source target updatedSource updatedTarget : ValueResolver} {ctx : WfIRContext OpCode}
    {region : RegionPtr} {rewriteRoot : OperationPtr} {block succ : BlockPtr}
    (blockParent : block.getParent! ctx.raw = some region)
    (succParent : succ.getParent! ctx.raw = some region)
    (ssa : region.hasSSADominance ctx) (successor : succ ∈ block.getSuccessors! ctx.raw)
    (prior : source.WatchedRefines target ctx region rewriteRoot (.atEnd block))
    (sourcePreserved : ∀ value, value.InBounds ctx.raw → value ∉ succ.getArguments! ctx.raw →
      updatedSource value = source value)
    (targetPreserved : ∀ value, value.InBounds ctx.raw → value ∉ succ.getArguments! ctx.raw →
      updatedTarget value = target value)
    (installed : ∀ value ∈ succ.getArguments! ctx.raw, ∀ s t,
      updatedSource value = some s → updatedTarget value = some t → s ⊒ t) :
    updatedSource.WatchedRefines updatedTarget ctx region rewriteRoot (InsertPoint.atStart! succ ctx.raw) := by
  intro value bounds inside static dynamic s t hs ht
  by_cases argument : value ∈ succ.getArguments! ctx.raw
  · exact installed value argument s t hs ht
  · obtain old | fresh := ValuePtr.DominatesIp.predecessor_exit_of_successor_entry
      blockParent succParent ssa successor dynamic
    · exact prior value bounds inside static old s t
        ((sourcePreserved value bounds argument).symm.trans hs)
        ((targetPreserved value bounds argument).symm.trans ht)
    · exact False.elim (argument fresh)

/-- Successful setters on a surviving operation maintain watched-slot refinement.
Result types have already been checked by the setters; only their counts and related values matter. -/
theorem ValueResolver.WatchedRefines.setResultValues_after
    {sourceCtx targetCtx : WfIRContext OpCode} {source source' : VariableState sourceCtx}
    {target target' : VariableState targetCtx} {op rewriteRoot : OperationPtr} {region : RegionPtr} {block : BlockPtr}
    {sourceValues targetValues : Array RuntimeValue}
    {sourceIn : op.InBounds sourceCtx.raw} {targetIn : op.InBounds targetCtx.raw}
    (count : op.getNumResults! targetCtx.raw = op.getNumResults! sourceCtx.raw)
    (opParent : op.getParent! sourceCtx.raw = some block)
    (blockParent : block.getParent! sourceCtx.raw = some region)
    (prior : ValueResolver.WatchedRefines source.getVar? target.getVar? sourceCtx region rewriteRoot (.before op))
    (values : RuntimeValue.arrayIsRefinedBy sourceValues targetValues)
    (sourceSet : source.setResultValues? op sourceValues sourceIn = some source')
    (targetSet : target.setResultValues? op targetValues targetIn = some target') :
    ValueResolver.WatchedRefines source'.getVar? target'.getVar? sourceCtx region rewriteRoot
      (InsertPoint.after op sourceCtx.raw block) := by
  apply prior.after_operation sourceIn opParent blockParent
  · intro value bounds notResult
    exact VariableState.getVar?_setResultValues?_of_notMem_getResults! notResult sourceSet
  · intro value bounds notResult
    apply VariableState.getVar?_setResultValues?_of_notMem_getResults! ?_ targetSet
    intro member
    obtain ⟨index, hi, equal⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp member
    apply notResult
    rw [← equal]
    apply OperationPtr.getResults!.mem_iff_exists_index.mpr
    exact ⟨index, by omega, rfl⟩
  · intro value member s t hs ht
    obtain ⟨index, hi, equal⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp member
    subst value
    have sg := VariableState.getVar?_getResult_of_setResultValues? hi sourceSet
    have tg := VariableState.getVar?_getResult_of_setResultValues? (by omega : index < op.getNumResults! targetCtx.raw) targetSet
    rw [sg] at hs
    rw [tg] at ht
    cases hs
    cases ht
    exact values.2 index (by grind)

/-- Checked installation of related successor arguments preserves original watched slots. -/
theorem ValueResolver.WatchedRefines.setArgumentValues_successor
    {sourceCtx targetCtx : WfIRContext OpCode} {source source' : VariableState sourceCtx}
    {target target' : VariableState targetCtx} {rewriteRoot : OperationPtr} {region : RegionPtr} {block succ : BlockPtr}
    {sourceValues targetValues : Array RuntimeValue}
    {sourceIn : succ.InBounds sourceCtx.raw} {targetIn : succ.InBounds targetCtx.raw}
    (count : succ.getNumArguments! targetCtx.raw = succ.getNumArguments! sourceCtx.raw)
    (blockParent : block.getParent! sourceCtx.raw = some region)
    (succParent : succ.getParent! sourceCtx.raw = some region)
    (ssa : region.hasSSADominance sourceCtx) (successor : succ ∈ block.getSuccessors! sourceCtx.raw)
    (prior : ValueResolver.WatchedRefines source.getVar? target.getVar? sourceCtx region rewriteRoot (.atEnd block))
    (values : RuntimeValue.arrayIsRefinedBy sourceValues targetValues)
    (sourceSet : source.setArgumentValues? succ sourceValues sourceIn = some source')
    (targetSet : target.setArgumentValues? succ targetValues targetIn = some target') :
    ValueResolver.WatchedRefines source'.getVar? target'.getVar? sourceCtx region rewriteRoot
      (InsertPoint.atStart! succ sourceCtx.raw) := by
  have sourceSize : sourceValues.size = succ.getNumArguments! sourceCtx.raw := by
    unfold VariableState.setArgumentValues? at sourceSet
    split at sourceSet <;> simp_all
  apply prior.successor_entry blockParent succParent ssa successor
  · intro value bounds notArgument
    exact VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! notArgument sourceSet
  · intro value bounds notArgument
    apply VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! ?_ targetSet
    intro member
    obtain ⟨index, hi, equal⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp member
    apply notArgument
    rw [← equal]
    apply BlockPtr.getArguments!.mem_iff_exists_index.mpr
    exact ⟨index, by omega, rfl⟩
  · intro value member s t hs ht
    obtain ⟨index, hi, equal⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp member
    subst value
    have sg := VariableState.getVar?_getArgument_of_setArgumentValues? hi sourceSet
    have tg := VariableState.getVar?_getArgument_of_setArgumentValues? (by omega : index < succ.getNumArguments! targetCtx.raw) targetSet
    rw [sg] at hs
    rw [tg] at ht
    cases hs
    cases ht
    exact values.2 index (by grind)

end
end Veir.Puddle
