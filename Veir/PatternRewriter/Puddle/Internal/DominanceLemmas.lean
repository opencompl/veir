module

public import Veir.Dominance.Lemmas.Dom
import all Veir.Dominance.Basic

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] {ctx : WfIRContext OpInfo}
variable {op op₁ op₂ : OperationPtr}
variable {root : IRNode} {region : RegionPtr} {value : ValuePtr}

namespace WfIRContext.Dom

/-- A reachable operation cannot use the result of an unreachable operation.
This lets a rewrite of unreachable code leave all reachable operands unchanged. -/
theorem not_mem_results_of_not_hierarchicallyReachable
    (ctxDom : ctx.Dom root)
    (op₁InRoot : root.Ancestor op₁ ctx)
    (op₁Region : op₁.getParentRegion! ctx.raw = some region)
    (reachable : op₁.HierarchicallyReachable ctx)
    (unreachable : ¬ op₂.HierarchicallyReachable ctx) :
    ∀ value, value ∈ op₁.getOperands! ctx.raw → value ∉ op₂.getResults! ctx.raw := by
  obtain ⟨_, localReachable⟩ := reachable.exists_locallyReachable op₁Region
  apply ctxDom.not_mem_results_of_mem_operands op₁InRoot localReachable
  intro dominance
  exact unreachable (reachable.of_dominates (.inr dominance))

end WfIRContext.Dom

end Veir
