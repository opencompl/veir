module

public import Veir.Dominance.Lemmas.Block
public import Veir.Dominance.Lemmas.Operation

import all Veir.Dominance.Basic

/-! # Lemmas for the Dominance Invariant `WfIRContext.Dom` -/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] {ctx : WfIRContext OpInfo}
variable {op op₁ op₂ : OperationPtr}
variable {root : IRNode} {region : RegionPtr} {value : ValuePtr}

namespace WfIRContext.Dom

/-- Operands of a locally reachable operation under the dominance root properly dominate
their user. -/
theorem operand_properlyDominates (ctxDom : ctx.Dom root)
    (opInRoot : root.Ancestor op ctx)
    (opReachable : op.LocallyReachable region ctx)
    (operand : value ∈ op.getOperands! ctx.raw) :
    value.ProperlyDominates op ctx := by
  obtain ⟨block, opParent, blockParent, reachable⟩ := opReachable
  exact ctxDom opInRoot opParent blockParent reachable operand

/-- Under the dominance invariant, an operand of a locally reachable user under `root`
cannot be a result of an operation that fails to properly dominate the user with
`enclosingOk = false`. -/
theorem not_mem_results_of_mem_operands (ctxDom : ctx.Dom root)
    (op₁InRoot : root.Ancestor op₁ ctx)
    (blockReachable : op₁.LocallyReachable region ctx) :
    ¬ op₂.ProperlyDominates op₁ ctx false →
    ∀ (value : ValuePtr), value ∈ op₁.getOperands! ctx.raw →
    value ∉ op₂.getResults! ctx.raw := by
  intro notDominance value operand result
  have dominance := ctxDom.operand_properlyDominates op₁InRoot blockReachable operand
  obtain ⟨index, _, valueEq⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp result
  rw [← valueEq] at dominance
  exact notDominance (by simpa only [ValuePtr.ProperlyDominates,
    OperationPtr.getResult_op] using dominance)

/-- Operands of a locally reachable operation under the dominance root dominate the point
before their user. -/
@[grind →]
theorem operand_dominatesIp_before (ctxDom : ctx.Dom root)
    (opInRoot : root.Ancestor op ctx)
    (opReachable : op.LocallyReachable region ctx) :
    value ∈ op.getOperands! ctx.raw → value.DominatesIp (.before op) ctx := by
  intro operand
  exact ValuePtr.DominatesIp.before_iff.mpr
    (ctxDom.operand_properlyDominates opInRoot opReachable operand)

/-- A result used by a locally reachable operation under the dominance root is defined by an
operation that properly dominates its user with `enclosingOk = false`. -/
theorem definingOp_properlyDominates_of_mem_operands
    (ctxDom : ctx.Dom root) (op₂InRoot : root.Ancestor op₂ ctx)
    (blockReachable : op₂.LocallyReachable region ctx) :
    value.definingOp? = some op₁ → value ∈ op₂.getOperands! ctx.raw →
    op₁.ProperlyDominates op₂ ctx false := by
  intro definingOp operand
  have dominance := ctxDom.operand_properlyDominates op₂InRoot blockReachable operand
  cases value with
  | opResult result =>
    have opEq : result.op = op₁ :=
      Option.some.inj (by simpa only [ValuePtr.definingOp?_opResult] using definingOp)
    rw [← opEq]
    exact dominance
  | blockArgument argument =>
    simp only [ValuePtr.definingOp?_blockArgument, reduceCtorEq] at definingOp

grind_pattern definingOp_properlyDominates_of_mem_operands =>
  ctx.Dom root, root.Ancestor op₂ ctx, op₂.LocallyReachable region ctx,
  value.definingOp?, some op₁, op₂.getOperands! ctx.raw where
  guard value.definingOp? = some op₁

/-- Operands of a locally reachable rooted dominator are not results of a hierarchically
reachable dominated SSA operation. -/
theorem not_mem_results_of_mem_operands_of_dominates
    (ctxDom : ctx.Dom root) (op₁Rooted : op₁.RootedAt root ctx)
    (op₁Reachable : op₁.LocallyReachable region₁ ctx)
    (op₂Region : op₂.getParentRegion! ctx.raw = some region)
    (regionSSA : region.hasSSADominance ctx)
    (op₂Reachable : op₂.HierarchicallyReachable ctx) :
    op₁.Dominates op₂ ctx enclosingOk →
    ∀ value, value ∈ op₁.getOperands! ctx.raw → value ∉ op₂.getResults! ctx.raw := by
  grind [WfIRContext.Dom.not_mem_results_of_mem_operands]

end WfIRContext.Dom

end Veir
