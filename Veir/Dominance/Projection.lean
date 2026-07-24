module

public import Veir.Dominance.Basic

/-!
# Ancestor Operation Lemmas for Dominance

Lemmas about selecting an ancestor operation in a region, including the
deterministic first-ancestor witness needed by insertion-point lifting. The
relations themselves live in `Veir.Dominance.Basic`.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}

namespace OperationPtr.AncestorOpInRegion

variable {op ancestor : OperationPtr}
variable {region : RegionPtr}

/-- The selected operation is an ancestor of the original operation. -/
theorem isAncestor
    (ancestorInRegion : op.AncestorOpInRegion ancestor region ctx) :
    (IRNode.operation ancestor).Ancestor (.operation op) ctx :=
  ancestorInRegion.1

/-- The selected ancestor operation is directly contained in the region. -/
theorem getParentRegion_eq
    (ancestorInRegion : op.AncestorOpInRegion ancestor region ctx) :
    ancestor.getParentRegion! ctx.raw = some region :=
  ancestorInRegion.2

/-- The selected ancestor operation and its block are contained in the region. -/
theorem parent_region
    (ancestorInRegion : op.AncestorOpInRegion ancestor region ctx) :
    ∃ block,
      (ancestor.get! ctx.raw).parent = some block ∧
      (block.get! ctx.raw).parent = some region :=
  OperationPtr.getParentRegion!_eq_some_iff.mp
    ancestorInRegion.getParentRegion_eq

end OperationPtr.AncestorOpInRegion

namespace OperationPtr.FirstAncestorOpInRegion

variable {op projection projection₁ projection₂ : OperationPtr}
variable {region : RegionPtr}

/-- The projected operation is directly contained in the requested region. -/
theorem parent_region
    (projected : op.FirstAncestorOpInRegion region projection ctx) :
    ∃ block,
      (projection.get! ctx.raw).parent = some block ∧
      (block.get! ctx.raw).parent = some region := by
  induction projected with
  | here opParent blockParent => exact ⟨_, opParent, blockParent⟩
  | step _ _ _ _ _ ih => exact ih

/-- The projected operation is an ancestor of the original operation. -/
theorem isAncestor
    (projected : op.FirstAncestorOpInRegion region projection ctx) :
    (IRNode.operation projection).Ancestor (.operation op) ctx := by
  induction projected with
  | here => exact .refl
  | @step op region block currentRegion parent projection ctx opParent blockParent
      regionNe regionParent tail ih =>
      apply ih.trans
      apply IRNode.Ancestor.of_getParentOp!_eq_some
      exact OperationPtr.getParentOp!_eq_some_iff.mpr
        ⟨block, currentRegion, opParent, blockParent, regionParent⟩

/-- A first-ancestor witness gives an ancestor operation in the region. -/
theorem toAncestorOpInRegion
    (projected : op.FirstAncestorOpInRegion region projection ctx) :
    op.AncestorOpInRegion projection region ctx :=
  ⟨projected.isAncestor,
    OperationPtr.getParentRegion!_eq_some_iff.mpr projected.parent_region⟩

/-- The first ancestor operation in a region is unique. -/
theorem unique
    (left : op.FirstAncestorOpInRegion region projection₁ ctx)
    (right : op.FirstAncestorOpInRegion region projection₂ ctx) :
    projection₁ = projection₂ := by
  induction left with
  | @here op region leftBlock ctx leftOpParent leftBlockParent =>
      cases right with
      | @here _ _ rightBlock _ rightOpParent rightBlockParent => rfl
      | @step _ _ rightBlock currentRegion parent projection _ rightOpParent
          rightBlockParent regionNe regionParent tail =>
          have blockEq := Option.some.inj (leftOpParent.symm.trans rightOpParent)
          subst rightBlock
          have regionEq :=
            Option.some.inj (leftBlockParent.symm.trans rightBlockParent)
          exact False.elim (regionNe regionEq.symm)
  | @step op region leftBlock leftRegion leftParent projection ctx leftOpParent
      leftBlockParent leftRegionNe leftRegionParent leftTail ih =>
      cases right with
      | @here _ _ rightBlock _ rightOpParent rightBlockParent =>
          have blockEq := Option.some.inj (leftOpParent.symm.trans rightOpParent)
          subst rightBlock
          have regionEq :=
            Option.some.inj (leftBlockParent.symm.trans rightBlockParent)
          exact False.elim (leftRegionNe regionEq)
      | @step _ _ rightBlock rightRegion rightParent _ _ rightOpParent
          rightBlockParent rightRegionNe rightRegionParent rightTail =>
          have blockEq := Option.some.inj (leftOpParent.symm.trans rightOpParent)
          subst rightBlock
          have regionEq :=
            Option.some.inj (leftBlockParent.symm.trans rightBlockParent)
          subst rightRegion
          have parentEq :=
            Option.some.inj (leftRegionParent.symm.trans rightRegionParent)
          subst rightParent
          exact ih rightTail

end OperationPtr.FirstAncestorOpInRegion

end Veir
