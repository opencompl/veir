module

public import Veir.Dominance.Operation

/-!
# Insertion-Point Dominance Lemmas

Lemmas about insertion-point projection and dominance. The underlying
definitions live in `Veir.Dominance.Basic`.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}

namespace InsertPoint.LiftToRegion

variable {point lifted lifted₁ lifted₂ : InsertPoint}
variable {region : RegionPtr}
variable {block : BlockPtr}

/-- A point lifted into its existing region is unchanged. -/
theorem here
    (pointBlockEq : point.block! ctx.raw = some block)
    (blockParent : (block.get! ctx.raw).parent = some region) :
    point.LiftToRegion region point ctx := by
  cases point with
  | before op =>
      exact .before (.here (by simpa using pointBlockEq) blockParent)
  | atEnd endBlock =>
      have : endBlock = block := by simpa using pointBlockEq
      subst endBlock
      exact .atEndHere blockParent

/-- The lifted point lies in a block directly contained in the requested region. -/
theorem lifted_parent
    (liftedPoint : point.LiftToRegion region lifted ctx) :
    ∃ block,
      lifted.block! ctx.raw = some block ∧
      (block.get! ctx.raw).parent = some region := by
  cases liftedPoint with
  | before projectionPath =>
      obtain ⟨block, projectionParent, blockParent⟩ := projectionPath.parent_region
      exact ⟨block, by simpa using projectionParent, blockParent⟩
  | atEndHere blockParent =>
      exact ⟨_, by simp, blockParent⟩
  | atEndNested _ _ _ projectionPath =>
      obtain ⟨block, projectionParent, blockParent⟩ := projectionPath.parent_region
      exact ⟨block, by simpa using projectionParent, blockParent⟩

/-- A lift witness exposes the region containing the original point. -/
theorem source_parent
    (liftedPoint : point.LiftToRegion region lifted ctx) :
    ∃ block currentRegion,
      point.block! ctx.raw = some block ∧
      (block.get! ctx.raw).parent = some currentRegion := by
  cases liftedPoint with
  | before projectionPath =>
      cases projectionPath with
      | here opParent blockParent =>
          exact ⟨_, _, by simpa using opParent, blockParent⟩
      | step opParent blockParent _ _ _ =>
          exact ⟨_, _, by simpa using opParent, blockParent⟩
  | atEndHere blockParent =>
      exact ⟨_, _, by simp, blockParent⟩
  | atEndNested blockParent _ _ _ =>
      exact ⟨_, _, by simp, blockParent⟩

/-- Lifting an insertion point into a region is deterministic. -/
theorem unique
    (left : point.LiftToRegion region lifted₁ ctx)
    (right : point.LiftToRegion region lifted₂ ctx) :
    lifted₁ = lifted₂ := by
  cases left with
  | before leftProjection =>
      cases right with
      | before rightProjection =>
          have := leftProjection.unique rightProjection
          grind
  | @atEndHere block region ctx leftBlockParent =>
      cases right with
      | atEndHere => rfl
      | @atEndNested _ rightRegion _ rightParent rightProjection _
          rightBlockParent rightRegionNe rightRegionParent rightProjectionPath =>
          have : rightRegion = region := by grind
          exact False.elim (rightRegionNe this)
  | @atEndNested block leftRegion region leftParent leftProjection ctx
      leftBlockParent leftRegionNe leftRegionParent leftProjectionPath =>
      cases right with
      | atEndHere rightBlockParent =>
          have : leftRegion = region := by grind
          exact False.elim (leftRegionNe this)
      | @atEndNested _ rightRegion _ rightParent rightProjection _
          rightBlockParent rightRegionNe rightRegionParent rightProjectionPath =>
          have regionEq : leftRegion = rightRegion := by grind
          subst rightRegion
          have parentEq : leftParent = rightParent := by grind
          subst rightParent
          have := leftProjectionPath.unique rightProjectionPath
          grind

/--
Before and after points lift differently only in the operation's own region.
In every proper ancestor region they both lift to the same point before the
same enclosing operation.
-/
theorem before_after
    {op : OperationPtr} {opBlock : BlockPtr}
    {currentRegion region : RegionPtr}
    {beforeLift afterLift : InsertPoint}
    (opParent : (op.get! ctx.raw).parent = some opBlock)
    (blockParent : (opBlock.get! ctx.raw).parent = some currentRegion)
    (opInBounds : op.InBounds ctx.raw)
    (beforeLifting :
      (InsertPoint.before op).LiftToRegion region beforeLift ctx)
    (afterLifting :
      (InsertPoint.after op ctx.raw opBlock opParent opInBounds).LiftToRegion
        region afterLift ctx) :
    (region = currentRegion ∧
      beforeLift = InsertPoint.before op ∧
      afterLift = InsertPoint.after op ctx.raw opBlock opParent opInBounds) ∨
    (region ≠ currentRegion ∧ beforeLift = afterLift) := by
  cases beforeLifting with
  | @before _ projection _ _ projectionPath =>
      cases projectionPath with
      | @here _ _ projectionBlock _ projectionParent projectionBlockParent =>
          have regionEq : region = currentRegion := by grind
          subst currentRegion
          have pointBlock :
              (InsertPoint.after op ctx.raw opBlock opParent opInBounds).block!
                ctx.raw = some opBlock :=
            InsertPoint.block!_after_eq ctx.wellFormed opParent opInBounds
          have afterHere :
              (InsertPoint.after op ctx.raw opBlock opParent opInBounds).LiftToRegion
                region (InsertPoint.after op ctx.raw opBlock opParent opInBounds) ctx :=
            .here pointBlock blockParent
          have afterEq := afterLifting.unique afterHere
          exact Or.inl ⟨rfl, rfl, afterEq⟩
      | @step _ _ projectionBlock projectionRegion parent projection _
          projectionParent projectionBlockParent regionNe regionParent tail =>
          have blockEq : projectionBlock = opBlock := by grind
          subst projectionBlock
          have currentRegionEq : projectionRegion = currentRegion := by grind
          subst projectionRegion
          cases nextEq : (op.get! ctx.raw).next with
          | none =>
              rw [InsertPoint.after_eq_of_none_next nextEq] at afterLifting
              have sameLift :
                  (InsertPoint.atEnd opBlock).LiftToRegion region
                    (InsertPoint.before projection) ctx :=
                .atEndNested blockParent regionNe regionParent tail
              have afterEq := afterLifting.unique sameLift
              exact Or.inr ⟨Ne.symm regionNe, afterEq.symm⟩
          | some next =>
              have nextParent : (next.get! ctx.raw).parent = some opBlock := by
                obtain ⟨operations, chain⟩ :=
                  ctx.wellFormed.opChain opBlock (by grind)
                exact chain.parent!_nextOp_eq opInBounds opParent nextEq
              rw [InsertPoint.after_eq_of_some_next nextEq] at afterLifting
              have nextProjection :
                  next.FirstAncestorOpInRegion region projection ctx :=
                .step nextParent blockParent regionNe regionParent tail
              have sameLift :
                  (InsertPoint.before next).LiftToRegion region
                    (InsertPoint.before projection) ctx :=
                .before nextProjection
              have afterEq := afterLifting.unique sameLift
              exact Or.inr ⟨Ne.symm regionNe, afterEq.symm⟩

/-- Lifting a before point determines a lifted after point in the same region. -/
theorem exists_after_of_before
    {op : OperationPtr} {opBlock : BlockPtr} {region : RegionPtr}
    {beforeLift : InsertPoint}
    (opParent : (op.get! ctx.raw).parent = some opBlock)
    (opInBounds : op.InBounds ctx.raw)
    (beforeLifting :
      (InsertPoint.before op).LiftToRegion region beforeLift ctx) :
    ∃ afterLift,
      (InsertPoint.after op ctx.raw opBlock opParent opInBounds).LiftToRegion
        region afterLift ctx := by
  cases beforeLifting with
  | @before _ projection _ _ projectionPath =>
      cases projectionPath with
      | @here _ _ projectionBlock _ projectionParent projectionBlockParent =>
          have blockEq : projectionBlock = opBlock := by grind
          subst projectionBlock
          have pointBlock :
              (InsertPoint.after op ctx.raw opBlock opParent opInBounds).block!
                ctx.raw = some opBlock :=
            InsertPoint.block!_after_eq ctx.wellFormed opParent opInBounds
          exact ⟨_, .here pointBlock projectionBlockParent⟩
      | @step _ _ projectionBlock currentRegion parent projection _
          projectionParent projectionBlockParent regionNe regionParent tail =>
          have blockEq : projectionBlock = opBlock := by grind
          subst projectionBlock
          cases nextEq : (op.get! ctx.raw).next with
          | none =>
              rw [InsertPoint.after_eq_of_none_next nextEq]
              exact ⟨_, .atEndNested projectionBlockParent regionNe regionParent tail⟩
          | some next =>
              have nextParent : (next.get! ctx.raw).parent = some opBlock := by
                obtain ⟨operations, chain⟩ :=
                  ctx.wellFormed.opChain opBlock (by grind)
                exact chain.parent!_nextOp_eq opInBounds opParent nextEq
              rw [InsertPoint.after_eq_of_some_next nextEq]
              exact ⟨_, .before
                (.step nextParent projectionBlockParent regionNe regionParent tail)⟩

/-- Lifting an after point determines a lifted before point in the same region. -/
theorem exists_before_of_after
    {op : OperationPtr} {opBlock : BlockPtr} {region : RegionPtr}
    {afterLift : InsertPoint}
    (opParent : (op.get! ctx.raw).parent = some opBlock)
    (opInBounds : op.InBounds ctx.raw)
    (afterLifting :
      (InsertPoint.after op ctx.raw opBlock opParent opInBounds).LiftToRegion
        region afterLift ctx) :
    ∃ beforeLift,
      (InsertPoint.before op).LiftToRegion region beforeLift ctx := by
  cases nextEq : (op.get! ctx.raw).next with
  | none =>
      rw [InsertPoint.after_eq_of_none_next nextEq] at afterLifting
      cases afterLifting with
      | @atEndHere _ _ _ liftedBlockParent =>
          exact ⟨_, .before (.here opParent liftedBlockParent)⟩
      | @atEndNested _ currentRegion _ parent projection _
          liftedBlockParent regionNe regionParent projectionPath =>
          exact ⟨_, .before
            (.step opParent liftedBlockParent regionNe regionParent projectionPath)⟩
  | some next =>
      have nextParent : (next.get! ctx.raw).parent = some opBlock := by
        obtain ⟨operations, chain⟩ :=
          ctx.wellFormed.opChain opBlock (by grind)
        exact chain.parent!_nextOp_eq opInBounds opParent nextEq
      rw [InsertPoint.after_eq_of_some_next nextEq] at afterLifting
      cases afterLifting with
      | @before _ projection _ _ projectionPath =>
          cases projectionPath with
          | @here _ _ projectionBlock _ projectionParent projectionBlockParent =>
              have blockEq : projectionBlock = opBlock := by grind
              subst projectionBlock
              exact ⟨_, .before (.here opParent projectionBlockParent)⟩
          | @step _ _ projectionBlock currentRegion parent projection _
              projectionParent projectionBlockParent regionNe regionParent tail =>
              have blockEq : projectionBlock = opBlock := by grind
              subst projectionBlock
              exact ⟨_, .before
                (.step opParent projectionBlockParent regionNe regionParent tail)⟩

/--
A successor entry and its predecessor's end lift to their distinct local
points in the CFG region, and to the same point in every proper ancestor
region.
-/
theorem exists_predecessor_end_of_successor_entry
    {ctx : WfIRContext OpCode}
    {predecessor successor : BlockPtr} {cfgRegion region : RegionPtr}
    {successorLift : InsertPoint}
    (ctxVerified : ctx.Verified)
    (predecessorParent :
      (predecessor.get! ctx.raw).parent = some cfgRegion)
    (_predecessorInBounds : predecessor.InBounds ctx.raw)
    (successorEdge : successor ∈ predecessor.getSuccessors! ctx.raw)
    (successorLifting :
      (InsertPoint.atStart! successor ctx.raw).LiftToRegion
        region successorLift ctx) :
    ∃ predecessorLift,
      (InsertPoint.atEnd predecessor).LiftToRegion region predecessorLift ctx ∧
      ((region = cfgRegion ∧
        successorLift = InsertPoint.atStart! successor ctx.raw ∧
        predecessorLift = InsertPoint.atEnd predecessor) ∨
       (region ≠ cfgRegion ∧ successorLift = predecessorLift)) := by
  have successorParent :
      (successor.get! ctx.raw).parent = some cfgRegion :=
    ctxVerified.successor_parent _predecessorInBounds predecessorParent successorEdge
  have successorInBounds : successor.InBounds ctx.raw := by
    grind [Block.default_parent_eq, BlockPtr.get!_of_not_inBounds]
  by_cases regionEq : region = cfgRegion
  · subst region
    have successorBlock :
        (InsertPoint.atStart! successor ctx.raw).block! ctx.raw =
          some successor :=
      InsertPoint.block!_atStart!_eq ctx.wellFormed successorInBounds
    have successorHere :
        (InsertPoint.atStart! successor ctx.raw).LiftToRegion cfgRegion
          (InsertPoint.atStart! successor ctx.raw) ctx :=
      .here successorBlock successorParent
    have successorLiftEq := successorLifting.unique successorHere
    exact ⟨InsertPoint.atEnd predecessor, .atEndHere predecessorParent,
      Or.inl ⟨rfl, successorLiftEq, rfl⟩⟩
  · cases firstOpEq : (successor.get! ctx.raw).firstOp with
    | none =>
        rw [InsertPoint.atStart!_eq_atEnd_of_firstOp_eq_none firstOpEq]
          at successorLifting
        cases successorLifting with
        | atEndHere liftedParent =>
            have : region = cfgRegion := by grind
            exact False.elim (regionEq this)
        | @atEndNested _ currentRegion _ parent projection _
            liftedParent currentRegionNe currentRegionParent projectionPath =>
            have currentRegionEq : currentRegion = cfgRegion := by grind
            subst currentRegion
            exact ⟨InsertPoint.before projection,
              .atEndNested predecessorParent (Ne.symm regionEq)
                currentRegionParent projectionPath,
              Or.inr ⟨regionEq, rfl⟩⟩
    | some first =>
        rw [InsertPoint.atStart!_eq_before_of_firstOp_eq_some firstOpEq]
          at successorLifting
        cases successorLifting with
        | @before _ projection _ _ projectionPath =>
            cases projectionPath with
            | @here _ _ firstBlock _ firstParent firstBlockParent =>
                have firstBlockEq : firstBlock = successor := by
                  have firstFacts :=
                    (ctx.wellFormed.firstOp!_eq_some_iff
                      successorInBounds (by grind)).mp firstOpEq
                  grind
                subst firstBlock
                have : region = cfgRegion := by grind
                exact False.elim (regionEq this)
            | @step _ _ firstBlock currentRegion parent projection _
                firstParent firstBlockParent currentRegionNe
                currentRegionParent tail =>
                have firstBlockEq : firstBlock = successor := by
                  have firstFacts :=
                    (ctx.wellFormed.firstOp!_eq_some_iff
                      successorInBounds (by grind)).mp firstOpEq
                  grind
                subst firstBlock
                have currentRegionEq : currentRegion = cfgRegion := by grind
                subst currentRegion
                exact ⟨InsertPoint.before projection,
                  .atEndNested predecessorParent (Ne.symm regionEq)
                    currentRegionParent tail,
                  Or.inr ⟨regionEq, rfl⟩⟩

/-- Corresponding lifted before and after points lie in the same block. -/
theorem block_eq_before_after
    {op : OperationPtr} {opBlock : BlockPtr}
    {currentRegion region : RegionPtr}
    {beforeLift afterLift : InsertPoint}
    (opParent : (op.get! ctx.raw).parent = some opBlock)
    (blockParent : (opBlock.get! ctx.raw).parent = some currentRegion)
    (opInBounds : op.InBounds ctx.raw)
    (beforeLifting :
      (InsertPoint.before op).LiftToRegion region beforeLift ctx)
    (afterLifting :
      (InsertPoint.after op ctx.raw opBlock opParent opInBounds).LiftToRegion
        region afterLift ctx) :
    beforeLift.block! ctx.raw = afterLift.block! ctx.raw := by
  rcases before_after opParent blockParent opInBounds beforeLifting afterLifting with
    ⟨rfl, rfl, rfl⟩ | ⟨_, rfl⟩
  · rw [InsertPoint.block!_after_eq ctx.wellFormed opParent opInBounds]
    simpa using opParent
  · rfl

end InsertPoint.LiftToRegion

namespace OperationPtr

variable {source target : OperationPtr}
variable {block : BlockPtr}
variable {region : RegionPtr}

/-- Dominance at the point after an operation is dominance of that operation. -/
theorem dominatesIp_iff
    (targetParent : (target.get! ctx.raw).parent = some block)
    (targetInBounds : target.InBounds ctx.raw) :
    source.DominatesIp
        (InsertPoint.after target ctx.raw block targetParent targetInBounds) ctx ↔
      source.Dominates target ctx := by
  simp [OperationPtr.DominatesIp, InsertPoint.prev!_after_eq ctx.wellFormed]

/-- Dominating the point before an operation implies dominating the operation itself. -/
theorem dominates_of_dominatesIp_before
    (targetParent : (target.get! ctx.raw).parent = some block)
    (blockParent : (block.get! ctx.raw).parent = some region)
    (pointDominance : source.DominatesIp (.before target) ctx) :
    source.Dominates target ctx := by
  cases previousEq : (target.get! ctx.raw).prev with
  | none =>
      simp only [OperationPtr.DominatesIp, InsertPoint.prev!_before_eq,
        previousEq] at pointDominance
      rcases pointDominance with strictDominance | ⟨rfl, _, _, _, _, _⟩
      · exact strictDominance.1
      · exact OperationPtr.dominates_refl
  | some previous =>
      have targetInBounds : target.InBounds ctx.raw := by
        apply Classical.byContradiction
        intro targetOutOfBounds
        have targetDefault : target.get! ctx.raw = default :=
          get!_of_not_inBounds targetOutOfBounds
        rw [targetDefault] at previousEq
        contradiction
      have nextEq : (previous.get! ctx.raw).next = some target :=
        ctx.wellFormed.OperationPtr_next!_eq_some_of_prev!_eq_some
          targetInBounds previousEq
      have previousParent : (previous.get! ctx.raw).parent = some block := by
        obtain ⟨operations, chain⟩ := ctx.wellFormed.opChain block (by grind)
        exact chain.parent!_prevOp_eq targetInBounds targetParent previousEq
      have sourcePrevious : source.Dominates previous ctx := by
        simpa [OperationPtr.DominatesIp, previousEq] using pointDominance
      exact OperationPtr.dominates_next sourcePrevious previousParent
        blockParent nextEq

/-- A strict operation dominator dominates the point before its target. -/
@[grind →]
theorem dominatesIp_before
    (dominance : source.StrictlyDominates target ctx) :
    source.DominatesIp (.before target) ctx := by
  cases previousEq : (target.get! ctx.raw).prev with
  | none =>
      simp [OperationPtr.DominatesIp, previousEq, dominance]
  | some previous =>
      have targetInBounds : target.InBounds ctx.raw := by
        apply Classical.byContradiction
        intro targetOutOfBounds
        have targetDefault : target.get! ctx.raw = default :=
          get!_of_not_inBounds targetOutOfBounds
        rw [targetDefault] at previousEq
        contradiction
      have nextEq : (previous.get! ctx.raw).next = some target :=
        ctx.wellFormed.OperationPtr_next!_eq_some_of_prev!_eq_some
          targetInBounds previousEq
      simpa [OperationPtr.DominatesIp, previousEq] using
        OperationPtr.dominates_previous dominance nextEq

/-- With distinct endpoints, before-point dominance is strict dominance. -/
theorem dominatesIp_before_iff_of_ne
    (targetParent : (target.get! ctx.raw).parent = some block)
    (blockParent : (block.get! ctx.raw).parent = some region)
    (sourceNeTarget : source ≠ target) :
    source.DominatesIp (.before target) ctx ↔
      source.StrictlyDominates target ctx := by
  constructor
  · intro pointDominance
    cases previousEq : (target.get! ctx.raw).prev with
    | none =>
        simpa [OperationPtr.DominatesIp, previousEq, sourceNeTarget] using
          pointDominance
    | some previous =>
        have targetInBounds : target.InBounds ctx.raw := by
          apply Classical.byContradiction
          intro targetOutOfBounds
          have targetDefault : target.get! ctx.raw = default :=
            get!_of_not_inBounds targetOutOfBounds
          rw [targetDefault] at previousEq
          contradiction
        have nextEq : (previous.get! ctx.raw).next = some target :=
          ctx.wellFormed.OperationPtr_next!_eq_some_of_prev!_eq_some
            targetInBounds previousEq
        have previousParent : (previous.get! ctx.raw).parent = some block := by
          obtain ⟨operations, chain⟩ := ctx.wellFormed.opChain block (by grind)
          exact chain.parent!_prevOp_eq targetInBounds targetParent previousEq
        have sourcePrevious : source.Dominates previous ctx := by
          simpa [OperationPtr.DominatesIp, previousEq] using
            pointDominance
        exact ⟨OperationPtr.dominates_next sourcePrevious previousParent
          blockParent nextEq, sourceNeTarget⟩
  · intro dominance
    exact dominatesIp_before dominance

/-- Dominance after an operation is dominance before it, or equality with it. -/
theorem dominatesIp_after_iff_before_or_eq
    (targetParent : (target.get! ctx.raw).parent = some block)
    (blockParent : (block.get! ctx.raw).parent = some region)
    (targetInBounds : target.InBounds ctx.raw) :
    source.DominatesIp
        (InsertPoint.after target ctx.raw block targetParent targetInBounds) ctx ↔
      source.DominatesIp (InsertPoint.before target) ctx ∨ source = target := by
  rw [dominatesIp_iff targetParent targetInBounds]
  constructor
  · intro dominance
    by_cases sourceEq : source = target
    · exact Or.inr sourceEq
    · exact Or.inl (dominatesIp_before ⟨dominance, sourceEq⟩)
  · rintro (beforeDominance | rfl)
    · by_cases sourceEq : source = target
      · subst source
        exact OperationPtr.dominates_refl
      · exact (dominatesIp_before_iff_of_ne targetParent blockParent sourceEq).mp
          beforeDominance |>.1
    · exact OperationPtr.dominates_refl

/-- In an SSA region, distinct-endpoint before-point dominance is strict dominance. -/
theorem dominatesIp_before_iff_of_ssa_of_ne
    (targetParent : (target.get! ctx.raw).parent = some block)
    (blockParent : (block.get! ctx.raw).parent = some region)
    (_regionSSA : region.hasSSADominance ctx = true)
    (sourceNeTarget : source ≠ target) :
    source.DominatesIp (.before target) ctx ↔
      source.StrictlyDominates target ctx :=
  dominatesIp_before_iff_of_ne targetParent blockParent sourceNeTarget

/-- In a graph region, before-point dominance is ordinary operation dominance. -/
theorem dominatesIp_before_iff_of_graph
    (targetParent : (target.get! ctx.raw).parent = some block)
    (blockParent : (block.get! ctx.raw).parent = some region)
    (regionGraph : region.hasSSADominance ctx = false) :
    source.DominatesIp (.before target) ctx ↔
      source.Dominates target ctx := by
  cases previousEq : (target.get! ctx.raw).prev with
  | none =>
      simp [OperationPtr.DominatesIp, previousEq, targetParent, blockParent,
        regionGraph, OperationPtr.dominates_iff_strictlyDominates_or_eq]
  | some previous =>
      have targetInBounds : target.InBounds ctx.raw := by
        apply Classical.byContradiction
        intro targetOutOfBounds
        have targetDefault : target.get! ctx.raw = default :=
          get!_of_not_inBounds targetOutOfBounds
        rw [targetDefault] at previousEq
        contradiction
      have nextEq : (previous.get! ctx.raw).next = some target :=
        ctx.wellFormed.OperationPtr_next!_eq_some_of_prev!_eq_some
          targetInBounds previousEq
      have previousParent : (previous.get! ctx.raw).parent = some block := by
        obtain ⟨operations, chain⟩ := ctx.wellFormed.opChain block (by grind)
        exact chain.parent!_prevOp_eq targetInBounds targetParent previousEq
      simp only [OperationPtr.DominatesIp, InsertPoint.prev!_before_eq, previousEq]
      constructor
      · intro sourcePrevious
        exact OperationPtr.dominates_next sourcePrevious previousParent
          blockParent nextEq
      · intro sourceTarget
        by_cases sourceEq : source = target
        · subst source
          exact OperationPtr.dominates_of_graph targetParent previousParent
            blockParent blockParent regionGraph
        · exact OperationPtr.dominates_previous ⟨sourceTarget, sourceEq⟩ nextEq

/-- Dominance at a block's start has structural block-entry evidence. -/
theorem blockEntryDominance_of_dominatesIp_atStart
    (blockInBounds : block.InBounds ctx.raw)
    (pointDominance : source.DominatesIp (InsertPoint.atStart! block ctx.raw) ctx) :
    source.BlockEntryDominance block ctx := by
  cases firstOpEq : (block.get! ctx.raw).firstOp with
  | none =>
      obtain ⟨operations, chain⟩ := ctx.wellFormed.opChain block blockInBounds
      have lastOpEq : (block.get! ctx.raw).lastOp = none :=
        (chain.firstOp_eq_none_iff_lastOp_eq_none).mp firstOpEq
      rw [InsertPoint.atStart!_eq_atEnd_of_firstOp_eq_none firstOpEq] at pointDominance
      have blockEnd : source.BlockEndDominance block ctx := by
        simpa [OperationPtr.DominatesIp, lastOpEq] using pointDominance
      exact blockEnd.toEntry_of_first_eq_none firstOpEq
  | some first =>
      have firstInBounds : first.InBounds ctx.raw := by grind
      have firstFacts :=
        (ctx.wellFormed.firstOp!_eq_some_iff blockInBounds firstInBounds).mp
          firstOpEq
      rw [InsertPoint.atStart!_eq_before_of_firstOp_eq_some firstOpEq] at pointDominance
      simp only [OperationPtr.DominatesIp, InsertPoint.prev!_before_eq,
        firstFacts.2] at pointDominance
      rcases pointDominance with strictDominance |
          ⟨rfl, witnessBlock, witnessRegion, firstParent, blockParent,
            regionGraph⟩
      · exact .of_strictlyDominates_first strictDominance.1
          strictDominance.2 firstFacts.1 firstOpEq
      · have blockEq : witnessBlock = block := by grind
        subst witnessBlock
        exact .graph firstParent blockParent blockParent regionGraph

end OperationPtr

/--
An operation dominating a verified successor's entry also dominates the
predecessor's end. No predecessor-reachability premise is needed under
LLVM/MLIR unreachable-block semantics.
-/
theorem WfIRContext.Verified.op_dominatesIp_successor_entry
    {ctx : WfIRContext OpCode} {source : OperationPtr}
    {predecessor successor : BlockPtr} {region : RegionPtr}
    (ctxVerified : ctx.Verified)
    (predecessorParent : (predecessor.get! ctx.raw).parent = some region)
    (_predecessorInBounds : predecessor.InBounds ctx.raw)
    (successorEdge : successor ∈ predecessor.getSuccessors! ctx.raw)
    (successorDominance :
      source.DominatesIp (InsertPoint.atStart! successor ctx.raw) ctx) :
    source.DominatesIp (InsertPoint.atEnd predecessor) ctx := by
  have successorParent : (successor.get! ctx.raw).parent = some region :=
    ctxVerified.successor_parent _predecessorInBounds predecessorParent successorEdge
  have successorInBounds : successor.InBounds ctx.raw := by
    grind [Block.default_parent_eq, BlockPtr.get!_of_not_inBounds]
  have successorStart : source.BlockEntryDominance successor ctx :=
    OperationPtr.blockEntryDominance_of_dominatesIp_atStart
      successorInBounds successorDominance
  have predecessorEnd : source.BlockEndDominance predecessor ctx :=
    successorStart.atPredecessorEnd predecessorParent successorParent successorEdge
  cases lastOpEq : (predecessor.get! ctx.raw).lastOp with
  | none =>
      simpa [OperationPtr.DominatesIp, lastOpEq] using predecessorEnd
  | some last =>
      have lastDominance : source.Dominates last ctx :=
        predecessorEnd.dominates_last predecessorParent lastOpEq
      simpa [OperationPtr.DominatesIp, lastOpEq] using lastDominance

end Veir
